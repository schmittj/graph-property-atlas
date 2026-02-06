// Graph Property Atlas — interactive explorer
"use strict";

let DATA = null;

// Per-property filter state: { pid: { enabled: bool, value: "T"|"F"|"A" } }
let propFilters = {};
let statusFilter = "all";   // "all" | "realized" | "impossible" | "open"
let currentPage = 1;
const PAGE_SIZE = 20;

async function init() {
  try {
    const resp = await fetch("_data/data.json");
    DATA = await resp.json();
  } catch (e) {
    document.querySelector("main").innerHTML =
      '<p style="text-align:center;color:#dc2626;margin:3rem">Failed to load data.json. Run <code>python scripts/build_site.py</code> first.</p>';
    return;
  }

  renderSummary();
  renderImplications();
  initFilters();
  initStatusBar();
  renderCells();
  renderWitnesses();
  renderContradictions();

  if (DATA.generated_at) {
    const d = new Date(DATA.generated_at);
    document.getElementById("generated-at").textContent =
      "Updated " + d.toLocaleDateString("en-US", { year: "numeric", month: "short", day: "numeric" });
  }
}

// ---- Summary ----

function renderSummary() {
  const s = DATA.summary;
  document.getElementById("stat-properties").textContent = DATA.property_ids.length;
  document.getElementById("stat-cells").textContent = s.total_cells.toLocaleString();
  document.getElementById("stat-realized").textContent = s.realized.toLocaleString();
  document.getElementById("stat-impossible").textContent = s.impossible.toLocaleString();
  document.getElementById("stat-open").textContent = s.open.toLocaleString();
  const fill = ((s.realized + s.impossible) / s.total_cells * 100).toFixed(1);
  document.getElementById("stat-fill").textContent = fill + "%";
}

// ---- Implications ----

function renderImplications() {
  const container = document.getElementById("implications-graph");
  if (!DATA.implications.length) {
    container.innerHTML = '<span style="color:var(--muted)">No implications yet (need size-2 contradictions).</span>';
    return;
  }
  container.innerHTML = DATA.implications.map(imp =>
    `<span class="implication">${imp.from} \u21D2 ${imp.to}</span>`
  ).join("");
}

// ---- Property Filters ----

function initFilters() {
  const bar = document.getElementById("filter-bar");

  DATA.property_ids.forEach(pid => {
    propFilters[pid] = { enabled: true, value: "A" };

    const wrapper = document.createElement("div");
    wrapper.className = "prop-filter";
    wrapper.dataset.prop = pid;

    // Checkbox
    const cb = document.createElement("input");
    cb.type = "checkbox";
    cb.checked = true;
    cb.addEventListener("change", () => {
      propFilters[pid].enabled = cb.checked;
      wrapper.classList.toggle("disabled", !cb.checked);
      currentPage = 1;
      renderCells();
    });

    // Property name
    const nameSpan = document.createElement("span");
    nameSpan.className = "prop-name";
    nameSpan.textContent = pid;

    // T / F / A button group
    const tfaGroup = document.createElement("span");
    tfaGroup.className = "tfa-group";

    ["T", "F", "A"].forEach(val => {
      const btn = document.createElement("button");
      btn.className = "tfa-btn" + (val === "A" ? " active-a" : "");
      btn.textContent = val;
      btn.addEventListener("click", () => {
        propFilters[pid].value = val;
        // Update button classes
        tfaGroup.querySelectorAll(".tfa-btn").forEach(b => {
          b.className = "tfa-btn";
        });
        btn.classList.add(val === "T" ? "active-t" : val === "F" ? "active-f" : "active-a");
        currentPage = 1;
        renderCells();
      });
      tfaGroup.appendChild(btn);
    });

    wrapper.appendChild(cb);
    wrapper.appendChild(nameSpan);
    wrapper.appendChild(tfaGroup);
    bar.appendChild(wrapper);
  });
}

// ---- Status filter bar ----

function initStatusBar() {
  document.querySelectorAll(".status-btn").forEach(btn => {
    btn.addEventListener("click", () => {
      document.querySelectorAll(".status-btn").forEach(b => b.classList.remove("active"));
      btn.classList.add("active");
      statusFilter = btn.dataset.status;
      currentPage = 1;
      renderCells();
    });
  });
}

// ---- Cell table ----

function getFilteredCells() {
  return DATA.cells.filter(cell => {
    // Property filters
    for (const pid of DATA.property_ids) {
      const f = propFilters[pid];
      if (!f.enabled) continue;  // disabled = don't filter on this property
      if (f.value === "T" && cell.properties[pid] !== true) return false;
      if (f.value === "F" && cell.properties[pid] !== false) return false;
      // "A" = any, no filter
    }
    // Status filter
    if (statusFilter !== "all" && cell.status !== statusFilter) return false;
    return true;
  });
}

function getEnabledPids() {
  return DATA.property_ids.filter(pid => propFilters[pid].enabled);
}

// Deduplicate rows: when some properties are disabled, multiple cells may
// project to the same visible row. Group them and merge status.
function projectRows(filtered, enabledPids) {
  const map = new Map();
  filtered.forEach(cell => {
    const key = enabledPids.map(pid => cell.properties[pid] ? "T" : "F").join(",");
    if (!map.has(key)) {
      map.set(key, {
        key,
        properties: {},
        cells: [],
      });
      enabledPids.forEach(pid => {
        map.get(key).properties[pid] = cell.properties[pid];
      });
    }
    map.get(key).cells.push(cell);
  });

  // Convert to array and compute aggregate status
  return Array.from(map.values()).map(row => {
    const statuses = new Set(row.cells.map(c => c.status));
    let status;
    if (statuses.size === 1) {
      status = row.cells[0].status;
    } else {
      // Mixed — show most interesting: open > impossible > realized
      if (statuses.has("open")) status = "open";
      else if (statuses.has("impossible")) status = "impossible";
      else status = "realized";
    }

    // Collect info text
    let info = "";
    const witnesses = row.cells.filter(c => c.status === "realized" && c.witness);
    const contradictions = row.cells.filter(c => c.status === "impossible" && c.contradiction);
    const opens = row.cells.filter(c => c.status === "open");
    const parts = [];
    if (witnesses.length) {
      parts.push(witnesses.length === 1
        ? witnesses[0].witness.description + " (" + witnesses[0].witness.order + "v)"
        : witnesses.length + " witnesses");
    }
    if (contradictions.length) {
      parts.push(contradictions.length === 1
        ? contradictions[0].contradiction
        : contradictions.length + " contradictions");
    }
    if (opens.length) {
      parts.push(opens.length + " open");
    }
    info = parts.join("; ");

    return {
      properties: row.properties,
      status,
      info,
      cellCount: row.cells.length,
    };
  });
}

function renderCells() {
  const enabledPids = getEnabledPids();
  const filtered = getFilteredCells();
  const rows = projectRows(filtered, enabledPids);
  const totalPages = Math.max(1, Math.ceil(rows.length / PAGE_SIZE));
  if (currentPage > totalPages) currentPage = totalPages;
  const startIdx = (currentPage - 1) * PAGE_SIZE;
  const pageRows = rows.slice(startIdx, startIdx + PAGE_SIZE);

  // Header
  const header = document.getElementById("cell-header");
  header.innerHTML = "";
  enabledPids.forEach(pid => {
    const th = document.createElement("th");
    th.textContent = pid;
    header.appendChild(th);
  });
  ["status", "info"].forEach(label => {
    const th = document.createElement("th");
    th.textContent = label;
    header.appendChild(th);
  });

  // Count text
  document.getElementById("cell-count").textContent =
    `Showing ${rows.length} row${rows.length !== 1 ? "s" : ""} (${filtered.length} cell${filtered.length !== 1 ? "s" : ""})`;

  // Body
  const body = document.getElementById("cell-body");
  body.innerHTML = "";

  pageRows.forEach(row => {
    const tr = document.createElement("tr");

    enabledPids.forEach(pid => {
      const td = document.createElement("td");
      td.textContent = row.properties[pid] ? "T" : "F";
      td.className = row.properties[pid] ? "val-true" : "val-false";
      tr.appendChild(td);
    });

    const statusTd = document.createElement("td");
    statusTd.textContent = row.status;
    statusTd.className = "status-" + row.status;
    tr.appendChild(statusTd);

    const infoTd = document.createElement("td");
    infoTd.textContent = row.info;
    tr.appendChild(infoTd);

    body.appendChild(tr);
  });

  renderPagination(totalPages);
}

// ---- Pagination ----

function renderPagination(totalPages) {
  const container = document.getElementById("pagination");
  container.innerHTML = "";
  if (totalPages <= 1) return;

  // Prev button
  const prev = document.createElement("button");
  prev.className = "page-btn";
  prev.textContent = "\u2039";
  prev.disabled = currentPage <= 1;
  prev.addEventListener("click", () => { currentPage--; renderCells(); });
  container.appendChild(prev);

  // Page numbers (show at most 7 pages with ellipsis)
  const pages = computePageRange(currentPage, totalPages, 7);
  pages.forEach(p => {
    if (p === "...") {
      const span = document.createElement("span");
      span.textContent = "...";
      span.style.padding = "0 0.2em";
      span.style.color = "var(--muted)";
      container.appendChild(span);
    } else {
      const btn = document.createElement("button");
      btn.className = "page-btn" + (p === currentPage ? " active" : "");
      btn.textContent = p;
      btn.addEventListener("click", () => { currentPage = p; renderCells(); });
      container.appendChild(btn);
    }
  });

  // Next button
  const next = document.createElement("button");
  next.className = "page-btn";
  next.textContent = "\u203A";
  next.disabled = currentPage >= totalPages;
  next.addEventListener("click", () => { currentPage++; renderCells(); });
  container.appendChild(next);
}

function computePageRange(current, total, maxVisible) {
  if (total <= maxVisible) {
    return Array.from({ length: total }, (_, i) => i + 1);
  }
  const pages = [];
  pages.push(1);
  let start = Math.max(2, current - 1);
  let end = Math.min(total - 1, current + 1);
  if (start > 2) pages.push("...");
  for (let i = start; i <= end; i++) pages.push(i);
  if (end < total - 1) pages.push("...");
  pages.push(total);
  return pages;
}

// ---- Witnesses ----

function renderWitnesses() {
  const body = document.getElementById("witness-body");
  DATA.witnesses.forEach(w => {
    const tr = document.createElement("tr");

    const fileTd = document.createElement("td");
    fileTd.style.fontFamily = "var(--mono)";
    fileTd.style.fontSize = "0.85rem";
    fileTd.textContent = w.file;
    tr.appendChild(fileTd);

    const descTd = document.createElement("td");
    descTd.textContent = w.description;
    tr.appendChild(descTd);

    const orderTd = document.createElement("td");
    orderTd.textContent = w.order;
    tr.appendChild(orderTd);

    const propsTd = document.createElement("td");
    propsTd.style.fontFamily = "var(--mono)";
    propsTd.style.fontSize = "0.82rem";
    const parts = DATA.property_ids.map(pid => {
      const val = w.properties[pid];
      return `<span class="${val ? 'val-true' : 'val-false'}">${pid[0].toUpperCase()}=${val ? 'T' : 'F'}</span>`;
    });
    propsTd.innerHTML = parts.join(" ");
    tr.appendChild(propsTd);

    body.appendChild(tr);
  });
}

// ---- Contradictions ----

function renderContradictions() {
  const body = document.getElementById("contradiction-body");
  DATA.contradictions.forEach(c => {
    const tr = document.createElement("tr");

    const idTd = document.createElement("td");
    idTd.style.fontFamily = "var(--mono)";
    idTd.style.fontSize = "0.85rem";
    idTd.textContent = c.id;
    tr.appendChild(idTd);

    const assTd = document.createElement("td");
    assTd.style.fontFamily = "var(--mono)";
    assTd.style.fontSize = "0.85rem";
    assTd.textContent = Object.entries(c.assignments)
      .map(([k, v]) => `${k}=${v ? 'T' : 'F'}`)
      .join(", ");
    tr.appendChild(assTd);

    const minTd = document.createElement("td");
    minTd.textContent = c.minimal;
    tr.appendChild(minTd);

    const notesTd = document.createElement("td");
    notesTd.textContent = c.notes;
    tr.appendChild(notesTd);

    body.appendChild(tr);
  });
}

// ---- Boot ----

document.addEventListener("DOMContentLoaded", init);
