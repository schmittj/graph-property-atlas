// Graph Property Atlas — interactive explorer
"use strict";

let DATA = null;
let filters = {};  // property_id -> null | true | false

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

// ---- Filters ----

function initFilters() {
  const bar = document.getElementById("filter-bar");
  DATA.property_ids.forEach(pid => {
    filters[pid] = null;
    const btn = document.createElement("button");
    btn.className = "filter-btn";
    btn.dataset.prop = pid;
    btn.textContent = pid + ": any";
    btn.addEventListener("click", () => cycleFilter(btn, pid));
    bar.appendChild(btn);
  });
}

function cycleFilter(btn, pid) {
  const current = filters[pid];
  if (current === null) {
    filters[pid] = true;
    btn.dataset.value = "true";
    btn.textContent = pid + ": T";
  } else if (current === true) {
    filters[pid] = false;
    btn.dataset.value = "false";
    btn.textContent = pid + ": F";
  } else {
    filters[pid] = null;
    btn.dataset.value = "";
    btn.textContent = pid + ": any";
  }
  renderCells();
}

// ---- Cell table ----

function renderCells() {
  const pids = DATA.property_ids;

  // Header
  const header = document.getElementById("cell-header");
  header.innerHTML = "";
  pids.forEach(pid => {
    const th = document.createElement("th");
    th.textContent = pid;
    th.className = "sortable";
    th.addEventListener("click", () => {
      const btn = document.querySelector(`.filter-btn[data-prop="${pid}"]`);
      if (btn) cycleFilter(btn, pid);
    });
    header.appendChild(th);
  });
  ["status", "witness / contradiction"].forEach(label => {
    const th = document.createElement("th");
    th.textContent = label;
    header.appendChild(th);
  });

  // Filter cells
  const filtered = DATA.cells.filter(cell => {
    for (const pid of pids) {
      if (filters[pid] !== null && cell.properties[pid] !== filters[pid]) return false;
    }
    return true;
  });

  document.getElementById("cell-count").textContent =
    `Showing ${filtered.length} of ${DATA.cells.length} cells`;

  // Body
  const body = document.getElementById("cell-body");
  body.innerHTML = "";

  // Cap at 256 rows for performance
  const display = filtered.slice(0, 256);

  display.forEach(cell => {
    const tr = document.createElement("tr");

    pids.forEach(pid => {
      const td = document.createElement("td");
      td.textContent = cell.properties[pid] ? "T" : "F";
      td.className = cell.properties[pid] ? "val-true" : "val-false";
      tr.appendChild(td);
    });

    const statusTd = document.createElement("td");
    statusTd.textContent = cell.status;
    statusTd.className = "status-" + cell.status;
    tr.appendChild(statusTd);

    const infoTd = document.createElement("td");
    if (cell.status === "realized" && cell.witness) {
      infoTd.textContent = cell.witness.description + " (" + cell.witness.order + "v)";
    } else if (cell.status === "impossible" && cell.contradiction) {
      infoTd.textContent = cell.contradiction;
    }
    tr.appendChild(infoTd);

    body.appendChild(tr);
  });

  if (filtered.length > 256) {
    const tr = document.createElement("tr");
    const td = document.createElement("td");
    td.colSpan = pids.length + 2;
    td.style.textAlign = "center";
    td.style.color = "var(--muted)";
    td.textContent = `... and ${filtered.length - 256} more cells (use filters to narrow)`;
    tr.appendChild(td);
    body.appendChild(tr);
  }
}

// ---- Witnesses ----

function renderWitnesses() {
  const body = document.getElementById("witness-body");
  DATA.witnesses.forEach(w => {
    const tr = document.createElement("tr");

    const fileTd = document.createElement("td");
    fileTd.style.fontFamily = "var(--mono)";
    fileTd.style.fontSize = "0.82rem";
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
    propsTd.style.fontSize = "0.8rem";
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
    idTd.style.fontSize = "0.82rem";
    idTd.textContent = c.id;
    tr.appendChild(idTd);

    const assTd = document.createElement("td");
    assTd.style.fontFamily = "var(--mono)";
    assTd.style.fontSize = "0.82rem";
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
