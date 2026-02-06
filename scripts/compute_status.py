#!/usr/bin/env python3
"""
Compute the status of every cell in the property cube.

For each of the 2^|P| cells, determines whether it is:
  - realized: has a witness graph
  - impossible: extends a known contradiction
  - open: neither

Detects conflicts (realized + impossible) and fails if found.
Outputs status.json as a CI artifact.
"""

import itertools
import json
import os
import sys
from datetime import datetime, timezone

import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WITNESSES_DIR = os.path.join(REPO_ROOT, "witnesses")
CONTRADICTIONS_DIR = os.path.join(REPO_ROOT, "contradictions")
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")
CONFIG_PATH = os.path.join(REPO_ROOT, "config.yaml")


def load_config():
    with open(CONFIG_PATH) as f:
        return yaml.safe_load(f)


def load_property_ids():
    registry_path = os.path.join(PROPERTIES_DIR, "registry.yaml")
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return [p["id"] for p in data["properties"]]


def cell_key(props_dict):
    """Canonical string key for a cell (sorted by property ID)."""
    return json.dumps(props_dict, sort_keys=True)


def decode_graph6_order(data):
    """Decode vertex count from a graph6 string (pure Python, no Sage needed)."""
    # graph6 format: first byte(s) encode N
    # If first byte b satisfies 63 <= b-63 <= 62, then N = b - 63
    # If first byte is 126 (~), next 3 bytes encode N in big-endian base-63
    # (There's also a 6-byte encoding for very large N, but unlikely here)
    if data.startswith(">>graph6<<"):
        data = data[len(">>graph6<<"):]
    if not data:
        return 0
    b0 = ord(data[0]) - 63
    if b0 <= 62:
        return b0
    # 3-byte encoding
    if len(data) >= 4:
        n = 0
        for i in range(1, 4):
            n = n * 64 + (ord(data[i]) - 63)
        return n
    return 0


def graph_order_size(graph_data):
    """Extract (order, size) from graph data without Sage.

    Returns (order, size). When size cannot be determined (graph6/sparse6),
    returns sys.maxsize so unknown-size graphs lose tie-breaking against
    graphs with known edge counts at the same order.
    """
    fmt = graph_data.get("format", "")
    if fmt == "edge_list":
        order = graph_data.get("vertices", 0)
        size = len(graph_data.get("data", []))
        return order, size
    elif fmt == "graph6":
        order = decode_graph6_order(graph_data.get("data", ""))
        return order, sys.maxsize
    elif fmt == "sparse6":
        # sparse6 starts with ':', then graph6-style N encoding
        raw = graph_data.get("data", "")
        if raw.startswith(":"):
            raw = raw[1:]
        order = decode_graph6_order(raw)
        return order, sys.maxsize
    return 0, 0


def load_witnesses(property_ids):
    """Load all witness files and return their cells."""
    witnesses = {}
    if not os.path.isdir(WITNESSES_DIR):
        return witnesses
    for filename in sorted(os.listdir(WITNESSES_DIR)):
        if not filename.endswith(".yaml"):
            continue
        filepath = os.path.join(WITNESSES_DIR, filename)
        with open(filepath) as f:
            data = yaml.safe_load(f)
        props = data.get("properties", {})
        key = cell_key(props)
        graph_data = data.get("graph", {})
        order, size = graph_order_size(graph_data)
        if key not in witnesses or (order, size) < (
            witnesses[key]["order"],
            witnesses[key]["size"],
        ):
            witnesses[key] = {
                "file": filename,
                "order": order,
                "size": size,
            }
    return witnesses


def load_contradictions():
    """Load all contradictions from the registry."""
    registry_path = os.path.join(CONTRADICTIONS_DIR, "registry.yaml")
    if not os.path.exists(registry_path):
        return []
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return data.get("contradictions", [])


def cell_extends_contradiction(cell, contradiction_assignments):
    """Check if a cell is consistent with (extends) a contradiction's assignments."""
    for prop_id, value in contradiction_assignments.items():
        if cell.get(prop_id) != value:
            return False
    return True


def main():
    config = load_config()
    property_ids = load_property_ids()
    n_props = len(property_ids)
    total_cells = 2**n_props

    print(f"Properties ({n_props}): {property_ids}")
    print(f"Total cells: {total_cells}")

    # Load data
    witnesses = load_witnesses(property_ids)
    contradictions = load_contradictions()

    print(f"Witnesses: {len(witnesses)} distinct cells")
    print(f"Contradictions: {len(contradictions)}")

    # Enumerate all cells and classify
    realized_count = 0
    impossible_count = 0
    open_count = 0
    conflicts = []
    canonical_witnesses = {}
    impossible_by_contradiction = {}

    for bits in itertools.product([True, False], repeat=n_props):
        cell = dict(zip(property_ids, bits))
        key = cell_key(cell)

        is_realized = key in witnesses
        killing_contradiction = None
        for c in contradictions:
            if cell_extends_contradiction(cell, c["assignments"]):
                killing_contradiction = c["id"]
                break

        # Detect conflicts
        if is_realized and killing_contradiction:
            conflicts.append(
                {
                    "cell": cell,
                    "witness": witnesses[key]["file"],
                    "contradiction": killing_contradiction,
                }
            )

        if is_realized:
            realized_count += 1
            canonical_witnesses[key] = witnesses[key]
        if killing_contradiction:
            impossible_count += 1
            if killing_contradiction not in impossible_by_contradiction:
                impossible_by_contradiction[killing_contradiction] = 0
            impossible_by_contradiction[killing_contradiction] += 1
        if not is_realized and not killing_contradiction:
            open_count += 1

    # Report conflicts
    if conflicts:
        print()
        print(f"CONFLICT: {len(conflicts)} cell(s) are both realized and impossible!")
        for c in conflicts:
            print(f"  Cell: {c['cell']}")
            print(f"  Witness: {c['witness']}")
            print(f"  Contradiction: {c['contradiction']}")
            print()
        print("This indicates a bug in checkers, proofs, or data files.")
        return 1

    # Build output
    status = {
        "sage_version": config.get("sage_version", "unknown"),
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "property_set": property_ids,
        "total_cells": total_cells,
        "realized": realized_count,
        "impossible": impossible_count,
        "open": open_count,
        "canonical_witnesses": canonical_witnesses,
        "impossible_cells_by_contradiction": impossible_by_contradiction,
    }

    # Print summary
    print()
    print(f"Realized:   {realized_count:>5} ({100*realized_count/total_cells:.1f}%)")
    print(
        f"Impossible: {impossible_count:>5} ({100*impossible_count/total_cells:.1f}%)"
    )
    print(f"Open:       {open_count:>5} ({100*open_count/total_cells:.1f}%)")

    # Write output
    output_path = os.path.join(REPO_ROOT, "status.json")
    with open(output_path, "w") as f:
        json.dump(status, f, indent=2)
    print(f"\nWrote {output_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
