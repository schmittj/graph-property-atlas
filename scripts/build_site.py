#!/usr/bin/env python3
"""
Build data.json for the GitHub Pages site.

Reads all witnesses, contradictions, and property definitions, then outputs
a single JSON file containing everything the interactive site needs.

Usage:
  python3 scripts/build_site.py              # writes site/_data/data.json
  python3 scripts/build_site.py --out DIR    # writes DIR/data.json
"""

import argparse
import itertools
import json
import os
import sys
from datetime import datetime, timezone

import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WITNESSES_DIR = os.path.join(REPO_ROOT, "witnesses")
GALLERY_DIR = os.path.join(REPO_ROOT, "gallery")
CONTRADICTIONS_DIR = os.path.join(REPO_ROOT, "contradictions")
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")
CONFIG_PATH = os.path.join(REPO_ROOT, "config.yaml")


def load_config():
    with open(CONFIG_PATH) as f:
        return yaml.safe_load(f)


def load_property_registry():
    registry_path = os.path.join(PROPERTIES_DIR, "registry.yaml")
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return data["properties"]


def load_yaml_dir(dirpath):
    """Load all YAML files from a directory."""
    results = []
    if not os.path.isdir(dirpath):
        return results
    for filename in sorted(os.listdir(dirpath)):
        if not filename.endswith(".yaml") or filename == "registry.yaml":
            continue
        filepath = os.path.join(dirpath, filename)
        with open(filepath) as f:
            data = yaml.safe_load(f)
        data["_filename"] = filename
        results.append(data)
    return results


def load_contradictions():
    registry_path = os.path.join(CONTRADICTIONS_DIR, "registry.yaml")
    if not os.path.exists(registry_path):
        return []
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return data.get("contradictions", [])


def graph_order(graph_data):
    """Extract vertex count from graph data."""
    fmt = graph_data.get("format", "")
    if fmt == "edge_list":
        return graph_data.get("vertices", 0)
    elif fmt in ("graph6", "sparse6"):
        raw = graph_data.get("data", "")
        if fmt == "sparse6" and raw.startswith(":"):
            raw = raw[1:]
        if raw.startswith(">>graph6<<"):
            raw = raw[len(">>graph6<<"):]
        if not raw:
            return 0
        b0 = ord(raw[0]) - 63
        if b0 <= 62:
            return b0
        if len(raw) >= 4:
            n = 0
            for i in range(1, 4):
                n = n * 64 + (ord(raw[i]) - 63)
            return n
    return 0


def cell_key(props_dict):
    return json.dumps(props_dict, sort_keys=True)


def cell_extends(cell, assignment):
    for prop, val in assignment.items():
        if cell.get(prop) != val:
            return False
    return True


def cell_label(cell):
    """Short human-readable label for a cell."""
    parts = []
    for k in sorted(cell.keys()):
        parts.append(f"{k}={'T' if cell[k] else 'F'}")
    return ", ".join(parts)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", default=os.path.join(REPO_ROOT, "site", "_data"))
    args = parser.parse_args()

    os.makedirs(args.out, exist_ok=True)

    config = load_config()
    properties = load_property_registry()
    property_ids = [p["id"] for p in properties]
    n_props = len(property_ids)

    # Load witnesses
    witnesses = load_yaml_dir(WITNESSES_DIR)
    gallery = load_yaml_dir(GALLERY_DIR)
    contradictions = load_contradictions()

    # Build witness index keyed by cell
    witness_by_cell = {}
    for w in witnesses:
        props = w.get("properties", {})
        key = cell_key(props)
        order = graph_order(w.get("graph", {}))
        entry = {
            "file": w["_filename"],
            "description": w.get("description", ""),
            "order": order,
        }
        if key not in witness_by_cell or order < witness_by_cell[key]["order"]:
            witness_by_cell[key] = entry

    # Enumerate all cells
    cells = []
    realized_count = 0
    impossible_count = 0
    open_count = 0

    for bits in itertools.product([True, False], repeat=n_props):
        cell = dict(zip(property_ids, bits))
        key = cell_key(cell)

        status = "open"
        witness = None
        killing_contradiction = None

        if key in witness_by_cell:
            status = "realized"
            witness = witness_by_cell[key]
            realized_count += 1

        for c in contradictions:
            if cell_extends(cell, c["assignments"]):
                if status == "open":
                    status = "impossible"
                    impossible_count += 1
                killing_contradiction = c["id"]
                break

        if status == "open":
            open_count += 1

        cells.append({
            "properties": cell,
            "label": cell_label(cell),
            "status": status,
            "witness": witness,
            "contradiction": killing_contradiction,
        })

    # Build implication edges from size-2 contradictions
    implications = []
    for c in contradictions:
        assignments = c["assignments"]
        if len(assignments) == 2:
            items = list(assignments.items())
            # An implication P=>Q is encoded as {P=T, Q=F} being impossible
            true_props = [k for k, v in items if v is True]
            false_props = [k for k, v in items if v is False]
            if len(true_props) == 1 and len(false_props) == 1:
                implications.append({
                    "from": true_props[0],
                    "to": false_props[0],
                    "contradiction_id": c["id"],
                })

    # Assemble output
    data = {
        "generated_at": datetime.now(timezone.utc).isoformat(),
        "min_vert": config.get("min_vert", 3),
        "properties": properties,
        "property_ids": property_ids,
        "summary": {
            "total_cells": 2 ** n_props,
            "realized": realized_count,
            "impossible": impossible_count,
            "open": open_count,
        },
        "cells": cells,
        "contradictions": [
            {
                "id": c["id"],
                "assignments": c["assignments"],
                "minimal": c.get("minimal", "unknown"),
                "notes": c.get("notes", ""),
            }
            for c in contradictions
        ],
        "implications": implications,
        "witnesses": [
            {
                "file": w["_filename"],
                "description": w.get("description", ""),
                "order": graph_order(w.get("graph", {})),
                "properties": w.get("properties", {}),
            }
            for w in witnesses
        ],
    }

    out_path = os.path.join(args.out, "data.json")
    with open(out_path, "w") as f:
        json.dump(data, f, indent=2)
    print(f"Wrote {out_path}")
    print(f"  {n_props} properties, {2**n_props} cells")
    print(f"  {realized_count} realized, {impossible_count} impossible, {open_count} open")
    return 0


if __name__ == "__main__":
    sys.exit(main())
