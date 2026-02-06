#!/usr/bin/env python3
"""
Verify the critical invariant: no cell is both realized and impossible.

If a cell has a witness AND extends a known contradiction, this indicates
a bug in either the Sage checkers, the Lean proofs, or the data files.
"""

import itertools
import json
import os
import sys

import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WITNESSES_DIR = os.path.join(REPO_ROOT, "witnesses")
CONTRADICTIONS_DIR = os.path.join(REPO_ROOT, "contradictions")
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")


def load_property_ids():
    registry_path = os.path.join(PROPERTIES_DIR, "registry.yaml")
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return [p["id"] for p in data["properties"]]


def cell_key(props_dict):
    return json.dumps(props_dict, sort_keys=True)


def cell_extends(cell, assignments):
    for prop_id, value in assignments.items():
        if cell.get(prop_id) != value:
            return False
    return True


def main():
    property_ids = load_property_ids()

    # Load realized cells from witnesses
    realized_cells = {}
    if os.path.isdir(WITNESSES_DIR):
        for filename in sorted(os.listdir(WITNESSES_DIR)):
            if not filename.endswith(".yaml"):
                continue
            filepath = os.path.join(WITNESSES_DIR, filename)
            with open(filepath) as f:
                data = yaml.safe_load(f)
            props = data.get("properties", {})
            key = cell_key(props)
            if key not in realized_cells:
                realized_cells[key] = []
            realized_cells[key].append(filename)

    # Load contradictions
    contradictions = []
    registry_path = os.path.join(CONTRADICTIONS_DIR, "registry.yaml")
    if os.path.exists(registry_path):
        with open(registry_path) as f:
            data = yaml.safe_load(f)
        contradictions = data.get("contradictions", [])

    # Check each realized cell against all contradictions
    violations = []
    for key, witness_files in realized_cells.items():
        cell = json.loads(key)
        for c in contradictions:
            if cell_extends(cell, c["assignments"]):
                violations.append(
                    {
                        "cell": cell,
                        "witnesses": witness_files,
                        "contradiction": c["id"],
                        "contradiction_assignments": c["assignments"],
                    }
                )

    if violations:
        print("CONSISTENCY CHECK FAILED")
        print(f"Found {len(violations)} violation(s):\n")
        for v in violations:
            print(f"  Cell: {v['cell']}")
            print(f"  Witnesses: {v['witnesses']}")
            print(f"  Contradiction: {v['contradiction']}")
            print(f"  Assignments: {v['contradiction_assignments']}")
            print()
        return 1
    else:
        print(
            f"CONSISTENCY CHECK PASSED: {len(realized_cells)} realized cell(s), "
            f"{len(contradictions)} contradiction(s), no conflicts."
        )
        return 0


if __name__ == "__main__":
    sys.exit(main())
