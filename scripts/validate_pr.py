#!/usr/bin/env python3
"""
Validate that a PR adds new information to the atlas.

Checks:
- New witnesses must cover an open cell or improve (smaller) an existing one.
- New contradictions must kill at least one currently-open cell.

Usage:
  python3 scripts/validate_pr.py --added-files file1.yaml file2.yaml ...
"""

import argparse
import json
import os
import sys

import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATUS_PATH = os.path.join(REPO_ROOT, "status.json")
WITNESSES_DIR = os.path.join(REPO_ROOT, "witnesses")
CONTRADICTIONS_DIR = os.path.join(REPO_ROOT, "contradictions")
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")


def load_status():
    if not os.path.exists(STATUS_PATH):
        print("status.json not found. Run scripts/compute_status.py first.")
        sys.exit(1)
    with open(STATUS_PATH) as f:
        return json.load(f)


def cell_key(props_dict):
    return json.dumps(props_dict, sort_keys=True)


def cell_extends(cell, assignment):
    for prop, val in assignment.items():
        if cell.get(prop) != val:
            return False
    return True


def validate_witness(filepath, status):
    """Check that a new witness adds value."""
    with open(filepath) as f:
        data = yaml.safe_load(f)
    props = data.get("properties", {})
    key = cell_key(props)
    canonical = status.get("canonical_witnesses", {})

    # Check if this cell was already realized
    if key in canonical:
        # Check if it's a smaller graph
        graph_data = data.get("graph", {})
        if graph_data.get("format") == "edge_list":
            new_order = graph_data.get("vertices", 0)
            new_size = len(graph_data.get("data", []))
        else:
            return True  # can't easily compare, accept provisionally

        existing = canonical[key]
        old_order = existing.get("order", 0)
        old_size = existing.get("size", 0)

        if (new_order, new_size) < (old_order, old_size):
            print(f"  {os.path.basename(filepath)}: "
                  f"IMPROVES existing ({new_order} < {old_order} vertices)")
            return True
        else:
            print(f"  {os.path.basename(filepath)}: "
                  f"REJECTED — cell already realized by {existing['file']} "
                  f"with equal or smaller graph")
            return False

    print(f"  {os.path.basename(filepath)}: NEW cell realized")
    return True


def validate_contradiction(dirpath, status):
    """Check that a new contradiction kills at least one open cell."""
    registry_path = os.path.join(dirpath, "..", "registry.yaml")
    dirname = os.path.basename(dirpath)

    # Read the contradiction's assignments from registry or infer from dirname
    assignments = {}
    if os.path.exists(registry_path):
        with open(registry_path) as f:
            reg = yaml.safe_load(f)
        for c in reg.get("contradictions", []):
            if c["id"] == dirname:
                assignments = c["assignments"]
                break

    if not assignments:
        print(f"  {dirname}: WARNING — cannot determine assignments")
        return True  # accept provisionally

    # Check how many currently-open cells this kills
    import itertools
    property_ids = status["property_set"]
    canonical = status.get("canonical_witnesses", {})

    killed_open = 0
    for bits in itertools.product([True, False], repeat=len(property_ids)):
        cell = dict(zip(property_ids, bits))
        key = cell_key(cell)

        if key in canonical:
            continue
        # Check if already killed by existing contradictions
        # (simplified: just check this new one)
        if cell_extends(cell, assignments):
            killed_open += 1

    if killed_open > 0:
        print(f"  {dirname}: kills {killed_open} open cell(s)")
        return True
    else:
        print(f"  {dirname}: REJECTED — kills no open cells")
        return False


def main():
    parser = argparse.ArgumentParser(description="Validate PR files")
    parser.add_argument(
        "--added-files", nargs="*", default=[],
        help="List of added/modified files to validate"
    )
    args = parser.parse_args()

    if not args.added_files:
        print("No files to validate.")
        return 0

    status = load_status()
    all_ok = True

    for filepath in args.added_files:
        abspath = os.path.join(REPO_ROOT, filepath) if not os.path.isabs(filepath) else filepath

        if filepath.startswith("witnesses/") and filepath.endswith(".yaml"):
            if not validate_witness(abspath, status):
                all_ok = False
        elif filepath.startswith("contradictions/") and "lean_proof.lean" in filepath:
            dirpath = os.path.dirname(abspath)
            if not validate_contradiction(dirpath, status):
                all_ok = False

    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
