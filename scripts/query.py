#!/usr/bin/env python3
"""
CLI tool for querying the Graph Property Atlas.

Uses status.json (computed by compute_status.py) plus raw data files.

Usage:
  python3 scripts/query.py --status                           # summary
  python3 scripts/query.py --open [--limit N]                 # list open cells
  python3 scripts/query.py --cell '{"connected":true,...}'    # check one cell
  python3 scripts/query.py --assignment '{"forest":true}'     # partial assignment
"""

import argparse
import itertools
import json
import os
import sys

import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATUS_PATH = os.path.join(REPO_ROOT, "status.json")
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")
CONTRADICTIONS_DIR = os.path.join(REPO_ROOT, "contradictions")


def load_status():
    if not os.path.exists(STATUS_PATH):
        print("status.json not found. Run scripts/compute_status.py first.")
        sys.exit(1)
    with open(STATUS_PATH) as f:
        return json.load(f)


def load_property_ids():
    registry_path = os.path.join(PROPERTIES_DIR, "registry.yaml")
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return [p["id"] for p in data["properties"]]


def load_contradictions():
    registry_path = os.path.join(CONTRADICTIONS_DIR, "registry.yaml")
    if not os.path.exists(registry_path):
        return []
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return data.get("contradictions", [])


def cell_key(props_dict):
    return json.dumps(props_dict, sort_keys=True)


def cell_extends(cell, assignment):
    for prop, val in assignment.items():
        if cell.get(prop) != val:
            return False
    return True


def cmd_status(status):
    total = status["total_cells"]
    print(f"Properties: {', '.join(status['property_set'])}")
    print(f"Realized: {status['realized']}/{total}, "
          f"Impossible: {status['impossible']}/{total}, "
          f"Open: {status['open']}/{total}")


def cmd_open(status, limit):
    property_ids = status["property_set"]
    canonical = status.get("canonical_witnesses", {})
    contradictions = load_contradictions()

    count = 0
    for bits in itertools.product([True, False], repeat=len(property_ids)):
        cell = dict(zip(property_ids, bits))
        key = cell_key(cell)

        if key in canonical:
            continue
        killed = False
        for c in contradictions:
            if cell_extends(cell, c["assignments"]):
                killed = True
                break
        if killed:
            continue

        # Open cell
        count += 1
        assignment_str = ", ".join(
            f"{k}={'T' if v else 'F'}" for k, v in sorted(cell.items())
        )
        print(f"  {assignment_str}")
        if limit and count >= limit:
            print(f"  ... (showing {limit} of possibly more)")
            break

    if count == 0:
        print("No open cells!")


def cmd_cell(status, cell_json):
    cell = json.loads(cell_json)
    key = cell_key(cell)
    canonical = status.get("canonical_witnesses", {})
    contradictions = load_contradictions()

    if key in canonical:
        info = canonical[key]
        print(f"REALIZED by {info['file']} ({info.get('order', '?')} vertices)")
        return

    for c in contradictions:
        if cell_extends(cell, c["assignments"]):
            print(f"IMPOSSIBLE — extends contradiction {c['id']}")
            return

    print("OPEN — no witness or contradiction known")


def cmd_assignment(status, assignment_json):
    assignment = json.loads(assignment_json)
    property_ids = status["property_set"]
    canonical = status.get("canonical_witnesses", {})
    contradictions = load_contradictions()

    # Check if any contradiction is a subset of this assignment
    for c in contradictions:
        if cell_extends(assignment, c["assignments"]):
            print(f"IMPOSSIBLE — extends contradiction {c['id']}")
            return

    # Count compatible witnesses
    compatible = []
    for key, info in canonical.items():
        cell = json.loads(key)
        if cell_extends(cell, assignment):
            compatible.append(info)

    if compatible:
        print(f"POSSIBLE — {len(compatible)} compatible witness(es):")
        for info in compatible[:10]:
            print(f"  {info['file']}")
    else:
        print("No known witnesses compatible with this assignment.")
        # Check if any sub-contradiction applies
        for c in contradictions:
            if all(
                c["assignments"].get(k) == v
                for k, v in assignment.items()
                if k in c["assignments"]
            ):
                print(f"  (partial overlap with contradiction {c['id']})")


def main():
    parser = argparse.ArgumentParser(description="Query the Graph Property Atlas")
    parser.add_argument("--status", action="store_true", help="Print summary")
    parser.add_argument("--open", action="store_true", help="List open cells")
    parser.add_argument("--limit", type=int, default=0, help="Limit open cells output")
    parser.add_argument("--cell", type=str, help="Check a specific cell (JSON)")
    parser.add_argument(
        "--assignment", type=str, help="Check a partial assignment (JSON)"
    )

    args = parser.parse_args()
    status = load_status()

    if args.status:
        cmd_status(status)
    elif args.open:
        cmd_open(status, args.limit)
    elif args.cell:
        cmd_cell(status, args.cell)
    elif args.assignment:
        cmd_assignment(status, args.assignment)
    else:
        cmd_status(status)

    return 0


if __name__ == "__main__":
    sys.exit(main())
