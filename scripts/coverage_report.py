#!/usr/bin/env python3
"""
Print summary statistics for the Graph Property Atlas.

Reads status.json (computed by compute_status.py) and prints a human-readable
coverage report including totals, per-contradiction breakdowns, and canonical
witnesses.

Usage:
  python3 scripts/coverage_report.py
  python3 scripts/coverage_report.py --json   # machine-readable output
"""

import json
import os
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
STATUS_PATH = os.path.join(REPO_ROOT, "status.json")


def main():
    json_mode = "--json" in sys.argv

    if not os.path.exists(STATUS_PATH):
        print("status.json not found. Run scripts/compute_status.py first.")
        return 1

    with open(STATUS_PATH) as f:
        status = json.load(f)

    total = status["total_cells"]
    realized = status["realized"]
    impossible = status["impossible"]
    open_cells = status["open"]
    props = status["property_set"]
    n_props = len(props)
    fill_pct = 100 * (realized + impossible) / total if total else 0

    if json_mode:
        summary = {
            "properties": n_props,
            "total_cells": total,
            "realized": realized,
            "impossible": impossible,
            "open": open_cells,
            "fill_percent": round(fill_pct, 1),
        }
        print(json.dumps(summary, indent=2))
        return 0

    print(f"Graph Property Atlas — Coverage Report")
    print(f"=" * 50)
    print(f"Properties ({n_props}): {', '.join(props)}")
    print(f"Total cells: {total}")
    print()
    print(f"  Realized:   {realized:>5}  ({100*realized/total:.1f}%)")
    print(f"  Impossible: {impossible:>5}  ({100*impossible/total:.1f}%)")
    print(f"  Open:       {open_cells:>5}  ({100*open_cells/total:.1f}%)")
    print(f"  Fill rate:  {fill_pct:.1f}%")
    print()

    # Per-contradiction breakdown
    by_contradiction = status.get("impossible_cells_by_contradiction", {})
    if by_contradiction:
        print("Impossible cells by contradiction:")
        for cid, count in sorted(by_contradiction.items(), key=lambda x: -x[1]):
            print(f"  {cid}: {count} cell(s)")
        print()

    # Canonical witnesses
    canonical = status.get("canonical_witnesses", {})
    if canonical:
        print(f"Canonical witnesses ({len(canonical)}):")
        for key, info in sorted(canonical.items()):
            order = info.get("order", "?")
            size = info.get("size", "?")
            size_str = f", {size} edges" if size != sys.maxsize else ""
            print(f"  {info['file']}: {order} vertices{size_str}")
        print()

    print(f"Generated: {status.get('generated_at', 'unknown')}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
