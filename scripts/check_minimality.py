#!/usr/bin/env python3
"""
Check and update minimality status of contradictions.

A contradiction (S, a) is minimal if removing any single condition yields a
satisfiable partial assignment. This script checks each sub-assignment against
existing witnesses.

Usage:
  python3 scripts/check_minimality.py           # report only
  python3 scripts/check_minimality.py --update  # update registry.yaml in place
"""

import json
import os
import sys

import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WITNESSES_DIR = os.path.join(REPO_ROOT, "witnesses")
CONTRADICTIONS_DIR = os.path.join(REPO_ROOT, "contradictions")
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")


def load_witnesses():
    """Load all witness property vectors."""
    witnesses = []
    if not os.path.isdir(WITNESSES_DIR):
        return witnesses
    for filename in sorted(os.listdir(WITNESSES_DIR)):
        if not filename.endswith(".yaml"):
            continue
        filepath = os.path.join(WITNESSES_DIR, filename)
        with open(filepath) as f:
            data = yaml.safe_load(f)
        witnesses.append({
            "file": filename,
            "properties": data.get("properties", {}),
        })
    return witnesses


def load_contradictions():
    registry_path = os.path.join(CONTRADICTIONS_DIR, "registry.yaml")
    if not os.path.exists(registry_path):
        return {"contradictions": []}
    with open(registry_path) as f:
        return yaml.safe_load(f)


def witness_compatible(witness_props, partial_assignment):
    """Check if a witness is compatible with a partial assignment."""
    for prop, val in partial_assignment.items():
        if witness_props.get(prop) != val:
            return False
    return True


def check_minimality(contradiction, witnesses):
    """Check if a contradiction is minimal.

    Returns (is_minimal, missing_sub_assignments) where:
    - is_minimal: True if all sub-assignments have compatible witnesses
    - missing_sub_assignments: list of sub-assignments with no compatible witness
    """
    assignments = contradiction["assignments"]
    props = list(assignments.keys())
    missing = []

    for drop_prop in props:
        # Form sub-assignment with one condition removed
        sub = {k: v for k, v in assignments.items() if k != drop_prop}

        # Check if any witness satisfies this sub-assignment
        found = False
        for w in witnesses:
            if witness_compatible(w["properties"], sub):
                found = True
                break

        if not found:
            missing.append({
                "dropped": drop_prop,
                "sub_assignment": sub,
            })

    return len(missing) == 0, missing


def main():
    do_update = "--update" in sys.argv
    witnesses = load_witnesses()
    registry = load_contradictions()
    contradictions = registry.get("contradictions", [])

    if not contradictions:
        print("No contradictions found.")
        return 0

    print(f"Checking minimality of {len(contradictions)} contradiction(s) "
          f"against {len(witnesses)} witness(es)")
    print()

    updated = False
    for c in contradictions:
        cid = c["id"]
        current_status = c.get("minimal", "unknown")

        if current_status == "no":
            print(f"  {cid}: minimal=no (skipping, known non-minimal)")
            continue

        is_minimal, missing = check_minimality(c, witnesses)

        if is_minimal:
            print(f"  {cid}: MINIMAL (all sub-assignments have witnesses)")
            if current_status != "yes":
                c["minimal"] = "yes"
                updated = True
        elif current_status == "yes":
            # Inconsistency: marked yes but we can't verify
            print(f"  {cid}: WARNING — marked minimal=yes but "
                  f"{len(missing)} sub-assignment(s) lack witnesses")
        else:
            print(f"  {cid}: unknown ({len(missing)} sub-assignment(s) need witnesses)")
            for m in missing:
                dropped = m["dropped"]
                sub = m["sub_assignment"]
                sub_str = ", ".join(
                    f"{k}={'T' if v else 'F'}" for k, v in sorted(sub.items())
                )
                print(f"    WANTED: witness for {{{sub_str}}} (drop {dropped})")

    if do_update and updated:
        registry_path = os.path.join(CONTRADICTIONS_DIR, "registry.yaml")
        with open(registry_path, "w") as f:
            yaml.dump(registry, f, default_flow_style=False, sort_keys=False)
        print(f"\nUpdated {registry_path}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
