#!/usr/bin/env sage
"""
Verify property test suites.

For each property with a tests/ directory, loads each test case YAML and
verifies the Sage checker returns the expected value.

Usage:
  sage verify_property_tests.sage

Exit code 0 if all pass, 1 if any fail.
"""

import os
import sys
import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")


# ---------------------------------------------------------------------------
# Checker cache
# ---------------------------------------------------------------------------

_checker_cache = {}

def load_checker(prop_id):
    if prop_id in _checker_cache:
        return _checker_cache[prop_id]
    checker_path = os.path.join(PROPERTIES_DIR, prop_id, "check.sage")
    if not os.path.exists(checker_path):
        raise FileNotFoundError(f"Checker not found: {checker_path}")
    with open(checker_path) as f:
        code = f.read()
    namespace = {}
    exec(compile(code, checker_path, "exec"), namespace)
    if "check" not in namespace:
        raise ValueError(f"Checker {checker_path} does not define 'check'")
    _checker_cache[prop_id] = namespace["check"]
    return namespace["check"]


# ---------------------------------------------------------------------------
# Graph decoding (same as verify_witnesses.sage)
# ---------------------------------------------------------------------------

def decode_graph(graph_data):
    fmt = graph_data["format"]
    if fmt == "edge_list":
        n = graph_data["vertices"]
        edges = graph_data["data"]
        for edge in edges:
            if len(edge) != 2:
                raise ValueError(f"Edge must have exactly 2 endpoints, got {edge}")
            u, v = edge
            if u == v:
                raise ValueError(f"Self-loop not allowed: {u}-{v}")
            if not (0 <= u < n and 0 <= v < n):
                raise ValueError(f"Edge endpoint out of range [0, {n}): {u}-{v}")
        edge_set = set()
        for u, v in edges:
            canon = (min(u, v), max(u, v))
            if canon in edge_set:
                raise ValueError(f"Duplicate edge: {u}-{v}")
            edge_set.add(canon)
        G = Graph(n)
        for u, v in edges:
            G.add_edge(u, v)
        return G
    elif fmt in ("graph6", "sparse6"):
        return Graph(graph_data["data"])
    else:
        raise ValueError(f"Unknown graph format: {fmt}")


# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------

def main():
    registry_path = os.path.join(PROPERTIES_DIR, "registry.yaml")
    with open(registry_path) as f:
        registry = yaml.safe_load(f)
    property_ids = [p["id"] for p in registry["properties"]]

    total_tests = 0
    total_errors = 0

    for prop_id in property_ids:
        tests_dir = os.path.join(PROPERTIES_DIR, prop_id, "tests")
        if not os.path.isdir(tests_dir):
            continue

        test_files = sorted(
            f for f in os.listdir(tests_dir) if f.endswith(".yaml")
        )
        if not test_files:
            continue

        print(f"Property: {prop_id} ({len(test_files)} test(s))")

        try:
            checker = load_checker(prop_id)
        except Exception as e:
            print(f"  ERROR: Failed to load checker: {e}")
            total_errors += len(test_files)
            total_tests += len(test_files)
            continue

        for test_file in test_files:
            total_tests += 1
            test_path = os.path.join(tests_dir, test_file)
            try:
                with open(test_path) as f:
                    data = yaml.safe_load(f)
                G = decode_graph(data["graph"])
                expected = data["expected"]
                result = checker(G)
                if result != expected:
                    print(f"  FAIL  {test_file}: expected {expected}, got {result}")
                    total_errors += 1
                else:
                    print(f"    OK  {test_file}")
            except Exception as e:
                print(f"  ERROR {test_file}: {e}")
                total_errors += 1

    print()
    if total_tests == 0:
        print("No test suites found.")
        return 0
    elif total_errors > 0:
        print(f"FAILED: {total_errors}/{total_tests} test(s) failed")
        return 1
    else:
        print(f"PASSED: {total_tests} test(s) across {len(property_ids)} property(ies)")
        return 0


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
