#!/usr/bin/env sage
"""
Verify all witness files in the witnesses/ directory.

For each witness:
  1. Parse YAML and decode the graph.
  2. Check that the graph has >= MIN_VERT vertices.
  3. For each property, run the checker and compare against declared value.
  4. Validate any certificates/counter-certificates.

Exit code 0 if all pass, 1 if any fail.
"""

import os
import sys
import importlib.util
import yaml

# ---------------------------------------------------------------------------
# Configuration
# ---------------------------------------------------------------------------

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WITNESSES_DIR = os.path.join(REPO_ROOT, "witnesses")
PROPERTIES_DIR = os.path.join(REPO_ROOT, "properties")
CONFIG_PATH = os.path.join(REPO_ROOT, "config.yaml")


def load_config():
    with open(CONFIG_PATH) as f:
        return yaml.safe_load(f)


def load_property_registry():
    registry_path = os.path.join(PROPERTIES_DIR, "registry.yaml")
    with open(registry_path) as f:
        data = yaml.safe_load(f)
    return [p["id"] for p in data["properties"]]


def load_checker(prop_id):
    """Load a property checker from properties/<id>/check.sage."""
    checker_path = os.path.join(PROPERTIES_DIR, prop_id, "check.sage")
    if not os.path.exists(checker_path):
        raise FileNotFoundError(f"Checker not found: {checker_path}")
    # Read and exec the sage file to get the check function
    with open(checker_path) as f:
        code = f.read()
    namespace = {}
    exec(compile(code, checker_path, "exec"), namespace)
    if "check" not in namespace:
        raise ValueError(f"Checker {checker_path} does not define a 'check' function")
    return namespace["check"]


def decode_graph(graph_data):
    """Decode a graph from witness YAML data."""
    fmt = graph_data["format"]
    if fmt == "edge_list":
        n = graph_data["vertices"]
        edges = graph_data["data"]
        G = Graph(n)
        for u, v in edges:
            G.add_edge(u, v)
        return G
    elif fmt == "graph6":
        return Graph(graph_data["data"])
    elif fmt == "sparse6":
        return Graph(graph_data["data"])
    else:
        raise ValueError(f"Unknown graph format: {fmt}")


def verify_witness(filepath, property_ids, min_vert):
    """Verify a single witness file. Returns list of error messages."""
    errors = []
    name = os.path.basename(filepath)

    with open(filepath) as f:
        data = yaml.safe_load(f)

    # Decode graph
    try:
        G = decode_graph(data["graph"])
    except Exception as e:
        return [f"{name}: Failed to decode graph: {e}"]

    # Check vertex count
    if G.order() < min_vert:
        errors.append(f"{name}: Graph has {G.order()} vertices, need >= {min_vert}")

    # Check that all properties are declared
    declared = data.get("properties", {})
    declared_ids = set(declared.keys())
    expected_ids = set(property_ids)

    missing = expected_ids - declared_ids
    extra = declared_ids - expected_ids
    if missing:
        errors.append(f"{name}: Missing properties: {missing}")
    if extra:
        errors.append(f"{name}: Unknown properties: {extra}")

    # Gather certificates and counter-certificates
    certs = data.get("certificates", {}) or {}
    counter_certs = data.get("counter_certificates", {}) or {}

    # Verify each property
    for prop_id in property_ids:
        if prop_id not in declared:
            continue

        declared_value = declared[prop_id]
        try:
            checker = load_checker(prop_id)
        except Exception as e:
            errors.append(f"{name}/{prop_id}: Failed to load checker: {e}")
            continue

        # Collect relevant kwargs (certificates + counter-certificates)
        kwargs = {}
        for key, val in certs.items():
            kwargs[key] = val
        for key, val in counter_certs.items():
            kwargs[key] = val

        try:
            computed = checker(G, **kwargs)
        except Exception as e:
            errors.append(f"{name}/{prop_id}: Checker raised error: {e}")
            continue

        if computed != declared_value:
            errors.append(
                f"{name}/{prop_id}: Declared {declared_value}, computed {computed}"
            )

    return errors


def main():
    config = load_config()
    min_vert = config["min_vert"]
    property_ids = load_property_registry()

    print(f"Properties: {property_ids}")
    print(f"MIN_VERT: {min_vert}")
    print()

    # Find all witness files
    witness_files = sorted(
        os.path.join(WITNESSES_DIR, f)
        for f in os.listdir(WITNESSES_DIR)
        if f.endswith(".yaml")
    )

    if not witness_files:
        print("No witness files found.")
        return 0

    all_errors = []
    for filepath in witness_files:
        name = os.path.basename(filepath)
        errors = verify_witness(filepath, property_ids, min_vert)
        if errors:
            print(f"FAIL  {name}")
            for e in errors:
                print(f"  {e}")
            all_errors.extend(errors)
        else:
            print(f"  OK  {name}")

    print()
    if all_errors:
        print(f"FAILED: {len(all_errors)} error(s) in {len(witness_files)} witness(es)")
        return 1
    else:
        print(f"PASSED: {len(witness_files)} witness(es) verified")
        return 0


if __name__ == "__main__":
    exit_code = main()
    sys.exit(exit_code)
