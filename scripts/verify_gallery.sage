#!/usr/bin/env sage
"""
Verify all gallery files in the gallery/ directory.

Same verification logic as verify_witnesses.sage, but for gallery files.
Gallery files have the same schema as witnesses but with looser merge criteria
(notability-based rather than strict additive policy).

Usage:
  sage verify_gallery.sage                 # standard verification
  sage verify_gallery.sage --cross-check   # also cross-check certified results

Exit code 0 if all pass, 1 if any fail.
"""

import os
import sys
import yaml

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GALLERY_DIR = os.path.join(REPO_ROOT, "gallery")
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


# ---------------------------------------------------------------------------
# Reuse checker/graph infrastructure from verify_witnesses
# ---------------------------------------------------------------------------

# We import the shared logic by exec'ing the verify_witnesses module.
# This avoids duplicating the checker cache, graph decoding, etc.

_verify_witnesses_path = os.path.join(REPO_ROOT, "scripts", "verify_witnesses.sage")
_vw_namespace = {}
with open(_verify_witnesses_path) as _f:
    exec(compile(_f.read(), _verify_witnesses_path, "exec"), _vw_namespace)

verify_witness = _vw_namespace["verify_witness"]


def main():
    cross_check = "--cross-check" in sys.argv

    config = load_config()
    min_vert = config["min_vert"]
    property_ids = load_property_registry()

    print(f"Properties: {property_ids}")
    print(f"MIN_VERT: {min_vert}")
    if cross_check:
        print("Cross-check mode: ON")
    print()

    if not os.path.isdir(GALLERY_DIR):
        print("No gallery/ directory found.")
        return 0

    gallery_files = sorted(
        os.path.join(GALLERY_DIR, f)
        for f in os.listdir(GALLERY_DIR)
        if f.endswith(".yaml")
    )

    if not gallery_files:
        print("No gallery files found.")
        return 0

    all_errors = []
    for filepath in gallery_files:
        name = os.path.basename(filepath)
        errors = verify_witness(filepath, property_ids, min_vert, cross_check)
        if errors:
            print(f"FAIL  {name}")
            for e in errors:
                print(f"  {e}")
            all_errors.extend(errors)
        else:
            print(f"  OK  {name}")

    print()
    if all_errors:
        print(f"FAILED: {len(all_errors)} error(s) in {len(gallery_files)} gallery file(s)")
        return 1
    else:
        print(f"PASSED: {len(gallery_files)} gallery file(s) verified")
        return 0


if __name__ == "__main__":
    # os._exit bypasses Sage's sys.exit interception which mishandles exit codes
    import os as _os
    _rc = main()
    sys.stdout.flush()
    sys.stderr.flush()
    _os._exit(_rc)
