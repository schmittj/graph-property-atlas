#!/usr/bin/env python3
"""
Assemble and build the Lean project, including contradiction proofs.

1. Copies lean_proof.lean from each contradiction directory into
   lean/GraphAtlas/Contradictions/<id>.lean
2. Generates lean/GraphAtlas.lean importing everything
3. Runs `lake build`
4. Checks for `sorry` in source files (not in Mathlib)
5. Reports results

Usage:
  python3 scripts/assemble_lean.py           # assemble + build
  python3 scripts/assemble_lean.py --check   # also check for sorry/axioms
"""

import os
import re
import shutil
import subprocess
import sys

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEAN_DIR = os.path.join(REPO_ROOT, "lean")
CONTRADICTIONS_DIR = os.path.join(REPO_ROOT, "contradictions")
GRAPH_ATLAS_DIR = os.path.join(LEAN_DIR, "GraphAtlas")
CONTRADICTIONS_LEAN_DIR = os.path.join(GRAPH_ATLAS_DIR, "Contradictions")
ROOT_LEAN = os.path.join(LEAN_DIR, "GraphAtlas.lean")


def find_contradiction_proofs():
    """Find all lean_proof.lean files in contradiction directories."""
    proofs = []
    if not os.path.isdir(CONTRADICTIONS_DIR):
        return proofs
    for dirname in sorted(os.listdir(CONTRADICTIONS_DIR)):
        dirpath = os.path.join(CONTRADICTIONS_DIR, dirname)
        if not os.path.isdir(dirpath):
            continue
        lean_file = os.path.join(dirpath, "lean_proof.lean")
        if os.path.exists(lean_file):
            proofs.append((dirname, lean_file))
    return proofs


def copy_contradiction_proofs(proofs):
    """Copy contradiction proofs into the Lean project tree."""
    os.makedirs(CONTRADICTIONS_LEAN_DIR, exist_ok=True)
    copied = []
    for dirname, src_path in proofs:
        # Convert contradiction ID to a valid Lean module name
        # e.g. "Nbipartite__forest" -> "NbipartiteForest"
        module_name = dirname.replace("__", "_").title().replace("_", "")
        dst_path = os.path.join(CONTRADICTIONS_LEAN_DIR, f"{module_name}.lean")
        shutil.copy2(src_path, dst_path)
        copied.append((dirname, module_name, dst_path))
    return copied


def generate_root_module(contradiction_modules):
    """Generate lean/GraphAtlas.lean importing all modules."""
    # Find all property definitions
    props_dir = os.path.join(GRAPH_ATLAS_DIR, "Properties")
    prop_modules = []
    if os.path.isdir(props_dir):
        for f in sorted(os.listdir(props_dir)):
            if f.endswith(".lean"):
                prop_modules.append(f[:-5])  # strip .lean

    # Find all shared lemmas
    lemmas_dir = os.path.join(GRAPH_ATLAS_DIR, "Lemmas")
    lemma_modules = []
    if os.path.isdir(lemmas_dir):
        for f in sorted(os.listdir(lemmas_dir)):
            if f.endswith(".lean"):
                lemma_modules.append(f[:-5])

    lines = ["import GraphAtlas.Defs"]
    for m in prop_modules:
        lines.append(f"import GraphAtlas.Properties.{m}")
    for m in lemma_modules:
        lines.append(f"import GraphAtlas.Lemmas.{m}")
    for dirname, module_name, _ in contradiction_modules:
        lines.append(f"import GraphAtlas.Contradictions.{module_name}")
    lines.append("")

    with open(ROOT_LEAN, "w") as f:
        f.write("\n".join(lines))


def check_for_sorry(contradiction_modules):
    """Check for 'sorry' in our source files (not Mathlib)."""
    sorry_files = []

    # Check all .lean files under lean/GraphAtlas/
    for root, dirs, files in os.walk(GRAPH_ATLAS_DIR):
        for fname in files:
            if not fname.endswith(".lean"):
                continue
            fpath = os.path.join(root, fname)
            with open(fpath) as f:
                content = f.read()
            # Look for sorry as a standalone token (not in comments)
            for i, line in enumerate(content.splitlines(), 1):
                stripped = line.split("--")[0]  # remove line comments
                if re.search(r'\bsorry\b', stripped):
                    sorry_files.append((fpath, i, line.strip()))

    return sorry_files


def run_build():
    """Run lake build in the lean directory."""
    result = subprocess.run(
        ["lake", "build"],
        cwd=LEAN_DIR,
        capture_output=True,
        text=True,
        timeout=600,
    )
    return result


def main():
    do_check = "--check" in sys.argv

    # 1. Find contradiction proofs
    proofs = find_contradiction_proofs()
    print(f"Found {len(proofs)} contradiction proof(s)")
    for dirname, path in proofs:
        print(f"  {dirname}: {os.path.basename(path)}")

    # 2. Copy into lean project
    copied = copy_contradiction_proofs(proofs)
    print(f"\nCopied {len(copied)} proof(s) into lean/GraphAtlas/Contradictions/")

    # 3. Generate root module
    generate_root_module(copied)
    print("Generated lean/GraphAtlas.lean")

    # 4. Build
    print("\nRunning lake build...")
    result = run_build()

    if result.stdout:
        # Print last 20 lines of stdout
        lines = result.stdout.strip().splitlines()
        for line in lines[-20:]:
            print(f"  {line}")

    if result.returncode != 0:
        print(f"\nBUILD FAILED (exit code {result.returncode})")
        if result.stderr:
            for line in result.stderr.strip().splitlines()[-20:]:
                print(f"  {line}")
        return 1

    print("\nBuild succeeded!")

    # 5. Check for sorry (if --check)
    if do_check:
        print("\nChecking for sorry...")
        sorry_files = check_for_sorry(copied)
        if sorry_files:
            print(f"WARNING: Found {len(sorry_files)} sorry occurrence(s):")
            for fpath, lineno, line in sorry_files:
                relpath = os.path.relpath(fpath, REPO_ROOT)
                print(f"  {relpath}:{lineno}: {line}")
            return 1
        else:
            print("No sorry found in project files!")

    return 0


if __name__ == "__main__":
    sys.exit(main())
