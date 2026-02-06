#!/usr/bin/env python3
"""
Assemble and build the Lean project, including contradiction proofs.

1. Copies lean_proof.lean from each contradiction directory into
   lean/GraphAtlas/Contradictions/<id>.lean  (gitignored)
2. Generates lean/GraphAtlas.lean importing everything (saved/restored after build)
3. Runs `lake build`
4. With --check: scans for `sorry` and `axiom` declarations in project source files

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

    return "\n".join(lines)


def check_for_sorry():
    """Check for 'sorry' in our source files (not Mathlib)."""
    hits = []
    for root, dirs, files in os.walk(GRAPH_ATLAS_DIR):
        for fname in files:
            if not fname.endswith(".lean"):
                continue
            fpath = os.path.join(root, fname)
            with open(fpath) as f:
                content = f.read()
            for i, line in enumerate(content.splitlines(), 1):
                stripped = line.split("--")[0]  # remove line comments
                if re.search(r'\bsorry\b', stripped):
                    hits.append((fpath, i, line.strip()))
    return hits


def check_for_axioms():
    """Check for 'axiom' declarations in our source files (not Mathlib)."""
    hits = []
    for root, dirs, files in os.walk(GRAPH_ATLAS_DIR):
        for fname in files:
            if not fname.endswith(".lean"):
                continue
            fpath = os.path.join(root, fname)
            with open(fpath) as f:
                content = f.read()
            for i, line in enumerate(content.splitlines(), 1):
                stripped = line.split("--")[0]  # remove line comments
                if re.search(r'^\s*axiom\b', stripped):
                    hits.append((fpath, i, line.strip()))
    return hits


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

    # 3. Generate root module (save/restore original to avoid dirtying tracked file)
    original_root = None
    if os.path.exists(ROOT_LEAN):
        with open(ROOT_LEAN) as f:
            original_root = f.read()

    new_root = generate_root_module(copied)
    with open(ROOT_LEAN, "w") as f:
        f.write(new_root)
    print("Generated lean/GraphAtlas.lean")

    # 4. Build
    print("\nRunning lake build...")
    try:
        result = run_build()

        if result.stdout:
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

        # 5. Check for sorry and axioms (if --check)
        if do_check:
            problems = []

            print("\nChecking for sorry...")
            sorry_hits = check_for_sorry()
            if sorry_hits:
                print(f"WARNING: Found {len(sorry_hits)} sorry occurrence(s):")
                for fpath, lineno, line in sorry_hits:
                    relpath = os.path.relpath(fpath, REPO_ROOT)
                    print(f"  {relpath}:{lineno}: {line}")
                problems.extend(sorry_hits)
            else:
                print("No sorry found in project files.")

            print("\nChecking for axiom declarations...")
            axiom_hits = check_for_axioms()
            if axiom_hits:
                print(f"WARNING: Found {len(axiom_hits)} axiom declaration(s):")
                for fpath, lineno, line in axiom_hits:
                    relpath = os.path.relpath(fpath, REPO_ROOT)
                    print(f"  {relpath}:{lineno}: {line}")
                problems.extend(axiom_hits)
            else:
                print("No axiom declarations found in project files.")

            if problems:
                return 1

        return 0

    finally:
        # Restore original GraphAtlas.lean to keep working tree clean
        if original_root is not None:
            with open(ROOT_LEAN, "w") as f:
                f.write(original_root)
        # Clean up generated Contradictions directory
        if os.path.isdir(CONTRADICTIONS_LEAN_DIR):
            shutil.rmtree(CONTRADICTIONS_LEAN_DIR)


if __name__ == "__main__":
    sys.exit(main())
