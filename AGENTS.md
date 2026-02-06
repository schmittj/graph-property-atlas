# Graph Property Atlas — Agent & Workflow Guide

## Project Overview

This repository aims to classify every Boolean property assignment for finite simple
graphs as **realized** (witnessed by an explicit graph), **impossible** (ruled out by
a Lean 4 proof), or **open**. See `DESIGN_SPEC.md` for the full specification.

## Working Principles

- **Collaborative culture**: Design questions are worked out together. We prefer
  sustainable, systematic solutions over quick patches.
- **Frequent commits**: Keep a steady log of progress with small, focused commits.
- **Minimal working version first**: Get the pipeline working end-to-end with a small
  property set before scaling up.
- **Three-way alignment**: Every property must agree across LaTeX description, SageMath
  checker, and Lean 4 definition. Misalignment is the most dangerous class of bug.

## Repository Layout

See `DESIGN_SPEC.md` §4 for the full directory structure. Key points:

- `properties/` — one directory per property (description.tex, check.sage, tests/)
- `witnesses/` — YAML files with graph data and full property vectors
- `contradictions/` — each gets a directory with latex_proof.tex + lean_proof.lean
- `lean/` — Lean 4 project with Defs.lean, Properties/, Lemmas/
- `scripts/` — Python/Sage scripts for verification, status computation, etc.

## Environment Setup

- **SageMath**: Managed via conda environment (`environment.yaml`). Use `conda activate
  graph-atlas` before running Sage scripts.
- **Lean 4**: Managed via elan. The `lean/lean-toolchain` pins the version.
- **Python**: Use the conda environment (includes PyYAML and other dependencies).

## Conventions

- Property IDs: lowercase snake_case (`vertex_transitive`, `triangle_free`)
- Contradiction directories: sorted property IDs, `N` prefix for false, joined by `__`
- Lean theorem names: directory name with `__` → `_`, `N` → `not_`, + `_contradiction`
- Witness filenames: freeform descriptive snake_case
- `MIN_VERT = 3`: minimum vertices for a witness graph

## Working with Lean

- Claude skills for Lean 4 are available (build, repair, sorry-filling, etc.)
- Load these when working on Lean proof files.
- Johannes has limited Mathlib experience — document Lean decisions clearly.
- The lean/ directory is built by CI using `scripts/assemble_lean.py`.

## Working with SageMath

- Always run sage scripts with the conda environment activated.
- Property checkers follow the `check(G, **kwargs) -> bool` signature.
- Certificates are pure data, never executable code.

## Git Workflow

- Work on `main` for now (single-developer phase).
- Commit frequently with clear messages describing what was added/changed.
- GraphProp* files are .gitignored — they contain pre-project analysis and may be
  incorporated later.
