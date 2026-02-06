# Graph Property Atlas — Development Guide

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

- Property predicates are `abbrev`s wrapping Mathlib definitions (transparent to tactics).
- The `lean/` directory is built by CI using `scripts/assemble_lean.py`.
- See `docs/mathlib_graph_theory.md` for the Mathlib API reference.

## Working with SageMath

- Run sage scripts via `conda run -n graph-atlas sage <script>`.
- Certificates are pure data, never executable code.

### Property Checker Architecture

Each `check.sage` declares a `CERTIFICATE_MODE`:

- **`"generic"`** — Cheap algorithm, no certificates. Just `check(G)`. (connected, forest)
- **`"both"`** — Has generic + certified paths. `check(G)` without kwargs gives
  the generic result; `check(G, **certs)` uses the certified path.
  `--cross-check` calls both and compares. (bipartite, hamiltonian)
- **`"certified"`** — No practical generic algorithm. Witnesses must provide certs.
  (cayley, vertex_transitive)

Design rationale: certificates exist to make verification tractable for expensive
properties. Cross-checking against generic algorithms catches cert/algorithm
misalignment but should be optional since it can be slow.

## Git Workflow

- Work on `main` for now (single-developer phase).
- Commit frequently with clear messages describing what was added/changed.
