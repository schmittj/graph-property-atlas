# Contributing to the Graph Property Atlas

Thanks for your interest! This project classifies combinations of graph
properties as realized, impossible, or open. Every contribution — from a single
witness graph to a formal impossibility proof — moves the atlas forward.

## Ways to Contribute

### 1. Add a witness graph (easiest)

A witness proves that a combination of properties is **realized** by providing
a concrete example graph.

Create a YAML file in `witnesses/`:

```yaml
description: "Short description of the graph"

graph:
  format: edge_list       # or graph6, sparse6
  vertices: 5
  data: [[0,1], [1,2], [2,3], [3,4], [4,0]]

properties:               # every tracked property, no more, no less
  connected: true
  bipartite: false
  forest: false

certificates:             # optional, for faster/certified verification
  bipartite_odd_cycle: [0, 1, 2, 3, 4]

provenance:
  source: "How you found this graph"
  found_by: "manual"      # or "automated", "literature"
```

**Requirements:**
- Graph must have at least 3 vertices (`MIN_VERT`).
- The `properties` dict must list every property in `properties/registry.yaml`.
- All values must match what the SageMath checkers compute.
- The cell should be currently **open**, or the graph should be **smaller** than
  the existing canonical witness for that cell.

**Verify locally before submitting:**
```bash
conda activate graph-atlas
sage scripts/verify_witnesses.sage
python scripts/check_consistency.py
```

### 2. Prove a combination is impossible

An impossibility proof shows that a combination **cannot occur** for any graph
with at least `MIN_VERT` vertices.

Create a directory in `contradictions/` following the naming convention
(sorted property IDs, `N` prefix for false, joined by `__`):

```
contradictions/forest__hamiltonian/
  latex_proof.tex       # informal LaTeX argument
  lean_proof.lean       # formal Lean 4 proof
```

The Lean proof must follow the standard template:

```lean
import GraphAtlas.Defs
import GraphAtlas.Properties.Forest
import GraphAtlas.Properties.Hamiltonian

theorem forest_hamiltonian_contradiction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≥ MIN_VERT)
    (h_forest : IsForest G)
    (h_hamiltonian : IsHamiltonian G) :
    False := by
  ...
```

Add an entry to `contradictions/registry.yaml` and verify:
```bash
python scripts/assemble_lean.py --check
```

### 3. Improve an existing witness

If you find a **smaller graph** (fewer vertices, then fewer edges as tiebreaker)
for an already-realized cell, submit it as a new witness. The previous canonical
witness will be moved to the gallery.

### 4. Add a new property

This is the most involved contribution. A new property requires:

1. `properties/<id>/description.tex` — precise LaTeX definition
2. `properties/<id>/check.sage` — SageMath checker with `CERTIFICATE_MODE`
3. `lean/GraphAtlas/Properties/<Name>.lean` — Lean 4 definition
4. Entry in `properties/registry.yaml`
5. All existing witness and gallery files updated with the new property

The three definitions (LaTeX, Sage, Lean) must agree precisely. See
[DESIGN_SPEC.md](DESIGN_SPEC.md) for the full specification including certificate
modes and naming conventions.

## Naming Conventions

| Thing | Convention | Example |
|-------|-----------|---------|
| Property IDs | lowercase snake_case | `triangle_free` |
| Witness files | descriptive snake_case | `petersen.yaml` |
| Contradiction dirs | sorted IDs, `N` prefix for false, `__`-joined | `Nbipartite__forest` |
| Lean theorems | dir name with `__`→`_`, `N`→`not_`, + `_contradiction` | `not_bipartite_forest_contradiction` |

## Running CI Locally

```bash
# Full verification suite
conda activate graph-atlas
sage scripts/verify_witnesses.sage --cross-check
sage scripts/verify_property_tests.sage
python scripts/check_consistency.py
python scripts/compute_status.py
python scripts/coverage_report.py

# Lean build
python scripts/assemble_lean.py --check
```

## Finding Open Cells

```bash
python scripts/compute_status.py          # generates status.json
python scripts/query.py --open            # list all open cells
python scripts/query.py --open --limit 5  # first 5 open cells
```

## Full Specification

For complete details on data formats, certificate schemas, CI policy, and
architectural decisions, see [DESIGN_SPEC.md](DESIGN_SPEC.md).
