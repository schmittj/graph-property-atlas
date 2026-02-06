# Graph Property Atlas

A collaborative, machine-verified repository classifying which combinations of
Boolean graph properties can coexist in finite simple graphs.

Every claim is backed by evidence: example graphs verified by SageMath, and
impossibility proofs checked by Lean 4 against Mathlib.

## The Idea

Given properties of finite simple graphs — *connected*, *bipartite*, *forest*,
*Hamiltonian*, *planar*, ... — which combinations are simultaneously achievable?

For |P| properties there are 2^|P| possible true/false assignments ("cells").
The atlas classifies each cell as:

- **Realized** — witnessed by an explicit graph (verified by SageMath checkers)
- **Impossible** — ruled out by a formal Lean 4 proof (compiled against Mathlib)
- **Open** — status unknown (contribution opportunity!)

## Current Status

<!-- Update these numbers when properties/witnesses/contradictions change -->

| Properties | Cells | Realized | Impossible | Open | Fill rate |
|------------|-------|----------|------------|------|-----------|
| 3 (connected, bipartite, forest) | 8 | 6 | 2 | 0 | 100% |

**Properties tracked:** connected, bipartite, forest

**Impossibility proofs:**
- *forest* ⇒ *bipartite* (acyclic graphs are 2-colorable) — [Lean proof](contradictions/Nbipartite__forest/lean_proof.lean)

Run `python scripts/coverage_report.py` for a detailed breakdown, or
`python scripts/query.py --open` to find open cells.

## Quick Start

**Verify everything locally:**

```bash
# SageMath environment
conda env create -f environment.yaml
conda activate graph-atlas

# Verify witnesses and property tests
sage scripts/verify_witnesses.sage --cross-check
sage scripts/verify_property_tests.sage

# Consistency check
python scripts/check_consistency.py

# Lean build (requires elan)
python scripts/assemble_lean.py --check
```

## Repository Structure

```
properties/          Property definitions (LaTeX + SageMath + tests)
witnesses/           Example graphs with full property vectors
contradictions/      Impossibility proofs (LaTeX + Lean 4)
lean/                Lean 4 project (Mathlib-based formal definitions)
gallery/             Additional notable graph examples
scripts/             Verification, status computation, and query tools
docs/                Reference documentation
```

See [DESIGN_SPEC.md](DESIGN_SPEC.md) for the full specification.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for how to add witnesses, proofs, and
properties. Contributions of all sizes welcome — from a single witness graph
to a new impossibility proof.

## License

MIT
