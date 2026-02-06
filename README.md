# Graph Property Atlas

A collaborative, machine-verified repository classifying which combinations of
Boolean graph properties can coexist.

## The Idea

Given a set of properties of finite simple graphs — like *connected*, *bipartite*,
*planar*, *Hamiltonian*, etc. — one can ask: which combinations are possible? For
example, can a graph be both a forest and non-bipartite? (No.) Can it be regular,
connected, and Eulerian? (Yes — any even-degree connected graph.)

The **Graph Property Atlas** answers these questions systematically. Every assignment
of true/false to every tracked property is classified as:

- **Realized** — witnessed by an explicit example graph, or
- **Impossible** — ruled out by a formal Lean 4 proof, or
- **Open** — status unknown (a contribution opportunity!).

## What's Here

- **Property definitions** in three aligned formats: LaTeX (human-readable),
  SageMath (computable), and Lean 4 (formally verified).
- **Witness graphs** in YAML with full property vectors and optional certificates.
- **Impossibility proofs** with both informal LaTeX and formal Lean 4 versions.
- **Verification scripts** that check everything is consistent.

## Current Status

| Properties | Cells | Realized | Impossible | Open |
|------------|-------|----------|------------|------|
| 3 (connected, bipartite, forest) | 8 | 6 | 2 | 0 |

## Contributing

This is a young project. We're building toward a larger property set and welcome
contributions of:

- New witness graphs for open cells
- Smaller witnesses that beat existing records
- Lean 4 proofs of impossibility
- New property definitions (requires LaTeX + SageMath + Lean alignment)

See `DESIGN_SPEC.md` for the full specification and `AGENTS.md` for workflow details.

## Setup

**SageMath** (for verification):
```bash
conda env create -f environment.yaml
conda activate graph-atlas
```

**Lean 4** (for formal proofs):
```bash
cd lean && lake build
```

## License

MIT
