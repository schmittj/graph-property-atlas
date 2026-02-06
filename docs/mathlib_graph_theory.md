# Mathlib Graph Theory Reference

Condensed reference for Mathlib's `SimpleGraph` API, focused on what's relevant
to the Graph Property Atlas. Sources: Mathlib4 docs, `mathlib4` repo, and our
own usage experience.

## Core Type

```lean
structure SimpleGraph (V : Type u) : Type u :=
  (Adj : V → V → Prop)
  (symm : Symmetric Adj)
  (loopless : Irreflexive Adj)
```

Module: `Mathlib.Combinatorics.SimpleGraph.Basic`

## Properties We Use

| Atlas property | Lean definition | Mathlib name | Module |
|---|---|---|---|
| connected | `G.Connected` | `SimpleGraph.Connected` | `Connectivity.Connected` |
| bipartite | `G.Colorable 2` | `SimpleGraph.IsBipartite` | `Bipartite` |
| forest (acyclic) | `G.IsAcyclic` | `SimpleGraph.IsAcyclic` | `Acyclic` |

### Connectivity (`Connectivity/Connected.lean`)
- `SimpleGraph.Connected` = `G.Preconnected ∧ Nonempty V` (structure)
- `SimpleGraph.Preconnected` = ∀ u v, `G.Reachable u v`
- `G.Reachable u v` = ∃ walk from u to v
- Related: `G.connectedComponent`, `G.ConnectedComponent`

### Bipartiteness (`Bipartite.lean`)
- `SimpleGraph.IsBipartite G` is an `abbrev` for `G.Colorable 2`
- `G.Colorable n` = ∃ proper coloring with `n` colors
- Key theorem: `SimpleGraph.IsBipartite.iff_no_odd_cycle` — bipartite ↔ no odd cycle

### Acyclicity (`Acyclic.lean`)
- `SimpleGraph.IsAcyclic` = ∀ v, ∀ (p : G.Walk v v), ¬p.IsCycle
- `SimpleGraph.IsTree` = `G.Connected ∧ G.IsAcyclic`
- **Key lemma we used**: `IsAcyclic.isBipartite` — acyclic graphs are bipartite
  (found at `Acyclic.lean:615`; proof: trees are 2-colorable)

## Lemmas Used in Atlas Proofs

### `Nbipartite__forest` (forest ⇒ bipartite)
```lean
-- One-liner using Mathlib:
h_not_bipartite h_forest.isBipartite
-- where h_forest : IsForest G  (= G.IsAcyclic)
-- and   h_not_bipartite : ¬IsBipartite G  (= ¬G.Colorable 2)
```

## Properties Available for Future Expansion

### Already in Mathlib (likely easy to wrap)
| Property | Mathlib concept | Module |
|---|---|---|
| tree | `SimpleGraph.IsTree` | `Acyclic` |
| hamiltonian | `SimpleGraph.IsHamiltonian` | `Hamiltonian` |
| eulerian | `SimpleGraph.Walk.IsEulerian` | `Trails` |
| k-colorable | `SimpleGraph.Colorable k` | `Coloring` |
| regular | `SimpleGraph.IsRegularOfDegree d` | `StronglyRegular` |
| planar | Not yet in Mathlib | — |
| triangle-free | `G.CliqueFree 3` | `Clique` |
| vertex-transitive | Not directly; need `Aut(G)` action | — |
| self-complementary | `G ≃g Gᶜ` via graph iso | `Iso` |
| complete | `G = ⊤` | `Basic` |
| perfect | Not yet in Mathlib | — |

### Finite combinatorics layer (`Finite.lean`)
- `SimpleGraph.edgeFinset` — edges as `Finset`
- `SimpleGraph.degree` — vertex degree (needs `Fintype (G.neighborSet v)`)
- `SimpleGraph.minDegree`, `SimpleGraph.maxDegree`
- `card_edgeFinset_le_card_choose_two` — |E| ≤ (n choose 2)

### Degree-sum / handshaking (`DegreeSum.lean`)
- `sum_degrees_eq_twice_card_edges`
- `even_card_odd_degree_vertices`

### Matchings / Hall (`Hall.lean`)
- Hall's marriage theorem in graph form
- `exists_isMatching_of_forall_ncard_le`
- `exists_isPerfectMatching_of_forall_ncard_le`

## Typeclass Assumptions

Most results require some combination of:
- `[Fintype V]` — finite vertex set
- `[DecidableEq V]` — decidable vertex equality
- `[DecidableRel G.Adj]` — decidable adjacency

Our atlas definitions use all three (see `lean/GraphAtlas/Defs.lean`).

Locally finite results only need `Fintype (G.neighborSet v)` per vertex.

## Naming Conventions

Mathlib follows consistent patterns:
- `Type.property_operation` — e.g., `IsAcyclic.isBipartite`
- `SimpleGraph.IsXxx` for property predicates
- `SimpleGraph.Xxx` for structures/types
- Negation: usually proved via contradiction
- `_iff_` for biconditionals

## Searching Mathlib

Priority order:
1. `lean_leanfinder` (semantic, >30% better, can paste goal states)
2. `lean_loogle` (type signature patterns)
3. `lean_local_search` (unlimited, grep-based)
4. Bash fallback: `search_mathlib.sh`

## References

- [Mathlib4 docs index](https://leanprover-community.github.io/mathlib4_docs/)
- [SimpleGraph.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Basic.html)
- [SimpleGraph.Finite](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Combinatorics/SimpleGraph/Finite.html)
- [OddCycleTheorem issue](https://github.com/leanprover-community/mathlib4/issues/33255)
