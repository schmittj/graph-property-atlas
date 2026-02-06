# Graph Property Atlas — Design Specification

**Version:** 0.3 (draft)
**Date:** 2026-02-05

## 1. Vision

Given a finite set of Boolean properties of simple graphs, one can ask which combinations of properties being satisfied or not can occur simultaneously. The **Graph Property Atlas** is a collaborative, machine-verified repository that aims to classify every such assignment as either:

- **Realized**: witnessed by an explicit example graph, or
- **Impossible**: ruled out by a Lean 4 proof of a contradiction, or
- **Open**: status unknown.

Each property comes with three aligned specifications: a LaTeX description, a SageMath implementation, and a Lean 4 definition. The repository is designed so that CI can verify correctness of all data, and merge decisions for contributions (new witnesses, new proofs) can be almost fully automated.

## 2. Core Concepts

### 2.1 Properties

Let $\mathcal{P}$ denote the finite set of properties tracked by the repository. A **property** $P \in \mathcal{P}$ is a Boolean predicate on finite simple graphs (undirected, no multi-edges, no self-loops). Each property has a unique short identifier (snake_case, e.g. `vertex_transitive`) and is defined by three artifacts that must be kept in mutual agreement:

- `description.tex` — human-readable LaTeX definition, precise enough to be unambiguous.
- `check.sage` — SageMath function `check(G, **certificates) -> bool`.
- A Lean 4 definition in `lean/GraphAtlas/Properties/<PropertyName>.lean`.

**Naming convention**: Property IDs are strictly lowercase snake_case (e.g., `vertex_transitive`, `triangle_free`). This ensures no collision with the `N` prefix used for negated properties in contradiction directory names.

Precision matters. For example, the property `eulerian` is defined as: *there exists an Euler circuit, i.e., a closed walk of length $\geq 0$ traversing each edge exactly once.* Under this definition, a graph of isolated vertices is Eulerian (the empty walk is a circuit of length 0), but a disconnected graph with edges is not.

#### Property Test Suites

Each property is strongly encouraged (though not strictly required) to include a test suite of example graphs with known ground-truth values. These serve to:

- Validate alignment between LaTeX definition, Sage implementation, and Lean formalization.
- Catch edge cases and corner cases.
- Provide documentation by example.

A good test suite includes:
- At least one graph where the property is TRUE.
- At least one graph where the property is FALSE.
- Edge cases that stress-test the definition (e.g., for `eulerian`: the disjoint union of two triangles → FALSE; a single vertex → TRUE).

Test cases live in `properties/<id>/tests/` as YAML files with graph data and expected Boolean value. Ideally, each test case has a corresponding Lean proof verifying the expected value.

### 2.2 Cells

A **cell** is a function $\alpha : \mathcal{P} \to \{T, F\}$ assigning a truth value to every property. The set of all cells is $\{T, F\}^{\mathcal{P}}$, which has $2^{|\mathcal{P}|}$ elements.

Cells are represented as dictionaries mapping property IDs to Boolean values:

```
{connected: T, bipartite: F, planar: T, regular: F, ...}
```

There is no canonical ordering on $\mathcal{P}$. All data structures use dictionaries keyed by property ID, not positional encodings.

### 2.3 Contradictions

A **contradiction** is a pair $(S, a)$ where $S \subseteq \mathcal{P}$ and $a : S \to \{T, F\}$, such that no graph with $\geq$ `MIN_VERT` vertices simultaneously satisfies all the conditions prescribed by $a$.

A contradiction is **minimal** if removing any single condition (i.e., restricting to any proper subset $S' \subsetneq S$) yields a satisfiable partial assignment. Minimal contradictions are the atoms of impossibility: a cell $\alpha$ is impossible if and only if it extends some minimal contradiction.

In practice, contributors may submit contradictions whose minimality has not yet been established. Minimality is a desirable property that can be verified or refuted later (by providing witness graphs for each sub-assignment, or by proving a stronger contradiction with fewer conditions). The contradiction registry tracks minimality status explicitly.

Special case: a contradiction involving just two conditions, e.g., $(\{P_i, P_j\},\; P_i \mapsto T,\, P_j \mapsto F)$, is equivalent to the implication $P_i \Rightarrow P_j$ (for graphs on $\geq$ `MIN_VERT` vertices). These form an **implication graph** among properties.

### 2.4 Global Parameters

| Parameter | Value | Description |
|-----------|-------|-------------|
| `MIN_VERT` | 3 | Minimum number of vertices for a graph to count as a witness. |
| `SAGE_VERSION` | (pinned) | The exact SageMath version used in CI, recorded in `config.yaml`. |

Rationale for `MIN_VERT`: excludes degenerate cases where $K_1$, $K_2$ vacuously satisfy many properties. This is a repository-wide constant referenced in all Lean theorem statements. It may be increased in a future major version.

Rationale for `SAGE_VERSION`: Graph property algorithms can behave differently across Sage versions. Pinning ensures reproducibility. Version updates are intentional migrations.

## 3. Initial Property List

| ID | Name | Precise definition summary | Key interactions |
|----|------|---------------------------|-----------------|
| `connected` | Connected | The graph has exactly one connected component. | Fundamental; interacts with Eulerian, forest. |
| `bipartite` | Bipartite | The vertex set admits a 2-coloring with no monochromatic edges. | ⇒ triangle_free, perfect. |
| `planar` | Planar | Admits a crossing-free embedding in the plane. | Implied by forest. |
| `regular` | Regular | All vertices have the same degree. | Implied by vertex_transitive. |
| `eulerian` | Eulerian | Admits an Euler circuit (closed walk of length ≥ 0 traversing each edge exactly once). Isolated vertices are Eulerian; disconnected graphs with edges are not. | Even-degree condition. Conflicts with forest+connected. |
| `hamiltonian` | Hamiltonian | Admits a Hamilton cycle (cycle visiting every vertex exactly once). | Hard to verify; certificate: Hamilton cycle. |
| `forest` | Forest (acyclic) | Contains no cycles. | ⇒ bipartite, planar, triangle_free, chordal, perfect. |
| `triangle_free` | Triangle-free | Contains no $K_3$ subgraph. | Implied by bipartite and forest. |
| `perfect` | Perfect | $\chi(H) = \omega(H)$ for every induced subgraph $H$. | Implied by bipartite, chordal. Deep theory (SPGT). |
| `vertex_transitive` | Vertex-transitive | The automorphism group acts transitively on vertices. | ⇒ regular. |
| `chordal` | Chordal | Every cycle of length ≥ 4 has a chord. | ⇒ perfect. Implied by forest. |
| `cayley` | Cayley graph | Isomorphic to a Cayley graph $\mathrm{Cay}(\Gamma, S)$ for some finite group $\Gamma$ and generating set $S$ (ignoring any resulting multi-edges or loops). | ⇒ vertex_transitive ⇒ regular. |

### Known implications (size-2 contradictions)

- `forest` ⇒ `bipartite`, `planar`, `triangle_free`, `chordal`
- `chordal` ⇒ `perfect`
- `bipartite` ⇒ `triangle_free`, `perfect`
- `cayley` ⇒ `vertex_transitive` ⇒ `regular`

### Known larger contradictions (examples)

- {`forest`=T, `hamiltonian`=T}: a forest has no cycles, so no Hamiltonian cycle ($\geq 3$ vertices).
- {`forest`=T, `connected`=T, `eulerian`=T}: a tree on $\geq 3$ vertices has leaves (degree 1), violating even-degree.
- {`forest`=T, `connected`=T, `regular`=T}: same reasoning.

### Further property ideas (not in v1)

- `self_complementary` — isomorphic to its complement. Arithmetic constraint $|V| \equiv 0, 1 \pmod{4}$.
- `claw_free` — no induced $K_{1,3}$.
- `edge_transitive` — automorphism group acts transitively on edges.
- `has_perfect_matching` — admits a perfect matching.

## 4. Repository Structure

```
graph-property-atlas/
├── README.md
├── LICENSE
├── config.yaml                         # MIN_VERT, SAGE_VERSION, other globals
│
├── properties/
│   ├── registry.yaml                   # set of properties (unordered)
│   ├── connected/
│   │   ├── description.tex
│   │   ├── check.sage
│   │   └── tests/                      # optional test suite
│   │       ├── path_3.yaml             # example: TRUE case
│   │       ├── two_triangles.yaml      # example: FALSE case
│   │       └── ...
│   ├── bipartite/
│   │   ├── description.tex
│   │   ├── check.sage
│   │   └── tests/
│   └── ... (one directory per property)
│
├── witnesses/
│   ├── README.md                       # explains YAML schema
│   ├── petersen.yaml                   # freeform filenames
│   ├── cycle_5.yaml
│   └── ...
│
├── gallery/
│   ├── README.md                       # editorial guidelines
│   ├── petersen_kneser.yaml
│   └── ... (extra examples, looser merge policy)
│
├── contradictions/
│   ├── registry.yaml                   # lists all contradictions
│   ├── forest__hamiltonian/
│   │   ├── latex_proof.tex             # informal LaTeX proof
│   │   ├── lean_proof.lean             # formal Lean 4 proof
│   │   └── README.md                   # optional discussion
│   ├── cayley__Nregular/
│   │   ├── latex_proof.tex
│   │   ├── lean_proof.lean
│   │   └── README.md
│   └── ...
│
├── lean/
│   ├── lakefile.lean                   # Lean project config (used by CI assembly)
│   ├── lean-toolchain
│   └── GraphAtlas/
│       ├── Defs.lean                   # SimpleGraph, MIN_VERT, common infrastructure
│       ├── Properties/
│       │   ├── Connected.lean
│       │   ├── Bipartite.lean
│       │   ├── Cayley.lean
│       │   └── ...
│       └── Lemmas/                     # shared lemmas (implications, utilities)
│           ├── ForestImpliesBipartite.lean
│           ├── CayleyImpliesVertexTransitive.lean
│           └── ...
│
├── scripts/
│   ├── assemble_lean.py                # assemble Lean project for CI
│   ├── verify_witnesses.sage           # verify all witness files
│   ├── verify_gallery.sage             # verify all gallery files
│   ├── verify_property_tests.sage      # verify property test suites
│   ├── compute_status.py               # derive status from witnesses + contradictions
│   ├── coverage_report.py              # print statistics
│   ├── validate_pr.py                  # check that a PR adds new information
│   ├── check_minimality.py             # check/update minimality status of contradictions
│   ├── query.py                        # CLI tool for querying the atlas
│   └── check_consistency.py            # verify no cell is both realized and impossible
│
├── docs/
│   ├── CONTRIBUTING.md
│   ├── PROPERTY_TEMPLATE.md            # how to propose a new property
│   ├── CERTIFICATE_SCHEMA.md           # certificate data formats
│   └── architecture.md
│
└── .github/
    └── workflows/
        ├── verify.yaml                 # CI: Sage checks + Lean build
        ├── build_cache.yaml            # CI: build status cache (artifact, not committed)
        └── validate_pr.yaml            # CI: ensure PR adds new info
```

Note: Cache files (`property_vectors.json`, `status.json`) are **not committed** to the repository. They are built by CI and uploaded as artifacts. This avoids merge conflicts and keeps the repository focused on source-of-truth data.

## 5. Data Formats

### 5.1 Property Registry (`properties/registry.yaml`)

The registry is an **unordered** set of property metadata. There are no index fields or positional encodings.

```yaml
properties:
  - id: connected
    lean_name: GraphAtlas.IsConnected
    display_name: Connected
  - id: bipartite
    lean_name: GraphAtlas.IsBipartite
    display_name: Bipartite
  - id: cayley
    lean_name: GraphAtlas.IsCayley
    display_name: Cayley graph
  # ...
```

### 5.2 Property Checker (`properties/<id>/check.sage`)

Each checker file must define a module-level `CERTIFICATE_MODE` constant and a `check` function.

#### Certificate Modes

| Mode | Meaning | Example properties |
|------|---------|-------------------|
| `"generic"` | Standard algorithm, no certificates needed. | `connected`, `forest` |
| `"both"` | Has both generic and certified paths. `check(G)` gives generic result; `check(G, **certs)` validates certificates. | `bipartite`, `hamiltonian` |
| `"certified"` | No practical generic algorithm. Witnesses must provide certificates. | `cayley`, `vertex_transitive` |

#### API

```python
# Required: certificate mode declaration
CERTIFICATE_MODE = "generic"  # or "both" or "certified"

def check(G, **kwargs):
    """
    Check whether the SageMath Graph G satisfies this property.

    Parameters
    ----------
    G : sage.graphs.graph.Graph
        A simple graph.
    **kwargs : dict
        Certificate/counter-certificate arguments (from witness YAML).
        When no certs are provided, falls back to generic algorithm
        (for "generic" and "both" modes).

    Returns
    -------
    bool
    """
```

Note: `check(G)` without kwargs always gives the generic result. This means cross-checking needs no separate function — just call `check` with and without certs and compare.

#### Verification modes

- `sage verify_witnesses.sage` — calls `check(G, **certs)`. Fast: certified properties use certificate validation only.
- `sage verify_witnesses.sage --cross-check` — for `"both"`-mode properties, additionally calls `check(G)` (no certs, i.e. generic path) and verifies agreement. Catches cert/algorithm misalignment.

### 5.3 Certificates and Counter-Certificates

Certificates provide witness data that makes verification faster and more robust. **Certificates are pure data, not executable code.** This is critical for security: CI must never execute arbitrary code from untrusted PRs.

#### Certificate Types (for TRUE properties)

| Property | Certificate key | Data format |
|----------|-----------------|-------------|
| `hamiltonian` | `hamiltonian_cycle` | List of vertex labels forming the cycle: `[0, 3, 1, 4, 2]` |
| `vertex_transitive` | `vertex_transitive_generators` | List of permutations in cycle notation: `["(0,1,2,3,4)", "(0,2)(1,4)"]` |
| `cayley` | `cayley_group_id` | GAP SmallGroup identifier: `[order, index]`, e.g., `[12, 3]` for $A_4$ |
| `cayley` | `cayley_generators` | List of group element indices: `[1, 2]` (indices into the SmallGroup) |
| `planar` | `planar_embedding` | Combinatorial embedding as adjacency dict with clockwise ordering |
| `bipartite` | `bipartite_coloring` | Dict mapping vertices to 0 or 1: `{0: 0, 1: 1, 2: 0, ...}` |

#### Counter-Certificate Types (for FALSE properties)

Counter-certificates prove a property is FALSE, enabling fast verification of negative claims.

| Property | Counter-certificate key | Data format |
|----------|------------------------|-------------|
| `bipartite` | `bipartite_odd_cycle` | List of vertices forming an odd cycle: `[0, 1, 2]` |
| `triangle_free` | `triangle_free_triangle` | List of 3 vertices forming a triangle: `[0, 1, 2]` |
| `chordal` | `chordal_induced_cycle` | List of ≥4 vertices forming a chordless induced cycle |
| `planar` | `planar_kuratowski` | Kuratowski subdivision witness (format TBD) |
| `forest` | `forest_cycle` | List of vertices forming a cycle |
| `connected` | `connected_components` | List of two vertex sets in different components |

#### Rules

- A witness file must not provide both a certificate and counter-certificate for the same property.
- If a certificate is provided for a TRUE property, the checker verifies it. Cross-checking against the generic algorithm is available via `--cross-check` (see below).
- If a counter-certificate is provided for a FALSE property, the checker verifies it. Cross-checking is likewise optional.
- If neither is provided, the checker runs the general algorithm.
- Properties with O(V+E) algorithms (e.g. `connected`, `forest`) do not need certificates — the checker simply runs the standard algorithm. Certificates are most valuable for properties that are expensive to verify from scratch (e.g. `vertex_transitive`, `cayley`, `hamiltonian`).
- **Cross-checking**: For `"both"`-mode properties, `verify_witnesses.sage --cross-check` additionally calls `check(G)` (no certs = generic path) and verifies agreement with the certified result. This catches cert/algorithm misalignment but is optional since it can be slow for expensive properties. CI should run with `--cross-check` for `"both"`-mode properties.

### 5.4 Witness Files (`witnesses/<name>.yaml`)

Filenames are freeform (descriptive snake_case). Each file contains the graph data, its full property vector, optional certificates/counter-certificates, and metadata.

```yaml
description: "Petersen graph"

graph:
  format: graph6               # graph6, sparse6, or edge_list
  data: "IsP@OKWHo"

properties:
  connected: true
  bipartite: false
  planar: false
  regular: true
  eulerian: false
  hamiltonian: false
  forest: false
  triangle_free: true
  perfect: false
  vertex_transitive: true
  chordal: false
  cayley: false

certificates:
  vertex_transitive_generators:
    - "(1,2,3,4,5)(6,7,8,9,10)"
    - "(1,6)(2,7)(3,8)(4,9)(5,10)"

counter_certificates:
  bipartite_odd_cycle: [0, 1, 2, 5, 4]
  chordal_induced_cycle: [0, 2, 6, 1, 3]

provenance:
  source: "Classical; see e.g. Diestel, Graph Theory, 5th ed."
  url: "https://houseofgraphs.org/graphs/660"
  found_by: "manual"
```

When `format` is `edge_list`, the `data` field is a list of edges:

```yaml
graph:
  format: edge_list
  vertices: 5
  data: [[0,1], [1,2], [2,3], [3,4], [4,0]]
```

Requirements enforced by CI:
- `graph.format` must be `graph6`, `sparse6`, or `edge_list`.
- The graph must have $\geq$ `MIN_VERT` vertices.
- The `properties` dictionary must list every property in $\mathcal{P}$, no more and no less.
- The actual property vector (computed by Sage checkers) must match the declared `properties`.
- Certificates/counter-certificates, if provided, must be valid.
- **CI consistency check**: the cell must not be marked impossible by any known contradiction.

### 5.5 Smallest Known Witness Tracking

For each realized cell, the atlas tracks which witness has the smallest graph (by vertex count, with edge count as tiebreaker).

- Each witness file is tagged with `order` (vertex count) and `size` (edge count) in the computed cache.
- The **canonical witness** for a cell is the smallest one.
- If a new witness PR provides a strictly smaller graph for an already-realized cell:
  - The PR is accepted (improves the atlas).
  - CI automatically moves the previous canonical witness to the gallery (if it's notable) or archives it.
  - The new witness becomes canonical.

This enables a "beat the record" game for contributors and ensures the atlas contains minimal examples.

### 5.6 Gallery Files (`gallery/<name>.yaml`)

Same schema as witness files. Multiple files per cell are allowed. 

Editorial bar for merging: the graph should be notable. Notability is indicated by tags:

```yaml
tags:
  - named           # a named graph (Petersen, Heawood, etc.)
  - extremal        # extremal for some property
  - smallest        # was previously the smallest witness (demoted by a smaller one)
  - counterexample  # historically significant counterexample
  - historical      # historically important
```

Graphs demoted from `witnesses/` by smaller examples automatically receive the `smallest` tag and a note about when they were demoted.

### 5.7 Contradiction Registry (`contradictions/registry.yaml`)

```yaml
contradictions:
  - id: forest__hamiltonian
    assignments:
      forest: true
      hamiltonian: true
    minimal: unknown    # unknown | yes | no
    notes: "Elementary: forests have no cycles."
    refs:
      - "Any graph theory textbook"

  - id: connected__eulerian__forest
    assignments:
      connected: true
      eulerian: true
      forest: true
    minimal: yes
    notes: "Trees on ≥3 vertices have leaves (degree 1)."

  - id: cayley__Nregular
    assignments:
      cayley: true
      regular: false
    minimal: yes
    notes: "Cayley graphs are vertex-transitive, hence regular."
    refs:
      - "Godsil & Royle, Algebraic Graph Theory, Lemma 3.1"
```

Fields:
- `id`: Canonical directory name (sorted property IDs, `N` prefix for false).
- `assignments`: The partial assignment defining the contradiction.
- `minimal`: Minimality status — `unknown` (default), `yes` (verified), or `no` (a smaller contradiction exists).
- `notes`: Brief informal description (optional).
- `refs`: References to literature (optional).

### 5.8 Contradiction Directory Structure

Each contradiction gets a directory named by sorting the property IDs alphabetically, using `N` prefix for false assignments, joined by double underscores:

- {forest=T, hamiltonian=T} → `forest__hamiltonian`
- {cayley=T, regular=F} → `cayley__Nregular`
- {connected=T, eulerian=T, forest=T} → `connected__eulerian__forest`

Since property IDs are lowercase snake_case, there is no ambiguity with the uppercase `N` prefix.

Each directory is self-contained:

```
contradictions/forest__hamiltonian/
├── latex_proof.tex       # Informal LaTeX proof (required)
├── lean_proof.lean       # Formal Lean 4 proof (required)
└── README.md             # Optional: discussion, references, context
```

The `latex_proof.tex` provides an informal mathematical argument readable by humans and acts as a blueprint for the formal Lean proof.

The `lean_proof.lean` contains the formal proof. It may import property definitions and shared lemmas from `lean/GraphAtlas/Lemmas/`.

### 5.9 Lean Proof Format

Every contradiction Lean file must contain a theorem of the following standard form:

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

For contradictions involving negated properties:

```lean
theorem cayley_not_regular_contradiction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≥ MIN_VERT)
    (h_cayley : IsCayley G)
    (h_not_regular : ¬IsRegular G) :
    False := by
  ...
```

The theorem must:
- Universally quantify over a `SimpleGraph V` with `Fintype.card V ≥ MIN_VERT`.
- Assume exactly the property predicates listed in the contradiction's `assignments` (positive for T, negated for F).
- Conclude `False`.
- Be named according to the canonical convention: directory name with `__` → `_`, `N` → `not_`, suffixed with `_contradiction`.

### 5.10 Shared Lean Lemmas

The folder `lean/GraphAtlas/Lemmas/` contains shared lemmas that multiple contradiction proofs can import. This avoids duplication and ensures consistency.

Common shared lemmas include:
- `ForestImpliesBipartite.lean`: forests are bipartite
- `CayleyImpliesVertexTransitive.lean`: Cayley graphs are vertex-transitive
- `VertexTransitiveImpliesRegular.lean`: vertex-transitive graphs are regular

Contradiction proofs should import from `Lemmas/` rather than re-proving these facts.

### 5.11 Lean Build Assembly

CI assembles and builds the Lean project in-place:

1. Copying each `lean_proof.lean` from contradiction directories into `lean/GraphAtlas/Contradictions/` (gitignored).
2. Regenerating `lean/GraphAtlas.lean` to import all modules (saved/restored after build).
3. Running `lake build`.
4. Optionally checking for `sorry` and `axiom` declarations (`--check`).

Contributors write self-contained `lean_proof.lean` files that import property definitions and shared lemmas.

## 6. Cache and Status Derivation

### 6.1 CI-Built Caches

Cache files are **not committed** to the repository. They are built by CI on every push to main and uploaded as artifacts. This avoids merge conflicts.

The CI workflow `build_cache.yaml`:
1. Runs `scripts/compute_status.py` which:
   - Parses all witnesses and computes their property vectors.
   - Parses all contradictions.
   - Computes the set of impossible cells (upward closure of contradictions).
   - Computes the set of realized cells.
   - Runs consistency check: **no cell may be both realized and impossible**.
2. Outputs `property_vectors.json` and `status.json` as CI artifacts.
3. Optionally uploads to a CDN or GitHub Pages for the website.

### 6.2 Consistency Invariant

**Critical invariant**: A cell cannot be both realized (has a witness) and impossible (extends a contradiction).

If this invariant is violated, it indicates a bug:
- Misalignment between Sage property checker and Lean property definition.
- Bug in a Sage checker.
- Incorrect assignments in a contradiction.

CI fails with a detailed diagnostic showing the witness(es) and contradiction(s) involved.

### 6.3 Status JSON Schema

```json
{
  "sage_version": "10.3",
  "generated_at": "2026-02-05T12:34:56Z",
  "property_set": ["connected", "bipartite", "planar", ...],
  "total_cells": 4096,
  "realized": 847,
  "impossible": 2901,
  "open": 348,
  "canonical_witnesses": {
    "{connected:true,bipartite:false,...}": {
      "file": "petersen.yaml",
      "order": 10,
      "size": 15
    }
  },
  "impossible_cells_by_contradiction": {
    "forest__hamiltonian": 512,
    "cayley__Nregular": 128
  }
}
```

## 7. CI / Merge Policy

### 7.1 Automated Checks (all PRs)

1. **Lean build**: Assemble the Lean project and run `lake build`.
2. **Sage verification**: For every new/modified witness or gallery file, verify property vectors and certificates.
3. **Property test suites**: Run `verify_property_tests.sage` for any modified properties.
4. **Consistency check**: Run `check_consistency.py` — fail if any cell is both realized and impossible.
5. **Schema validation**: All YAML files conform to their schemas.

### 7.2 Merge Criteria by PR Type

| PR type | Automated merge? | Human review? |
|---------|-----------------|---------------|
| New witness for an open cell | After CI passes | Light review initially |
| New witness improving (smaller) an existing cell | After CI passes | Light review |
| New Lean contradiction proof | After CI passes | Light review initially |
| New gallery example (notable) | CI passes | Review for notability |
| New property | CI passes | Full review: LaTeX ↔ Sage ↔ Lean alignment |
| Bug fix / refactor | CI passes | Standard code review |

Note: "automated merge" is aspirational for v1. Initially, all PRs require manual approval, but CI passing should be sufficient evidence for approval.

### 7.3 Strict Additive Policy

- A witness PR must either:
  - Cover a cell that is currently **open** (not realized, not impossible), or
  - Provide a **smaller** graph for an already-realized cell.
- A contradiction PR must render at least one currently **open** cell impossible.
- Gallery PRs are exempt from this rule but have notability standards.

### 7.4 Contradictions and Minimality

Minimality is desirable but not required for merge. A contradiction PR is accepted if:

1. The `lean_proof.lean` compiles.
2. The `latex_proof.tex` is present.
3. It kills at least one open cell.

The `minimal` field starts as `unknown`. It can be upgraded to `yes` by running `scripts/check_minimality.py`, which verifies that all proper sub-assignments have witnesses.

## 8. Adding a New Property

When a new property $P_{\mathrm{new}}$ is added to $\mathcal{P}$:

1. A new directory `properties/<id>/` is created with `description.tex`, `check.sage`, and ideally a `tests/` folder.
2. A new Lean file `lean/GraphAtlas/Properties/<PropertyName>.lean` is added.
3. The property is added to `properties/registry.yaml`.
4. A migration script:
   - Re-evaluates the new property on every existing witness and gallery graph.
   - Adds the new key to every `properties` dictionary in every YAML file.
5. New contradictions involving the new property can now be contributed.

Since cells are dictionaries (not positional strings), this migration only adds a key. This is much less disruptive than a positional encoding.

This is still a significant change (doubles the cell space) and should not be done too frequently.

## 9. Scripts

### `scripts/assemble_lean.py`

Assemble and build the Lean project (in-place, with save/restore of tracked files):
1. Copy all `lean_proof.lean` files from contradiction directories into `lean/GraphAtlas/Contradictions/` (gitignored).
2. Regenerate `lean/GraphAtlas.lean` importing all modules (original is saved and restored after build).
3. Run `lake build` and report results.
4. With `--check`: also scan for `sorry` and `axiom` declarations in project source files.

### `scripts/verify_witnesses.sage`

For each file in `witnesses/`:
- Parse YAML, decode graph.
- Check `G.order() >= MIN_VERT`.
- For each property, call `check(G, **certificates, **counter_certificates)`.
- Verify computed vector matches declared `properties`.

### `scripts/verify_property_tests.sage`

For each property with a `tests/` folder:
- Load each test case.
- Verify the Sage checker returns the expected value.

### `scripts/compute_status.py`

Build the status cache:
1. Parse all witnesses and gallery files.
2. Parse all contradictions.
3. Compute realized/impossible/open for each cell.
4. Output `property_vectors.json` and `status.json`.

### `scripts/check_consistency.py`

Verify the critical invariant: no cell is both realized and impossible.
- If violated, output detailed diagnostic and exit with error.

### `scripts/check_minimality.py`

For each contradiction with `minimal: unknown`:
- For each proper sub-assignment, check if a compatible witness exists.
- If all sub-assignments have witnesses, update `minimal: yes`.
- Report contradictions that are not yet verified minimal.

### `scripts/query.py`

CLI tool for querying the atlas:

```bash
# Check status of a partial assignment
./scripts/query.py --assignment '{"forest": true, "connected": true}'
# Output: possible (X witnesses compatible), or impossible (extends contradiction Y)

# Find open cells
./scripts/query.py --open --limit 10

# Find witnesses for a cell
./scripts/query.py --cell '{"connected": true, "bipartite": false, ...}'

# Find contradictions killing a cell
./scripts/query.py --why-impossible '{"forest": true, "hamiltonian": true, ...}'
```

### `scripts/coverage_report.py`

Print summary statistics: total cells, realized, impossible, open, fill percentage, smallest witnesses per cell, etc.

### `scripts/validate_pr.py`

Check that a PR strictly adds new information relative to current status.

## 10. Future Directions

These are out of scope for v1 but inform design decisions:

- **Website**: interactive explorer of the property cube. Select property assignments via T/F/any toggles, see matching examples, browse contradictions, view statistics.
- **Automated search**: CI job that enumerates small graphs (via `nauty`/`geng`), evaluates all properties, and auto-generates witness PRs for newly discovered cells.
- **Implication graph visualization**: automatically extract and visualize the implication graph from size-2 contradictions.
- **Vertex-count stratification**: track minimum vertex count required for each cell.
- **Parameterized properties**: extend from Boolean to parameterized properties (chromatic number, etc.).
- **Bitmask internal representation**: for scaling past ~20 properties, represent cells as bitmasks internally while keeping dict UX.
- **Property verification modes**: classify properties as `fast`, `certificate_required`, or `expensive` to control CI behavior.

## Appendix A: Example Walkthrough

Suppose we want to add the Petersen graph as a witness.

1. Create `witnesses/petersen.yaml`:
   ```yaml
   description: "Petersen graph"

   graph:
     format: graph6
     data: "IsP@OKWHo"

   properties:
     connected: true
     bipartite: false
     planar: false
     regular: true
     eulerian: false
     hamiltonian: false
     forest: false
     triangle_free: true
     perfect: false
     vertex_transitive: true
     chordal: false
     cayley: false

   certificates:
     vertex_transitive_generators:
       - "(1,2,3,4,5)(6,7,8,9,10)"
       - "(1,6)(2,7)(3,8)(4,9)(5,10)"

   counter_certificates:
     bipartite_odd_cycle: [0, 1, 2, 5, 4]

   provenance:
     source: "Classical named graph"
     url: "https://houseofgraphs.org/graphs/660"
     found_by: "manual"
   ```
2. Run `scripts/verify_witnesses.sage` — confirms all 12 properties match.
3. CI runs `scripts/check_consistency.py` — confirms no impossible/realized conflict.
4. Submit PR. CI passes. Approved and merged.

## Appendix B: Contradiction Minimality Workflow

To verify that a contradiction $(S, a)$ is minimal:

For each element $P_i \in S$, check whether the restricted assignment $(S \setminus \{P_i\},\; a|_{S \setminus \{P_i\}})$ is satisfiable.

`scripts/check_minimality.py` automates this:
1. For each contradiction with `minimal: unknown`:
2. For each property in the assignment, form the sub-assignment.
3. Search existing witnesses for compatibility.
4. If all sub-assignments have compatible witnesses → `minimal: yes`.
5. If any sub-assignment has no witness → remains `unknown` (contributor opportunity!).

Output: report of minimality status and "wanted" witnesses for proving minimality.

## Appendix C: Naming Conventions

### Property IDs

Lowercase snake_case only: `vertex_transitive`, `triangle_free`, `cayley`.

This ensures the `N` prefix (uppercase) used for negated properties in contradiction directory names is unambiguous.

### Contradiction directories

Formed by:
1. Listing each condition: bare property ID for true, `N`-prefixed for false.
2. Sorting alphabetically.
3. Joining with `__`.

Examples:
- {forest=T, hamiltonian=T} → `forest__hamiltonian`
- {cayley=T, regular=F} → `cayley__Nregular`
- {connected=T, eulerian=T, forest=T} → `connected__eulerian__forest`

### Lean theorem names

Canonically derived: replace `__` with `_`, replace `N` with `not_`, append `_contradiction`:
- `forest__hamiltonian` → `forest_hamiltonian_contradiction`
- `cayley__Nregular` → `cayley_not_regular_contradiction`

### Witness and gallery filenames

Freeform descriptive snake_case: `petersen.yaml`, `cycle_7.yaml`, `paley_13.yaml`.

## Appendix D: Certificate Data Formats

This appendix provides detailed schemas for certificate and counter-certificate data.

### Permutation Groups (for `vertex_transitive`)

Generators as cycle notation strings:
```yaml
vertex_transitive_generators:
  - "(0,1,2,3,4)"
  - "(0,2)(1,4)"
```

The Sage checker parses these strings and constructs a `PermutationGroup`, then verifies it acts transitively on vertices.

### Cayley Graph Certificates

Use GAP SmallGroup identifiers:
```yaml
cayley_group_id: [12, 3]  # SmallGroup(12, 3) = A4
cayley_generators: [1, 2]  # indices into the group's element list
cayley_isomorphism:        # optional: explicit vertex correspondence
  0: "()"
  1: "(1,2)(3,4)"
  # ...
```

The Sage checker constructs the Cayley graph from the SmallGroup and generators, then verifies isomorphism to G.

### Odd Cycle (for non-bipartite)

List of vertices forming an odd cycle:
```yaml
bipartite_odd_cycle: [0, 1, 2, 5, 4]
```

The checker verifies these vertices form a cycle of odd length in G.

### Induced Chordless Cycle (for non-chordal)

List of ≥4 vertices:
```yaml
chordal_induced_cycle: [0, 2, 6, 1, 3]
```

The checker verifies: (1) consecutive pairs are adjacent, (2) first and last are adjacent, (3) no other pairs are adjacent (no chords).
