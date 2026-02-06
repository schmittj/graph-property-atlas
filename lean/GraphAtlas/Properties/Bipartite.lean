/-
  Property: Bipartite

  A graph is bipartite if its vertex set admits a 2-coloring with no
  monochromatic edges. Equivalently, it contains no odd cycle.
-/

import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-- A graph is bipartite if it is 2-colorable. -/
abbrev IsBipartite {V : Type*} (G : SimpleGraph V) : Prop :=
  SimpleGraph.IsBipartite G
