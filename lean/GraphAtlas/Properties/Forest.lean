/-
  Property: Forest (Acyclic)

  A graph is a forest if it contains no cycle. A connected forest is a tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-- A graph is a forest (acyclic) if it contains no cycle. -/
abbrev IsForest {V : Type*} (G : SimpleGraph V) : Prop := G.IsAcyclic
