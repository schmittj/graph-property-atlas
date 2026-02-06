/-
  Property: Regular

  A graph is regular if all vertices have the same degree, i.e.,
  there exists d such that every vertex has exactly d neighbours.
-/

import Mathlib.Combinatorics.SimpleGraph.Finite

namespace GraphAtlas

/-- A graph is regular if there exists d such that every vertex has degree d. -/
abbrev IsRegular {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  ∃ d : ℕ, G.IsRegularOfDegree d

end GraphAtlas
