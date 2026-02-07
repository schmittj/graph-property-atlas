/-
  Property: Eulerian

  A graph is Eulerian if it admits an Euler circuit: a closed walk traversing
  each edge exactly once. Graphs with no edges are Eulerian (witnessed by the
  nil walk). Disconnected graphs with edges are not.
-/

import Mathlib.Combinatorics.SimpleGraph.Trails

namespace GraphAtlas

/-- A graph is Eulerian if there exists a closed walk traversing every edge exactly once. -/
abbrev IsEulerian {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Prop :=
  ∃ v, ∃ p : G.Walk v v, p.IsEulerian

end GraphAtlas
