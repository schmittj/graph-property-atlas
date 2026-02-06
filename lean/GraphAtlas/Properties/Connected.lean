/-
  Property: Connected

  A graph is connected if for every pair of vertices, there exists a path
  between them (and the vertex type is nonempty).
-/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-- A graph is connected if it has exactly one connected component. -/
abbrev IsConnected {V : Type*} (G : SimpleGraph V) : Prop := G.Connected
