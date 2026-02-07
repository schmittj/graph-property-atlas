/-
  Property: Triangle-free

  A graph is triangle-free if it contains no K_3 subgraph, i.e., no three
  vertices are pairwise adjacent.
-/

import Mathlib.Combinatorics.SimpleGraph.Clique

namespace GraphAtlas

/-- A graph is triangle-free if it has no 3-clique. -/
abbrev IsTriangleFree {V : Type*} (G : SimpleGraph V) : Prop := G.CliqueFree 3

end GraphAtlas
