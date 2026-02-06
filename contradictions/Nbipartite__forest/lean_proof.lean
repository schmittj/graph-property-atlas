import GraphAtlas.Defs
import GraphAtlas.Properties.Forest
import GraphAtlas.Properties.Bipartite

open GraphAtlas

theorem not_bipartite_forest_contradiction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (_hcard : Fintype.card V ≥ MIN_VERT)
    (h_forest : IsForest G)
    (h_not_bipartite : ¬IsBipartite G) :
    False :=
  h_not_bipartite h_forest.isBipartite
