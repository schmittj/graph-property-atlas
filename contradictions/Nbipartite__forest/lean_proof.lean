import GraphAtlas.Defs
import GraphAtlas.Properties.Forest
import GraphAtlas.Properties.Bipartite

theorem not_bipartite_forest_contradiction
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : Fintype.card V ≥ MIN_VERT)
    (h_forest : IsForest G)
    (h_not_bipartite : ¬IsBipartite G) :
    False := by
  sorry
