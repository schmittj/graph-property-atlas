/-
  Property: Hamiltonian

  A graph is Hamiltonian if it contains a Hamiltonian cycle, i.e., a cycle
  visiting every vertex exactly once.
-/

import Mathlib.Combinatorics.SimpleGraph.Hamiltonian

namespace GraphAtlas

/-- A graph is Hamiltonian if it contains a Hamiltonian cycle. -/
abbrev IsHamiltonian {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) : Prop :=
  SimpleGraph.IsHamiltonian G

end GraphAtlas
