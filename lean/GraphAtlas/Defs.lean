/-
  GraphAtlas — Core Definitions

  This file defines the global constants and re-exports the property predicates
  used throughout the atlas. Each property predicate is a thin wrapper around
  the corresponding Mathlib definition, providing a stable interface for
  contradiction proofs.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic

/-- Minimum number of vertices for a graph to count as a witness. -/
def MIN_VERT : ℕ := 3
