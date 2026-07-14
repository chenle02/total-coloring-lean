import Mathlib.Combinatorics.SimpleGraph.LineGraph

/-!
# Graph primitives for total coloring

The project reuses mathlib's `SimpleGraph`, edge subtypes, and line graph. This
module adds the small incidence and decidability interface needed by the
executable certificate checkers.
-/

namespace TotalColoring

universe u

/-- A vertex is incident with an edge when it belongs to the edge's unordered
endpoint pair. -/
abbrev Incident {V : Type u} {G : SimpleGraph V} (v : V) (e : G.edgeSet) : Prop :=
  v ∈ (e : Sym2 V)

/-- Computable line-graph adjacency for a finite decidable vertex type.

Mathlib's definition of `SimpleGraph.lineGraph` has no global decidability
instance in the pinned release. The equivalent finite existential formulation
supplies exactly the local instance needed by the checkers. -/
@[reducible]
def lineGraphDecidableAdj {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : DecidableRel G.lineGraph.Adj := fun e f ↦
  decidable_of_iff
    (e ≠ f ∧ ∃ v : V, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V))
    (@SimpleGraph.lineGraph_adj_iff_exists V G e f).symm

end TotalColoring
