import TotalColoring.MatchingLowerBound

/-!
# A complement matching in the high-degree regime

This module specializes the minimum-degree matching bound to the complement of
a finite graph `G`.  In the regime `|V| ≤ 2 * G.maxDegree`, put
`k = |V| - (G.maxDegree + 1)`.  The complement degree formula shows that every
vertex of `Gᶜ` has degree at least `k`, and the high-degree hypothesis gives
`2 * k ≤ |V|`.  The general matching lower bound therefore supplies a matching
in `Gᶜ` with at least `k` edges.

This is only the complement-matching existence layer.  It neither trims the
matching to an exact edge count nor constructs a pair/singleton witness.
-/

namespace TotalColoring.MatchingLowerBound

universe u

variable {V : Type u}

/-- In the high-degree regime, every vertex in the complement has degree at
least `|V| - (G.maxDegree + 1)`. -/
theorem card_sub_maxDegree_add_one_le_degree_compl [Fintype V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Fintype.card V - (G.maxDegree + 1) ≤ Gᶜ.degree v := by
  classical
  rw [SimpleGraph.degree_compl]
  have hv := G.degree_le_maxDegree v
  omega

/-- The target matching size is at most half the order whenever
`|V| ≤ 2 * G.maxDegree`. -/
theorem twice_card_sub_maxDegree_add_one_le_card [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    2 * (Fintype.card V - (G.maxDegree + 1)) ≤ Fintype.card V := by
  omega

/-- A finite nonempty graph in the high-degree regime has a matching in its
complement with at least `|V| - (G.maxDegree + 1)` edges. -/
theorem exists_complement_matchingGraph_edgeFinset_card_ge [Fintype V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ M : SimpleGraph V, ∃ _ : DecidableRel M.Adj,
      M ≤ Gᶜ ∧ IsMatchingGraph M ∧
        Fintype.card V - (G.maxDegree + 1) ≤ M.edgeFinset.card := by
  classical
  exact exists_matchingGraph_edgeFinset_card_ge
    (Gᶜ) (Fintype.card V - (G.maxDegree + 1))
    (card_sub_maxDegree_add_one_le_degree_compl G)
    (twice_card_sub_maxDegree_add_one_le_card G hdense)

end TotalColoring.MatchingLowerBound
