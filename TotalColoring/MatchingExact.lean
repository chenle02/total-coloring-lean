import TotalColoring.MatchingLowerBound

/-!
# Exact-size matching extraction

This module separates a finite trimming step from the lower-bound argument in
`MatchingLowerBound`.  Any spanning matching graph with at least `r` edges has
a spanning matching subgraph with exactly `r` edges.  Combining that fact with
the minimum-degree lower bound produces an exact-size matching.
-/

namespace TotalColoring.MatchingLowerBound

open Finset

universe u

variable {V : Type u}

/-- A matching can be trimmed to any smaller prescribed number of edges. -/
theorem IsMatchingGraph.exists_subgraph_edgeFinset_card_eq [Fintype V]
    {M : SimpleGraph V} [DecidableRel M.Adj] (hM : IsMatchingGraph M)
    {r : ℕ} (hr : r ≤ #M.edgeFinset) :
    ∃ N : SimpleGraph V, ∃ _ : DecidableRel N.Adj,
      N ≤ M ∧ IsMatchingGraph N ∧ #N.edgeFinset = r := by
  classical
  obtain ⟨S, hSM, hScard⟩ := Finset.exists_subset_card_eq hr
  let N := M.deleteEdges (↑(M.edgeFinset \ S) : Set (Sym2 V))
  let instN : DecidableRel N.Adj := inferInstance
  letI : DecidableRel N.Adj := instN
  have hNM : N ≤ M := by
    change M.deleteEdges (↑(M.edgeFinset \ S) : Set (Sym2 V)) ≤ M
    exact SimpleGraph.deleteEdges_le _
  refine ⟨N, instN, hNM, hM.mono hNM, ?_⟩
  change #(M.deleteEdges (↑(M.edgeFinset \ S) : Set (Sym2 V))).edgeFinset = r
  rw [SimpleGraph.edgeFinset_deleteEdges,
    Finset.sdiff_sdiff_eq_self hSM, hScard]

/-- Exact-cardinality form of the minimum-degree matching bound. -/
theorem exists_matchingGraph_edgeFinset_card_eq [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (r : ℕ)
    (hdegree : ∀ v, r ≤ H.degree v) (horder : 2 * r ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, ∃ _ : DecidableRel M.Adj,
      M ≤ H ∧ IsMatchingGraph M ∧ #M.edgeFinset = r := by
  obtain ⟨M, instM, hMH, hM, hcard⟩ :=
    exists_matchingGraph_edgeFinset_card_ge H r hdegree horder
  letI : DecidableRel M.Adj := instM
  obtain ⟨N, instN, hNM, hN, hNcard⟩ :=
    hM.exists_subgraph_edgeFinset_card_eq hcard
  letI : DecidableRel N.Adj := instN
  exact ⟨N, instN, hNM.trans hMH, hN, hNcard⟩

end TotalColoring.MatchingLowerBound
