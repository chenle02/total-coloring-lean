/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.MatchingLowerBound

/-!
# Comparator solution: a matching of size `k` from degree and order bounds

Same statement as `Audit/MatchingLowerBound/Challenge.lean`, from
`TotalColoring.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_ge`:
`IsMatchingGraph M` is by definition `∀ v, (M.neighborSet v).Subsingleton`.

`Fidelity.not_weaker` derives the library theorem back from the Challenge
statement, so the two statements are equivalent.
-/

namespace TotalColoringAudit.MatchingLowerBound

theorem exists_matchingGraph_edgeFinset_card_ge
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hdegree : ∀ v, k ≤ H.degree v) (horder : 2 * k ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V) (_ : DecidableRel M.Adj),
      M ≤ H ∧ (∀ v, (M.neighborSet v).Subsingleton) ∧ k ≤ M.edgeFinset.card :=
  TotalColoring.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_ge H k hdegree horder

namespace Fidelity

universe u

/-- The Challenge statement implies the library statement. -/
theorem not_weaker (h : type_of% @exists_matchingGraph_edgeFinset_card_ge.{u}) :
    type_of% @TotalColoring.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_ge.{u} := by
  intro V _ H _ k hdegree horder
  exact h H k hdegree horder

end Fidelity

end TotalColoringAudit.MatchingLowerBound
