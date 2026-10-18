/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib

/-!
# Comparator challenge: a matching of size `k` from degree and order bounds

Statement only, in Mathlib's vocabulary. A matching of `H` is a subgraph
`M ≤ H` in which every vertex has at most one neighbor
(`(M.neighborSet v).Subsingleton`).

Claim: if every vertex of the finite graph `H` has degree at least `k` and `H`
has at least `2 * k` vertices, then `H` has a matching (with decidable
adjacency, so that its edge finset is defined) with at least `k` edges.
-/

namespace TotalColoringAudit.MatchingLowerBound

theorem exists_matchingGraph_edgeFinset_card_ge
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hdegree : ∀ v, k ≤ H.degree v) (horder : 2 * k ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V) (_ : DecidableRel M.Adj),
      M ≤ H ∧ (∀ v, (M.neighborSet v).Subsingleton) ∧ k ≤ M.edgeFinset.card := by
  sorry

end TotalColoringAudit.MatchingLowerBound
