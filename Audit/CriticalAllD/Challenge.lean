/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib

/-!
# Comparator challenge: no outside-edge-minimal noncolorable auxiliary member

Statement only, in Mathlib's vocabulary. Membership of `(H, J)` in the
auxiliary class `A_D` is the existence of a center `x` and a matching part `M`
satisfying the nine membership conditions of
`Audit/AuxiliaryClass/Challenge.lean`, written out. `(H, J)` is colorable when
`H` has a proper edge coloring with `D + 2` colors (on Mathlib's line graph)
that gives distinct colors to distinct edges of `J`. The outside-edge count of
`H` is the number of edges of `H` not in `J`.

Claim: there is no finite `(H, J)` that is a member of `A_D`, is not colorable,
and has at most as many outside edges as every noncolorable member `(H₁, J)`
of `A_D` on the same vertex type with the same `J`.
-/

namespace TotalColoringAudit.CriticalAllD

theorem false_of_critical_allD
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (J : Finset (Sym2 V))
    (member : ∃ (x : V) (M : Finset (Sym2 V)),
      (∀ ⦃e⦄, e ∈ J → e ∈ H.edgeSet) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f) ∧
      (∀ ⦃e⦄, e ∈ M → x ∉ e) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H.Adj x v) ∧
      J = M ∪ H.incidenceFinset x ∧
      (∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e) ∧
      J.card = D ∧
      H.maxDegree ≤ D ∧
      (2 ≤ H.degree x ∧ H.degree x ≤ D))
    (noncolorable : ¬∃ color : H.edgeSet → Fin (D + 2),
      (∀ e f, H.lineGraph.Adj e f → color e ≠ color f) ∧
      (∀ e f : H.edgeSet, (e : Sym2 V) ∈ J → (f : Sym2 V) ∈ J → e ≠ f →
        color e ≠ color f))
    (minimal : ∀ (H₁ : SimpleGraph V) [DecidableRel H₁.Adj],
      (∃ (x : V) (M : Finset (Sym2 V)),
        (∀ ⦃e⦄, e ∈ J → e ∈ H₁.edgeSet) ∧
        (∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f) ∧
        (∀ ⦃e⦄, e ∈ M → x ∉ e) ∧
        (∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H₁.Adj x v) ∧
        J = M ∪ H₁.incidenceFinset x ∧
        (∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e) ∧
        J.card = D ∧
        H₁.maxDegree ≤ D ∧
        (2 ≤ H₁.degree x ∧ H₁.degree x ≤ D)) →
      (¬∃ color : H₁.edgeSet → Fin (D + 2),
        (∀ e f, H₁.lineGraph.Adj e f → color e ≠ color f) ∧
        (∀ e f : H₁.edgeSet, (e : Sym2 V) ∈ J → (f : Sym2 V) ∈ J → e ≠ f →
          color e ≠ color f)) →
      (H.edgeSet \ (J : Set (Sym2 V))).ncard ≤ (H₁.edgeSet \ (J : Set (Sym2 V))).ncard) :
    False := by
  sorry

end TotalColoringAudit.CriticalAllD
