/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.CriticalAllDClosure

/-!
# Comparator solution: no outside-edge-minimal noncolorable auxiliary member

Same statement as `Audit/CriticalAllD/Challenge.lean`, from
`TotalColoring.IsOutsideEdgeMinimalNoncolorable.false_of_critical_allD`: the
structure `IsOutsideEdgeMinimalNoncolorable D H J` has the three fields
`member : InAuxiliaryClass D H J` (the center, the matching part and the nine
fields of `IsAuxiliaryClassMember`), `noncolorable : ¬HasValidRainbowColoring D H J`
(a valid edge assignment into `Fin (D + 2)`, rainbow on the edges of `J`), and
`minimal`, with `outsideEdgeCount H J = (H.edgeSet \ ↑J).ncard`.

`Fidelity.not_weaker` derives the library theorem back from the Challenge
statement, so the two statements are equivalent.
-/

namespace TotalColoringAudit.CriticalAllD

namespace Bridge

open TotalColoring

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Membership in the auxiliary class, written out. -/
theorem inAuxiliaryClass_iff (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (J : Finset (Sym2 V)) :
    InAuxiliaryClass D H J ↔ ∃ (x : V) (M : Finset (Sym2 V)),
      (∀ ⦃e⦄, e ∈ J → e ∈ H.edgeSet) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f) ∧
      (∀ ⦃e⦄, e ∈ M → x ∉ e) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H.Adj x v) ∧
      J = M ∪ H.incidenceFinset x ∧
      (∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e) ∧
      J.card = D ∧
      H.maxDegree ≤ D ∧
      (2 ≤ H.degree x ∧ H.degree x ≤ D) := by
  constructor
  · rintro ⟨x, M, h⟩
    exact ⟨x, M, h.distinguished_edges, h.matching, h.matching_off_center,
      h.matching_avoids_center_neighbors, h.decomposition, h.exact_coverage,
      h.card_distinguished, h.maxDegree_bound, h.center_degree⟩
  · rintro ⟨x, M, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    exact ⟨x, M, ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩

/-- Colorability, written out. -/
theorem hasValidRainbowColoring_iff {V : Type*} (D : ℕ) (H : SimpleGraph V)
    (J : Finset (Sym2 V)) :
    HasValidRainbowColoring D H J ↔ ∃ color : H.edgeSet → Fin (D + 2),
      (∀ e f, H.lineGraph.Adj e f → color e ≠ color f) ∧
      (∀ e f : H.edgeSet, (e : Sym2 V) ∈ J → (f : Sym2 V) ∈ J → e ≠ f →
        color e ≠ color f) := by
  constructor
  · rintro ⟨a, hvalid, hrainbow⟩
    exact ⟨a.color, hvalid, fun e f he hf hne => hrainbow he hf hne⟩
  · rintro ⟨color, hvalid, hrainbow⟩
    exact ⟨⟨color⟩, hvalid, fun {e} he {f} hf hne => hrainbow e f he hf hne⟩

end Bridge

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
  refine TotalColoring.IsOutsideEdgeMinimalNoncolorable.false_of_critical_allD
    (D := D) (H := H) (J := J) ⟨?_, ?_, ?_⟩
  · exact (Bridge.inAuxiliaryClass_iff D H J).2 member
  · rwa [Bridge.hasValidRainbowColoring_iff]
  · intro H₁ _ hmember hnon
    exact minimal H₁ ((Bridge.inAuxiliaryClass_iff D H₁ J).1 hmember)
      (by rwa [Bridge.hasValidRainbowColoring_iff] at hnon)

namespace Fidelity

universe u

/-- The Challenge statement implies the library statement. -/
theorem not_weaker (h : type_of% @false_of_critical_allD.{u}) :
    type_of% @TotalColoring.IsOutsideEdgeMinimalNoncolorable.false_of_critical_allD.{u} := by
  intro V _ _ D H J _ hmin
  refine h D H J ((Bridge.inAuxiliaryClass_iff D H J).1 hmin.member) ?_ ?_
  · rw [← Bridge.hasValidRainbowColoring_iff]
    exact hmin.noncolorable
  · intro H₁ _ hmember hnon
    exact hmin.minimal ((Bridge.inAuxiliaryClass_iff D H₁ J).2 hmember)
      (by rwa [Bridge.hasValidRainbowColoring_iff])

end Fidelity

end TotalColoringAudit.CriticalAllD
