import TotalColoring.AuxiliaryClass
import TotalColoring.DeletionBridge
import TotalColoring.Distinguished
import TotalColoring.MissingCount
import Mathlib.Data.Fintype.EquivFin

/-!
# Deletion-critical one-hole states

This module turns the paper's edge-minimal-counterexample setup into the
one-hole interface used by the recoloring and missing-color modules.  The
minimality hypothesis is explicit and local: every smaller member on the same
vertex type and with the same stable distinguished finset is colorable.

No member of the auxiliary class is asserted to be colorable here.  Rather,
the theorems state what follows from a hypothetical minimal noncolorable
member, exactly as required inside a contradiction proof.
-/

namespace TotalColoring

universe u

/-- The exact `D + 2` palette used by the auxiliary extension problem. -/
abbrev ExtensionPalette (D : ℕ) := Fin (D + 2)

/-- Existence of a proper edge coloring which is rainbow on the stable
distinguished finset. -/
def HasValidRainbowColoring {V : Type u} (D : ℕ) (H : SimpleGraph V)
    (J : Finset (Sym2 V)) : Prop :=
  ∃ a : EdgeAssignment H (ExtensionPalette D),
    a.Valid ∧ a.RainbowOn (distinguishedEdgeSet H J)

/-- The number of ambient edges outside the stable distinguished finset. -/
noncomputable def outsideEdgeCount {V : Type u} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (J : Finset (Sym2 V)) : ℕ :=
  (H.edgeSet \ (J : Set (Sym2 V))).ncard

/-- A hypothetical noncolorable member minimal in the number of edges outside
`J`, expressed by the order-theoretic minimality property.

A global minimum among all noncolorable members supplies this structure.  The
same-vertex, same-`J` formulation avoids claiming more than the deletion proof
uses. -/
structure IsOutsideEdgeMinimalNoncolorable
    {V : Type u} [Fintype V] [DecidableEq V]
    (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (J : Finset (Sym2 V)) : Prop where
  member : InAuxiliaryClass D H J
  noncolorable : ¬HasValidRainbowColoring D H J
  minimal :
    ∀ {H' : SimpleGraph V} [DecidableRel H'.Adj],
      InAuxiliaryClass D H' J →
      ¬HasValidRainbowColoring D H' J →
      outsideEdgeCount H J ≤ outsideEdgeCount H' J

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

omit [Fintype V] [DecidableEq V] [DecidableRel H.Adj] in
/-- The coloring-facing distinguished set commutes with deletion transport. -/
theorem distinguishedInDelete_eq (e : H.edgeSet) :
    DeletionBridge.distinguishedInDelete e (distinguishedEdgeSet H J) =
      distinguishedEdgeSet (DeletionBridge.DeletedGraph H e) J := by
  ext f
  rfl

/-- A strictly smaller member on the same vertex type and with the same
stable `J` is colorable by minimality. -/
theorem colorable_of_smaller
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {H' : SimpleGraph V} [DecidableRel H'.Adj]
    (hmember : InAuxiliaryClass D H' J)
    (hsmaller : outsideEdgeCount H' J < outsideEdgeCount H J) :
    HasValidRainbowColoring D H' J := by
  by_contra hnoncolorable
  exact (Nat.not_lt_of_ge (h.minimal hmember hnoncolorable)) hsmaller

/-- A member with no edge outside `J` is colorable: all ambient edges are
distinguished, and the `D` of them inject into the `D + 2` palette.

This is the base case needed to know that a hypothetical noncolorable member
has an edge available for deletion. -/
theorem hasValidRainbowColoring_of_outsideEdgeCount_eq_zero
    (hmember : InAuxiliaryClass D H J)
    (hzero : outsideEdgeCount H J = 0) :
    HasValidRainbowColoring D H J := by
  classical
  rcases hmember with ⟨x, M, hstructure⟩
  have houtsideEmpty :
      H.edgeSet \ (J : Set (Sym2 V)) = ∅ := by
    rw [← Set.ncard_eq_zero]
    simpa [outsideEdgeCount] using hzero
  have hallJ (e : H.edgeSet) : e ∈ distinguishedEdgeSet H J := by
    by_contra heJ
    have heOutside : (e : Sym2 V) ∈
        H.edgeSet \ (J : Set (Sym2 V)) := ⟨e.2, heJ⟩
    rw [houtsideEmpty] at heOutside
    exact heOutside
  have hdistinguished : distinguishedEdgeSet H J = Set.univ := by
    ext e
    simp only [Set.mem_univ, iff_true]
    exact hallJ e
  letI : Fintype H.edgeSet := Fintype.ofFinite _
  have hedgeCard : Fintype.card H.edgeSet = D := by
    calc
      Fintype.card H.edgeSet = (Set.univ : Set H.edgeSet).ncard := by simp
      _ = (distinguishedEdgeSet H J).ncard := by rw [hdistinguished]
      _ = D := hstructure.card_distinguishedEdgeSet
  have hcardLE : Fintype.card H.edgeSet ≤
      Fintype.card (ExtensionPalette D) := by
    simp [hedgeCard, ExtensionPalette]
  rcases Function.Embedding.nonempty_of_card_le hcardLE with
    ⟨colorEmbedding⟩
  let a : EdgeAssignment H (ExtensionPalette D) :=
    ⟨fun e ↦ colorEmbedding e⟩
  refine ⟨a, ?_, ?_⟩
  · intro e f hef heq
    exact hef.ne (colorEmbedding.injective heq)
  · intro e _he f _hf hef heq
    exact hef (colorEmbedding.injective heq)

/-- Every minimal noncolorable member has at least one edge outside `J`. -/
theorem exists_outside_edge
    (h : IsOutsideEdgeMinimalNoncolorable D H J) :
    ∃ e : H.edgeSet, (e : Sym2 V) ∉ J := by
  by_contra hno
  push Not at hno
  have houtsideEmpty : H.edgeSet \ (J : Set (Sym2 V)) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro f hf
    exact hf.2 (hno ⟨f, hf.1⟩)
  have hzero : outsideEdgeCount H J = 0 := by
    simp [outsideEdgeCount, houtsideEmpty]
  exact h.noncolorable
    (hasValidRainbowColoring_of_outsideEdgeCount_eq_zero h.member hzero)

omit [DecidableRel H.Adj] in
/-- Deleting an edge outside `J` strictly reduces the outside-edge count. -/
theorem outsideEdgeCount_delete_lt (e : H.edgeSet)
    (heJ : (e : Sym2 V) ∉ J) :
    outsideEdgeCount (DeletionBridge.DeletedGraph H e) J <
      outsideEdgeCount H J := by
  have hsubset :
      (DeletionBridge.DeletedGraph H e).edgeSet \ (J : Set (Sym2 V)) ⊆
        H.edgeSet \ (J : Set (Sym2 V)) := by
    intro f hf
    rw [SimpleGraph.edgeSet_deleteEdges] at hf
    exact ⟨hf.1.1, hf.2⟩
  have hne :
      (DeletionBridge.DeletedGraph H e).edgeSet \ (J : Set (Sym2 V)) ≠
        H.edgeSet \ (J : Set (Sym2 V)) := by
    intro heq
    have heOutside : (e : Sym2 V) ∈
        H.edgeSet \ (J : Set (Sym2 V)) := ⟨e.2, heJ⟩
    have heDeleted : (e : Sym2 V) ∈
        (DeletionBridge.DeletedGraph H e).edgeSet \
          (J : Set (Sym2 V)) := heq ▸ heOutside
    rw [SimpleGraph.edgeSet_deleteEdges] at heDeleted
    exact heDeleted.1.2 (Set.mem_singleton (e : Sym2 V))
  exact Set.ncard_lt_ncard
    ((Set.ssubset_iff_subset_ne).2 ⟨hsubset, hne⟩)

/-- Every outside edge of a minimal noncolorable member yields a valid,
`J`-rainbow one-hole state which admits no direct valid rainbow fill from the
whole `D + 2` palette. -/
theorem exists_blocked_oneHoleState
    (h : IsOutsideEdgeMinimalNoncolorable D H J) (e : H.edgeSet)
    (heJ : (e : Sym2 V) ∉ J) :
    ∃ a : PartialEdgeAssignment H (ExtensionPalette D),
      a.Valid ∧ a.OneHoleAt e ∧
      a.RainbowOn (distinguishedEdgeSet H J) ∧
      a.NoValidCompleteRainbowFill Finset.univ e
        (distinguishedEdgeSet H J) := by
  have hdeletedMember :
      InAuxiliaryClass D (DeletionBridge.DeletedGraph H e) J :=
    h.member.deleteEdgeOutside e.2 heJ
  have hsmaller := outsideEdgeCount_delete_lt (J := J) e heJ
  rcases h.colorable_of_smaller hdeletedMember hsmaller with
    ⟨b, hbvalid, hbrainbow⟩
  let a : PartialEdgeAssignment H (ExtensionPalette D) :=
    DeletionBridge.lift e b
  have hvalid : a.Valid := DeletionBridge.lift_valid e hbvalid
  have hhole : a.OneHoleAt e := DeletionBridge.lift_oneHoleAt e b
  have heJset : e ∉ distinguishedEdgeSet H J := heJ
  have hrainbow : a.RainbowOn (distinguishedEdgeSet H J) := by
    apply DeletionBridge.lift_rainbowOn e heJset
    rw [distinguishedInDelete_eq (J := J) e]
    exact hbrainbow
  refine ⟨a, hvalid, hhole, hrainbow, ?_⟩
  intro c _hc hfill
  apply h.noncolorable
  let full := (a.fill e c).toEdgeAssignment hfill.2.1
  exact ⟨full,
    PartialEdgeAssignment.toEdgeAssignment_valid hfill.2.1 hfill.1,
    PartialEdgeAssignment.toEdgeAssignment_rainbowOn hfill.2.1 hfill.2.2⟩

/-- The full critical degree-sum checkpoint for a hypothetical minimal
noncolorable member: no missing-count or disjointness hypothesis remains to be
supplied by prose. -/
theorem degree_sum_outside_edge
    (h : IsOutsideEdgeMinimalNoncolorable D H J) (e : H.edgeSet)
    (heJ : (e : Sym2 V) ∉ J) {u v : V}
    (hends : (e : Sym2 V) = s(u, v)) :
    D + 4 ≤ H.degree u + H.degree v := by
  rcases h.exists_blocked_oneHoleState e heJ with
    ⟨a, hvalid, hhole, hrainbow, hblocked⟩
  exact a.degree_sum_of_no_valid_complete_rainbow_fill_of_palette_card_eq
    hends hvalid hhole hrainbow heJ hblocked (by simp [ExtensionPalette])

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
