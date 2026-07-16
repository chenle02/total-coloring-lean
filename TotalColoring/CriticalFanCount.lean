import TotalColoring.CriticalFan
import TotalColoring.FanLeaves
import TotalColoring.FanMissingCount
import TotalColoring.MissingGeneralCount

/-!
# Conditional missing-incidence count on a critical fan

Every leaf of a fan in an `A_D` member has at least two missing colors from the
`D + 2` palette.  The root leaf, being incident with the unique hole, has one
additional missing color.  This module kernel-checks the resulting lower
bound and combines it with an explicitly assumed multiplicity-two hypothesis.

It does **not** prove multiplicity two or the final fan contradiction.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- The selected fan leaves have at least two missing incidences each, plus
one extra at the root endpoint of the unique hole. -/
theorem two_mul_card_leafFinset_add_one_le_sum_missingColorsAt
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hhole : a.OneHoleAt F.root.edge) :
    2 * F.leafFinset.card + 1 ≤
      ∑ leaf ∈ F.leafFinset,
        (a.missingColorsAt Finset.univ leaf).card := by
  classical
  rcases h.member with ⟨x, M, hstructure⟩
  have hPalette : (Finset.univ : Finset (ExtensionPalette D)).card = D + 2 := by
    simp [ExtensionPalette]
  have htwo (leaf : V) :
      2 ≤ (a.missingColorsAt Finset.univ leaf).card :=
    PartialEdgeAssignment.two_le_missingColorsAt_card_of_palette_card_eq_of_degree_le
      a Finset.univ leaf D hPalette (hstructure.degree_le_parameter leaf)
  have hrootCount :=
    PartialEdgeAssignment.D_add_three_sub_degree_le_missingColorsAt_card
      (a := a) (palette := Finset.univ) hhole F.root.leaf_incident hPalette
  have hrootThree :
      3 ≤ (a.missingColorsAt Finset.univ F.root.leaf).card := by
    have hdegree := hstructure.degree_le_parameter F.root.leaf
    have hthreeSub : 3 ≤ D + 3 - H.degree F.root.leaf :=
      Nat.le_sub_of_add_le (by omega)
    exact hthreeSub.trans hrootCount
  let weight : V → ℕ := fun leaf ↦
    if leaf = F.root.leaf then 3 else 2
  have hpoint (leaf : V) (hleaf : leaf ∈ F.leafFinset) :
      weight leaf ≤ (a.missingColorsAt Finset.univ leaf).card := by
    by_cases hroot : leaf = F.root.leaf
    · subst leaf
      simpa [weight] using hrootThree
    · simpa [weight, hroot] using htwo leaf
  have hsum :
      (∑ leaf ∈ F.leafFinset, weight leaf) ≤
        ∑ leaf ∈ F.leafFinset,
          (a.missingColorsAt Finset.univ leaf).card :=
    Finset.sum_le_sum hpoint
  have hrootMem : F.root.leaf ∈ F.leafFinset :=
    F.root_leaf_mem_leafFinset
  have hweight :
      (∑ leaf ∈ F.leafFinset, weight leaf) =
        2 * F.leafFinset.card + 1 := by
    rw [← Finset.sum_erase_add F.leafFinset weight hrootMem]
    have herase :
        (∑ leaf ∈ F.leafFinset.erase F.root.leaf, weight leaf) =
          2 * (F.leafFinset.erase F.root.leaf).card := by
      calc
        _ = ∑ _leaf ∈ F.leafFinset.erase F.root.leaf, 2 := by
          apply Finset.sum_congr rfl
          intro leaf hleaf
          have hne : leaf ≠ F.root.leaf :=
            (Finset.mem_erase.mp hleaf).1
          simp [weight, hne]
        _ = 2 * (F.leafFinset.erase F.root.leaf).card := by
          simp [Nat.mul_comm]
    rw [herase, Finset.card_erase_of_mem hrootMem]
    simp [weight]
    have hcardPos : 0 < F.leafFinset.card :=
      Finset.card_pos.mpr ⟨F.root.leaf, hrootMem⟩
    omega
  rw [hweight] at hsum
  exact hsum

/-- Conditional leaf-count consequence of the proposed multiplicity-two
lemma: the number of distinct colors missing on the fan leaves is at least one
more than the number of leaves.  Multiplicity two remains an explicit input. -/
theorem card_leafFinset_add_one_le_distinct_missingColors_of_multiplicity_two
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hhole : a.OneHoleAt F.root.edge)
    (hmultiplicity : ∀ color ∈
      FanCount.occurringColors F.leafFinset Finset.univ a.MissingAt,
      FanCount.colorMultiplicity F.leafFinset a.MissingAt color ≤ 2) :
    F.leafFinset.card + 1 ≤
      (FanCount.occurringColors F.leafFinset Finset.univ
        a.MissingAt).card := by
  classical
  apply PartialEdgeAssignment.card_add_one_le_distinct_fanMissingColors_of_multiplicity_two
    a F.leafFinset Finset.univ hmultiplicity
  exact h.two_mul_card_leafFinset_add_one_le_sum_missingColorsAt F hhole

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
