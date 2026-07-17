import TotalColoring.FanCount

/-!
# Saturated finite incidence profiles

This module isolates the equality case behind the canonical reachable-set
count.  If one occurring color has multiplicity three, every other occurring
color has multiplicity at most two, the number of occurring colors is at most
the number of leaves, and there are at least `2 * |L| + 1` incidences, then
all inequalities are equalities.  In particular every other occurring color
has multiplicity exactly two.

This is finite arithmetic only.  It does not assert that a graph-theoretic
critical state satisfies the unique-triple premise.
-/

namespace TotalColoring

namespace FanCount

variable {L C : Type*}

/-- With one distinguished triple and every other occurring multiplicity at
most two, the incidence count is at most `2 * |R| + 1`. -/
theorem incidenceCount_le_two_mul_occurringColors_card_add_one_of_one_three
    (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R] {gamma : C}
    (hgamma : gamma ∈ occurringColors leaves colors R)
    (hgammaThree : colorMultiplicity leaves R gamma = 3)
    (hother : ∀ color ∈ occurringColors leaves colors R,
      color ≠ gamma → colorMultiplicity leaves R color ≤ 2) :
    incidenceCount leaves colors R ≤
      2 * (occurringColors leaves colors R).card + 1 := by
  classical
  let O := occurringColors leaves colors R
  let multiplicity : C → ℕ := fun color ↦ colorMultiplicity leaves R color
  have hsumErase :
      (∑ color ∈ O.erase gamma, multiplicity color) ≤
        2 * (O.erase gamma).card := by
    have hpoint : ∀ color ∈ O.erase gamma, multiplicity color ≤ 2 := by
      intro color hcolor
      exact hother color (Finset.mem_erase.mp hcolor).2
        (Finset.mem_erase.mp hcolor).1
    have hsum := Finset.sum_le_card_nsmul
      (O.erase gamma) multiplicity 2 hpoint
    simpa [Nat.mul_comm] using hsum
  have hcardErase : (O.erase gamma).card + 1 = O.card :=
    Finset.card_erase_add_one hgamma
  rw [incidenceCount_eq_sum_occurringColors]
  change (∑ color ∈ O, multiplicity color) ≤ 2 * O.card + 1
  rw [← Finset.sum_erase_add O multiplicity hgamma]
  have hgammaThree' : multiplicity gamma = 3 := by
    simpa [multiplicity] using hgammaThree
  rw [hgammaThree']
  omega

/-- Equality case of the one-triple incidence bound.  Besides saturating the
number of occurring colors and the total incidence count, every other
occurring color has multiplicity exactly two. -/
theorem saturatedProfile_of_one_three
    (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R] {gamma : C}
    (hgamma : gamma ∈ occurringColors leaves colors R)
    (hgammaThree : colorMultiplicity leaves R gamma = 3)
    (hother : ∀ color ∈ occurringColors leaves colors R,
      color ≠ gamma → colorMultiplicity leaves R color ≤ 2)
    (hoccurring : (occurringColors leaves colors R).card ≤ leaves.card)
    (hincidences : 2 * leaves.card + 1 ≤
      incidenceCount leaves colors R) :
    (occurringColors leaves colors R).card = leaves.card ∧
      incidenceCount leaves colors R = 2 * leaves.card + 1 ∧
      ∀ color ∈ occurringColors leaves colors R,
        color ≠ gamma → colorMultiplicity leaves R color = 2 := by
  classical
  let O := occurringColors leaves colors R
  let multiplicity : C → ℕ := fun color ↦ colorMultiplicity leaves R color
  have hupper : incidenceCount leaves colors R ≤ 2 * O.card + 1 := by
    simpa [O] using
      incidenceCount_le_two_mul_occurringColors_card_add_one_of_one_three
        leaves colors R hgamma hgammaThree hother
  change O.card ≤ leaves.card at hoccurring
  have hcardEq : O.card = leaves.card := by omega
  have hincidenceEq :
      incidenceCount leaves colors R = 2 * leaves.card + 1 := by omega
  have hsumErase :
      (∑ color ∈ O.erase gamma, multiplicity color) =
        2 * (O.erase gamma).card := by
    have hcardErase : (O.erase gamma).card + 1 = O.card :=
      Finset.card_erase_add_one hgamma
    rw [incidenceCount_eq_sum_occurringColors] at hincidenceEq
    change (∑ color ∈ O, multiplicity color) =
      2 * leaves.card + 1 at hincidenceEq
    rw [← Finset.sum_erase_add O multiplicity hgamma] at hincidenceEq
    change colorMultiplicity leaves R gamma = 3 at hgammaThree
    change multiplicity gamma = 3 at hgammaThree
    rw [hgammaThree] at hincidenceEq
    omega
  refine ⟨hcardEq, hincidenceEq, ?_⟩
  intro color hcolor hne
  change color ∈ O at hcolor
  change multiplicity color = 2
  have hle : multiplicity color ≤ 2 := by
    simpa [multiplicity] using hother color hcolor hne
  have hmemErase : color ∈ O.erase gamma :=
    Finset.mem_erase.mpr ⟨hne, hcolor⟩
  by_contra hnotEq
  have hlt : multiplicity color < 2 := by omega
  have hstrict :
      (∑ theta ∈ O.erase gamma, multiplicity theta) <
        ∑ _theta ∈ O.erase gamma, 2 := by
    apply Finset.sum_lt_sum
    · intro theta htheta
      exact hother theta (Finset.mem_erase.mp htheta).2
        (Finset.mem_erase.mp htheta).1
    · exact ⟨color, hmemErase, hlt⟩
  have hconstant : (∑ _theta ∈ O.erase gamma, 2) =
      2 * (O.erase gamma).card := by
    simp [Nat.mul_comm]
  rw [hsumErase, hconstant] at hstrict
  exact (Nat.lt_irrefl _ hstrict)

end FanCount

end TotalColoring
