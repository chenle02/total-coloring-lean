import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Finite incidence counting

This module isolates the arithmetic core of a conditional fan count.  Given
finite sets of leaves and colors and an arbitrary incidence predicate `R`, it
counts the leaves incident with each color and the total incidences.  If every
color which actually occurs has multiplicity at most two, then the number of
incidences is at most twice the number of distinct occurring colors.

The multiplicity-two assertion is deliberately an explicit hypothesis.  No
graph-theoretic argument establishing it is claimed here.
-/

namespace TotalColoring

namespace FanCount

variable {L C : Type*}

/-- The number of selected leaves related to a fixed color. -/
def colorMultiplicity (leaves : Finset L) (R : L → C → Prop)
    [DecidableRel R] (color : C) : ℕ :=
  (leaves.filter fun leaf ↦ R leaf color).card

/-- The colors in `colors` which occur on at least one selected leaf. -/
def occurringColors (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R] : Finset C :=
  colors.filter fun color ↦ 0 < colorMultiplicity leaves R color

/-- The total number of `R`-incidences between the selected leaves and
selected colors, counted by color fibers. -/
def incidenceCount (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R] : ℕ :=
  ∑ color ∈ colors, colorMultiplicity leaves R color

@[simp]
theorem mem_occurringColors_iff (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R] (color : C) :
    color ∈ occurringColors leaves colors R ↔
      color ∈ colors ∧ 0 < colorMultiplicity leaves R color := by
  simp [occurringColors]

/-- Removing the zero-multiplicity colors does not change the incidence
count. -/
theorem incidenceCount_eq_sum_occurringColors
    (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R] :
    incidenceCount leaves colors R =
      ∑ color ∈ occurringColors leaves colors R,
        colorMultiplicity leaves R color := by
  unfold incidenceCount
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro color hcolor hnotOccurs
  have hnotPositive : ¬0 < colorMultiplicity leaves R color := by
    intro hpositive
    exact hnotOccurs (mem_occurringColors_iff leaves colors R color |>.2
      ⟨hcolor, hpositive⟩)
  exact Nat.eq_zero_of_not_pos hnotPositive

/-- If every occurring color has multiplicity at most two, then total
incidences are at most twice the number of distinct occurring colors. -/
theorem incidenceCount_le_two_mul_occurringColors_card
    (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R]
    (hmultiplicity : ∀ color ∈ occurringColors leaves colors R,
      colorMultiplicity leaves R color ≤ 2) :
    incidenceCount leaves colors R ≤
      2 * (occurringColors leaves colors R).card := by
  rw [incidenceCount_eq_sum_occurringColors]
  have hsum := Finset.sum_le_card_nsmul
    (occurringColors leaves colors R)
    (fun color ↦ colorMultiplicity leaves R color) 2 hmultiplicity
  simpa [Nat.mul_comm] using hsum

/-- Sharp integral consequence of the multiplicity-two bound: at least
`2 * t + 3` incidences require at least `t + 2` distinct occurring colors. -/
theorem t_add_two_le_occurringColors_card_of_two_mul_t_add_three_le
    (leaves : Finset L) (colors : Finset C)
    (R : L → C → Prop) [DecidableRel R] (t : ℕ)
    (hmultiplicity : ∀ color ∈ occurringColors leaves colors R,
      colorMultiplicity leaves R color ≤ 2)
    (hincidences : 2 * t + 3 ≤ incidenceCount leaves colors R) :
    t + 2 ≤ (occurringColors leaves colors R).card := by
  have hupper := incidenceCount_le_two_mul_occurringColors_card
    leaves colors R hmultiplicity
  omega

end FanCount

end TotalColoring
