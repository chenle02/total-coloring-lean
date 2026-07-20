import TotalColoring.MinSixCageModel

namespace TotalColoring.MinSixCage

/-- Double-count the selected descriptor--core-vertex eligibility incidences. -/
theorem sum_columnCount_eq_sum_eligible_card (X : Finset Descriptor) :
    ∑ v : CoreVertex, columnCount X v =
      ∑ d ∈ X, d.eligible.card := by
  calc
    ∑ v : CoreVertex, columnCount X v =
        ∑ v : CoreVertex, ∑ d ∈ X, if v ∈ d.eligible then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      simp [columnCount]
    _ = ∑ d ∈ X, ∑ v : CoreVertex, if v ∈ d.eligible then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ X, d.eligible.card := by
      apply Finset.sum_congr rfl
      intro d _
      simp

/-- A six-column mask demands three incidences per column plus one for each
set bit. -/
theorem Mask.sum_requiredColumn (B : Mask) :
    ∑ v : CoreVertex, B.requiredColumn v = 18 + B.popcount := by
  calc
    ∑ v : CoreVertex, B.requiredColumn v =
        ∑ v : CoreVertex, (3 + if B.bit v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [Mask.requiredColumn]
      split_ifs <;> omega
    _ = 18 + B.popcount := by
      simp [Finset.sum_add_distrib, Mask.popcount, Finset.sum_boole]

/-- The ambient-incidence lower bound forces at least two degree-four
columns. -/
theorem Blocker.admissible {B : Mask} {X : Finset Descriptor}
    (h : Blocker B X) : B.Admissible := by
  unfold Mask.Admissible
  have hDemand : 20 ≤ ∑ v : CoreVertex, B.requiredColumn v := by
    calc
      20 ≤ ∑ v : CoreVertex, columnCount X v := h.ambientIncidence
      _ = ∑ v : CoreVertex, B.requiredColumn v := by
        apply Finset.sum_congr rfl
        intro v _
        exact h.columns v
  rw [B.sum_requiredColumn] at hDemand
  omega

end TotalColoring.MinSixCage
