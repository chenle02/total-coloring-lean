import TotalColoring.FanCount
import TotalColoring.Missing

/-!
# Missing-color incidence counts on fan leaves

This module connects the predicate-level counting core in `FanCount` to the
finite missing-color sets of a partial edge coloring.  The graph-theoretic
multiplicity-two assertion remains an explicit hypothesis.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Counting missing incidences by colors agrees with counting the missing
palette finset at each selected leaf. -/
theorem fanMissing_incidenceCount_eq_sum_missingColorsAt_card
    [DecidableEq V] [DecidableEq C]
    (a : PartialEdgeAssignment G C) [DecidableRel a.MissingAt]
    (leaves : Finset V)
    (palette : Finset C) :
    FanCount.incidenceCount leaves palette a.MissingAt =
      ∑ leaf ∈ leaves, (a.missingColorsAt palette leaf).card := by
  classical
  induction leaves using Finset.induction_on with
  | empty =>
      simp [FanCount.incidenceCount, FanCount.colorMultiplicity]
  | @insert leaf leaves hleaf ih =>
      unfold FanCount.incidenceCount FanCount.colorMultiplicity at ih ⊢
      rw [Finset.sum_insert hleaf, ← ih]
      have hmissingDef :
          a.missingColorsAt palette leaf =
            palette.filter (a.MissingAt leaf) := by
        ext color
        simp only [mem_missingColorsAt, Finset.mem_filter]
      rw [hmissingDef]
      change
        (∑ color ∈ palette,
          ({v ∈ insert leaf leaves | a.MissingAt v color}).card) =
        (palette.filter (a.MissingAt leaf)).card +
          ∑ color ∈ palette,
            ({v ∈ leaves | a.MissingAt v color}).card
      calc
        _ = ∑ color ∈ palette,
            ((if a.MissingAt leaf color then 1 else 0) +
              ({v ∈ leaves | a.MissingAt v color}).card) := by
          apply Finset.sum_congr rfl
          intro color _hcolor
          by_cases hmissing : a.MissingAt leaf color
          · simp [Finset.filter_insert, hmissing, hleaf, Nat.add_comm]
          · simp [Finset.filter_insert, hmissing]
        _ = (∑ color ∈ palette,
              if a.MissingAt leaf color then 1 else 0) +
            ∑ color ∈ palette,
              ({v ∈ leaves | a.MissingAt v color}).card := by
          rw [Finset.sum_add_distrib]
        _ = (palette.filter (a.MissingAt leaf)).card +
            ∑ color ∈ palette,
              ({v ∈ leaves | a.MissingAt v color}).card := by
          congr 1
          simp

/-- Conditional distinct-color consequence in the notation of a partial edge
coloring.  If every palette color is missing at at most two selected leaves
and the leaves have at least `2 * t + 3` missing incidences, then at least
`t + 2` distinct palette colors are missing somewhere on the leaves. -/
theorem t_add_two_le_distinct_fanMissingColors_of_multiplicity_two
    [DecidableEq V] [DecidableEq C]
    (a : PartialEdgeAssignment G C) [DecidableRel a.MissingAt]
    (leaves : Finset V)
    (palette : Finset C) (t : ℕ)
    (hmultiplicity : ∀ color ∈
      FanCount.occurringColors leaves palette a.MissingAt,
      FanCount.colorMultiplicity leaves a.MissingAt color ≤ 2)
    (hincidences : 2 * t + 3 ≤
      ∑ leaf ∈ leaves, (a.missingColorsAt palette leaf).card) :
    t + 2 ≤
      (FanCount.occurringColors leaves palette a.MissingAt).card := by
  apply FanCount.t_add_two_le_occurringColors_card_of_two_mul_t_add_three_le
    leaves palette a.MissingAt t hmultiplicity
  rw [fanMissing_incidenceCount_eq_sum_missingColorsAt_card]
  exact hincidences

/-- Equivalent leaf-cardinality form of the sharp conditional bound.  A
baseline of two missing colors per selected leaf plus one extra incidence
forces strictly more distinct missing colors than leaves. -/
theorem card_add_one_le_distinct_fanMissingColors_of_multiplicity_two
    [DecidableEq V] [DecidableEq C]
    (a : PartialEdgeAssignment G C) [DecidableRel a.MissingAt]
    (leaves : Finset V) (palette : Finset C)
    (hmultiplicity : ∀ color ∈
      FanCount.occurringColors leaves palette a.MissingAt,
      FanCount.colorMultiplicity leaves a.MissingAt color ≤ 2)
    (hincidences : 2 * leaves.card + 1 ≤
      ∑ leaf ∈ leaves, (a.missingColorsAt palette leaf).card) :
    leaves.card + 1 ≤
      (FanCount.occurringColors leaves palette a.MissingAt).card := by
  have hupper := FanCount.incidenceCount_le_two_mul_occurringColors_card
    leaves palette a.MissingAt hmultiplicity
  rw [fanMissing_incidenceCount_eq_sum_missingColorsAt_card] at hupper
  omega

end PartialEdgeAssignment

end TotalColoring
