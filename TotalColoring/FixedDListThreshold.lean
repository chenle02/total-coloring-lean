import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-!
# Fixed-parameter list-edge threshold arithmetic

This module checks the numerical interface used when the
Borodin--Kostochka--Woodall local list-edge theorem is applied to an ordinary
graph together with a precolored distinguished matching.  It does not
formalize that external list-edge theorem and therefore proves no coloring
existence statement by itself.

For an ordinary edge with endpoint degrees `du,dv`, the external theorem asks
for a list of size at least

`max du dv + floor (min du dv / 2)`.

In the fixed-parameter class, a vertex covered by the matching has ordinary
degree at most `D - 1`, while an uncovered vertex has ordinary degree at most
`D`.  The three endpoint cases fit the available lists for every `D <= 6`.
At `D = 7`, exactly the extremal covered/covered and covered/uncovered bounds
first exceed their corresponding guaranteed list sizes.
-/

namespace TotalColoring

namespace FixedDListThreshold

/-- The local list size demanded by the BKW edge-choosability criterion. -/
def demand (du dv : ℕ) : ℕ := max du dv + min du dv / 2

/-- The BKW numerical demand is monotone in the two endpoint degrees. -/
theorem demand_mono {du dv Du Dv : ℕ}
    (hu : du ≤ Du) (hv : dv ≤ Dv) :
    demand du dv ≤ demand Du Dv := by
  unfold demand
  exact Nat.add_le_add (max_le_max hu hv)
    (Nat.div_le_div_right (min_le_min hu hv))

/-- Two endpoints covered by distinct matching edges have enough colors when
`1 <= D <= 6`: two different forbidden matching colors leave `D + 1`
available colors. -/
theorem demand_le_D_add_one_of_both_covered
    {D du dv : ℕ} (hpos : 1 ≤ D) (hD : D ≤ 6)
    (hu : du ≤ D - 1) (hv : dv ≤ D - 1) :
    demand du dv ≤ D + 1 := by
  calc
    demand du dv ≤ demand (D - 1) (D - 1) := demand_mono hu hv
    _ = (D - 1) + (D - 1) / 2 := by simp [demand]
    _ ≤ D + 1 := by omega

/-- One covered and one uncovered endpoint have enough colors when
`1 <= D <= 6`: one or two forbidden matching colors leave at least `D + 2`
available colors. -/
theorem demand_le_D_add_two_of_one_covered
    {D du dv : ℕ} (hpos : 1 ≤ D) (hD : D ≤ 6)
    (hu : du ≤ D - 1) (hv : dv ≤ D) :
    demand du dv ≤ D + 2 := by
  calc
    demand du dv ≤ demand (D - 1) D := demand_mono hu hv
    _ = D + (D - 1) / 2 := by simp [demand]
    _ ≤ D + 2 := by omega

/-- The preceding mixed-endpoint estimate is symmetric. -/
theorem demand_le_D_add_two_of_one_covered'
    {D du dv : ℕ} (hpos : 1 ≤ D) (hD : D ≤ 6)
    (hu : du ≤ D) (hv : dv ≤ D - 1) :
    demand du dv ≤ D + 2 := by
  rw [demand, max_comm, min_comm]
  exact demand_le_D_add_two_of_one_covered hpos hD hv hu

/-- Two uncovered endpoints have enough colors when `D <= 6`: no matching
color is forbidden, so all `D + 3` colors remain available. -/
theorem demand_le_D_add_three_of_both_uncovered
    {D du dv : ℕ} (hD : D ≤ 6)
    (hu : du ≤ D) (hv : dv ≤ D) :
    demand du dv ≤ D + 3 := by
  calc
    demand du dv ≤ demand D D := demand_mono hu hv
    _ = D + D / 2 := by simp [demand]
    _ ≤ D + 3 := by omega

/-- Endpoints covered by the same matching edge forbid only one matching
color.  The weaker `D + 2` list bound follows from the distinct-carrier case. -/
theorem demand_le_D_add_two_of_same_carrier
    {D du dv : ℕ} (hpos : 1 ≤ D) (hD : D ≤ 6)
    (hu : du ≤ D - 1) (hv : dv ≤ D - 1) :
    demand du dv ≤ D + 2 := by
  have h := demand_le_D_add_one_of_both_covered hpos hD hu hv
  omega

/-- All four endpoint bounds used in the fixed-`D` application hold through
`D = 6`. -/
theorem all_endpoint_bounds_of_le_six
    {D : ℕ} (hpos : 1 ≤ D) (hD : D ≤ 6) :
    demand (D - 1) (D - 1) ≤ D + 1 ∧
      demand (D - 1) D ≤ D + 2 ∧
      demand D D ≤ D + 3 ∧
      demand (D - 1) (D - 1) ≤ D + 2 := by
  exact ⟨
    demand_le_D_add_one_of_both_covered hpos hD le_rfl le_rfl,
    demand_le_D_add_two_of_one_covered hpos hD le_rfl le_rfl,
    demand_le_D_add_three_of_both_uncovered hD le_rfl le_rfl,
    demand_le_D_add_two_of_same_carrier hpos hD le_rfl le_rfl⟩

/-- At `D = 7`, two ordinary-degree-six endpoints covered by distinct
matching edges require nine list colors, while only eight are guaranteed. -/
theorem seven_both_covered_residue :
    demand 6 6 = 9 ∧ 7 + 1 < demand 6 6 := by
  decide

/-- At `D = 7`, a covered degree-six endpoint joined to an uncovered
degree-seven endpoint requires ten list colors, while only nine are
guaranteed. -/
theorem seven_one_covered_residue :
    demand 6 7 = 10 ∧ 7 + 2 < demand 6 7 := by
  decide

/-- The two-uncovered endpoint case remains exactly within the BKW threshold
at `D = 7`. -/
theorem seven_both_uncovered_still_fits :
    demand 7 7 = 10 ∧ demand 7 7 = 7 + 3 := by
  decide

end FixedDListThreshold

end TotalColoring
