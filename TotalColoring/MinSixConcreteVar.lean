import Mathlib

/-!
# Finite variable namespace for the mask-63 minimum-six certificate

This file replaces the reusable encoders' unbounded auxiliary indices by the
exact bounded constructors occurring in the pinned full-parent mask-63 CNF.
That generator uses the `selected_atleast6` table with cap six; this is not the
separate `selected_exact_6` branch, whose table has cap seven. `rawCode`
implements the zero-based version of the independently audited parent-DIMACS
ledger.

This leaf proves that `rawCode` is a bijection with `Fin 34473`. Later leaves
must construct the ordered semantic lookups, identify the emitted raw formula
with the pinned CNF bytes, and attach the LRAT endpoint. Nothing here rules out
a blocker or proves a graph theorem.
-/

namespace TotalColoring.MinSixConcreteVar

/-- Number of allocated cells in all threshold rows strictly before row `i`,
where rows are zero-based and have width capped by `top`. -/
def thresholdRowOffset (top : Nat) : Nat → Nat
  | 0 => 0
  | i + 1 => thresholdRowOffset top i + min (i + 1) top

@[simp] theorem thresholdRowOffset_zero (top : Nat) :
    thresholdRowOffset top 0 = 0 := rfl

@[simp] theorem thresholdRowOffset_succ (top i : Nat) :
    thresholdRowOffset top (i + 1) =
      thresholdRowOffset top i + min (i + 1) top := rfl

/-- Every nonempty capped row advances the prefix offset. -/
theorem thresholdRowOffset_lt_succ
    {top : Nat} (htop : 0 < top) (i : Nat) :
    thresholdRowOffset top i < thresholdRowOffset top (i + 1) := by
  rw [thresholdRowOffset_succ]
  have hwidth : 0 < min (i + 1) top := by omega
  omega

/-- A cell's within-row rank lies before the next row offset. -/
theorem thresholdCell_lt_nextRow
    {top i j : Nat} (hj : j < min (i + 1) top) :
    thresholdRowOffset top i + j < thresholdRowOffset top (i + 1) := by
  rw [thresholdRowOffset_succ]
  omega

/-- A coarse bound sufficient to place every concrete constructor below the
global raw-variable limit. -/
theorem thresholdRowOffset_le_mul (top i : Nat) :
    thresholdRowOffset top i ≤ i * top := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [thresholdRowOffset_succ]
      calc
        thresholdRowOffset top i + min (i + 1) top ≤ i * top + top :=
          Nat.add_le_add ih (min_le_right _ _)
        _ = (i + 1) * top := by simp [Nat.add_mul]

/-- Row offsets are monotone in the row index. -/
theorem thresholdRowOffset_mono (top : Nat) {i k : Nat} (hik : i ≤ k) :
    thresholdRowOffset top i ≤ thresholdRowOffset top k := by
  induction k generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      exact le_rfl
  | succ k ih =>
      by_cases hi : i ≤ k
      · exact (ih hi).trans (by
          rw [thresholdRowOffset_succ]
          omega)
      · have hi : i = k + 1 := by omega
        subst i
        exact le_rfl

/-- Row-major threshold-cell ranks are injective on valid bounded cells. -/
theorem thresholdCellRank_injective
    {top i j k l : Nat}
    (hj : j < min (i + 1) top) (hl : l < min (k + 1) top)
    (heq : thresholdRowOffset top i + j =
      thresholdRowOffset top k + l) :
    i = k ∧ j = l := by
  by_cases hik : i = k
  · subst k
    exact ⟨rfl, by omega⟩
  · have horder : i < k ∨ k < i := by omega
    rcases horder with hik' | hki'
    · have hnext := thresholdCell_lt_nextRow hj
      have hrows := thresholdRowOffset_mono top (show i + 1 ≤ k by omega)
      omega
    · have hnext := thresholdCell_lt_nextRow hl
      have hrows := thresholdRowOffset_mono top (show k + 1 ≤ i by omega)
      omega

/-- Once the row cap has been reached, every later row has constant width. -/
theorem thresholdRowOffset_add_of_le
    {top i : Nat} (hitop : top ≤ i) (n : Nat) :
    thresholdRowOffset top (i + n) =
      thresholdRowOffset top i + n * top := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.add_succ, thresholdRowOffset_succ, ih]
      have hmin : min (i + n + 1) top = top := by
        rw [min_eq_right]
        omega
      rw [hmin]
      simp [Nat.add_mul, Nat.add_assoc]

/-- Exact terminal offset of the selected-at-least-six table. -/
theorem thresholdRowOffset_six_terminal :
    thresholdRowOffset 6 1560 = 9345 := by
  rw [show 1560 = 6 + 1554 by omega,
    thresholdRowOffset_add_of_le (show 6 ≤ 6 by omega)]
  norm_num [thresholdRowOffset]

/-- Exact terminal offset of each exact-four column table. -/
theorem thresholdRowOffset_five_terminal :
    thresholdRowOffset 5 640 = 3190 := by
  rw [show 640 = 5 + 635 by omega,
    thresholdRowOffset_add_of_le (show 5 ≤ 5 by omega)]
  norm_num [thresholdRowOffset]

/-- The exact finite propositional namespace of the mask-63 generator.
Threshold row and column indices are zero-based. -/
inductive Var where
  | primary : Fin 1560 → Var
  | edgePrefix : Fin 15 → Fin 260 → Var
  | selectedCell : (i : Fin 1560) → Fin (min (i.val + 1) 6) → Var
  | columnCell : Fin 6 → (i : Fin 640) → Fin (min (i.val + 1) 5) → Var
  | negativeGuard : Fin 420 → Var
  | positiveGuard : Fin 108 → Var
  deriving DecidableEq, Fintype

/-- Local zero-based rank of a selected-threshold cell. -/
def selectedRank (i : Fin 1560) (j : Fin (min (i.val + 1) 6)) : Nat :=
  thresholdRowOffset 6 i.val + j.val

/-- Local zero-based rank of a column-threshold cell. -/
def columnRank (i : Fin 640) (j : Fin (min (i.val + 1) 5)) : Nat :=
  thresholdRowOffset 5 i.val + j.val

theorem selectedRank_lt
    (i : Fin 1560) (j : Fin (min (i.val + 1) 6)) :
    selectedRank i j < 9345 := by
  have hcell := thresholdCell_lt_nextRow j.isLt
  have hmono := thresholdRowOffset_mono 6
    (show i.val + 1 ≤ 1560 by omega)
  rw [thresholdRowOffset_six_terminal] at hmono
  exact lt_of_lt_of_le hcell hmono

theorem columnRank_lt
    (i : Fin 640) (j : Fin (min (i.val + 1) 5)) :
    columnRank i j < 3190 := by
  have hcell := thresholdCell_lt_nextRow j.isLt
  have hmono := thresholdRowOffset_mono 5
    (show i.val + 1 ≤ 640 by omega)
  rw [thresholdRowOffset_five_terminal] at hmono
  exact lt_of_lt_of_le hcell hmono

/-- Equality of selected-cell ranks identifies the dependent cell indices. -/
theorem selectedCell_eq_of_rank_eq
    (i : Fin 1560) (j : Fin (min (i.val + 1) 6))
    (k : Fin 1560) (l : Fin (min (k.val + 1) 6))
    (h : selectedRank i j = selectedRank k l) :
    Var.selectedCell i j = Var.selectedCell k l := by
  rcases thresholdCellRank_injective j.isLt l.isLt h with ⟨hi, hj⟩
  have hiFin : i = k := Fin.ext hi
  subst k
  have hjFin : j = l := Fin.ext hj
  subst l
  rfl

/-- Equality of column-cell ranks identifies the dependent row and cell. -/
theorem columnCell_eq_of_rank_eq
    (v : Fin 6)
    (i : Fin 640) (j : Fin (min (i.val + 1) 5))
    (k : Fin 640) (l : Fin (min (k.val + 1) 5))
    (h : columnRank i j = columnRank k l) :
    Var.columnCell v i j = Var.columnCell v k l := by
  rcases thresholdCellRank_injective j.isLt l.isLt h with ⟨hi, hj⟩
  have hiFin : i = k := Fin.ext hi
  subst k
  have hjFin : j = l := Fin.ext hj
  subst l
  rfl

/-- Exact zero-based raw SAT variable number.  Adding one gives the DIMACS
number in the audited mask-63 ledger. -/
def rawCode : Var → Nat
  | .primary i => i.val
  | .edgePrefix e r => 1560 + 260 * e.val + r.val
  | .selectedCell i j => 5460 + thresholdRowOffset 6 i.val + j.val
  | .columnCell v i j =>
      14805 + 3190 * v.val + thresholdRowOffset 5 i.val + j.val
  | .negativeGuard k => 33945 + k.val
  | .positiveGuard k => 34365 + k.val

@[simp] theorem rawCode_primary (i : Fin 1560) :
    rawCode (.primary i) = i.val := rfl

@[simp] theorem rawCode_edgePrefix (e : Fin 15) (r : Fin 260) :
    rawCode (.edgePrefix e r) = 1560 + 260 * e.val + r.val := rfl

@[simp] theorem rawCode_selectedCell
    (i : Fin 1560) (j : Fin (min (i.val + 1) 6)) :
    rawCode (.selectedCell i j) =
      5460 + thresholdRowOffset 6 i.val + j.val := rfl

@[simp] theorem rawCode_columnCell
    (v : Fin 6) (i : Fin 640) (j : Fin (min (i.val + 1) 5)) :
    rawCode (.columnCell v i j) =
      14805 + 3190 * v.val + thresholdRowOffset 5 i.val + j.val := rfl

@[simp] theorem rawCode_negativeGuard (k : Fin 420) :
    rawCode (.negativeGuard k) = 33945 + k.val := rfl

@[simp] theorem rawCode_positiveGuard (k : Fin 108) :
    rawCode (.positiveGuard k) = 34365 + k.val := rfl

/-- Every constructor maps into the exact raw namespace's ambient interval. -/
theorem rawCode_lt (v : Var) : rawCode v < 34473 := by
  cases v with
  | primary i =>
      simp only [rawCode]
      omega
  | edgePrefix e r =>
      simp only [rawCode]
      omega
  | selectedCell i j =>
      simp only [rawCode]
      have hoff := thresholdRowOffset_le_mul 6 i.val
      omega
  | columnCell v i j =>
      simp only [rawCode]
      have hoff := thresholdRowOffset_le_mul 5 i.val
      omega
  | negativeGuard k =>
      simp only [rawCode]
      omega
  | positiveGuard k =>
      simp only [rawCode]
      omega

/-- The exact raw code packaged with its certified global bound. -/
def rawFinCode (v : Var) : Fin 34473 :=
  ⟨rawCode v, rawCode_lt v⟩

/-- Constructor-block index in the serialized variable namespace. -/
def blockIndex : Var → Nat
  | .primary _ => 0
  | .edgePrefix _ _ => 1
  | .selectedCell _ _ => 2
  | .columnCell _ _ _ => 3
  | .negativeGuard _ => 4
  | .positiveGuard _ => 5

/-- Exact half-open interval occupied by each constructor block. -/
def blockInterval : Nat → Nat × Nat
  | 0 => (0, 1560)
  | 1 => (1560, 5460)
  | 2 => (5460, 14805)
  | 3 => (14805, 33945)
  | 4 => (33945, 34365)
  | _ => (34365, 34473)

theorem rawCode_mem_block (v : Var) :
    (blockInterval (blockIndex v)).1 ≤ rawCode v ∧
      rawCode v < (blockInterval (blockIndex v)).2 := by
  cases v with
  | primary i =>
      simp [blockIndex, blockInterval, rawCode]
  | edgePrefix e r =>
      simp only [blockIndex, blockInterval, rawCode]
      omega
  | selectedCell i j =>
      have hrank := selectedRank_lt i j
      simp only [blockIndex, blockInterval, rawCode, selectedRank] at *
      omega
  | columnCell v i j =>
      have hrank := columnRank_lt i j
      simp only [blockIndex, blockInterval, rawCode, columnRank] at *
      omega
  | negativeGuard k =>
      simp only [blockIndex, blockInterval, rawCode]
      omega
  | positiveGuard k =>
      simp only [blockIndex, blockInterval, rawCode]
      omega

/-- Equal raw codes must lie in the same disjoint constructor block. -/
theorem blockIndex_eq_of_rawCode_eq {v w : Var}
    (h : rawCode v = rawCode w) : blockIndex v = blockIndex w := by
  have hv := rawCode_mem_block v
  have hw := rawCode_mem_block w
  cases v <;> cases w <;>
    simp only [blockIndex, blockInterval] at hv hw ⊢ <;> omega

theorem primary_eq_of_code_eq
    (i k : Fin 1560) (h : rawCode (.primary i) = rawCode (.primary k)) :
    Var.primary i = Var.primary k := by
  congr 1
  apply Fin.ext
  simpa only [rawCode] using h

theorem edgePrefix_eq_of_code_eq
    (e f : Fin 15) (r s : Fin 260)
    (h : rawCode (.edgePrefix e r) = rawCode (.edgePrefix f s)) :
    Var.edgePrefix e r = Var.edgePrefix f s := by
  have he : e = f := Fin.ext (by
    simp only [rawCode] at h
    omega)
  subst f
  have hr : r = s := Fin.ext (by
    simp only [rawCode] at h
    omega)
  subst s
  rfl

theorem selectedCell_eq_of_code_eq
    (i : Fin 1560) (j : Fin (min (i.val + 1) 6))
    (k : Fin 1560) (l : Fin (min (k.val + 1) 6))
    (h : rawCode (.selectedCell i j) = rawCode (.selectedCell k l)) :
    Var.selectedCell i j = Var.selectedCell k l := by
  apply selectedCell_eq_of_rank_eq
  simp only [rawCode, selectedRank] at h ⊢
  omega

theorem columnVar_eq_of_code_eq
    (v w : Fin 6)
    (i : Fin 640) (j : Fin (min (i.val + 1) 5))
    (k : Fin 640) (l : Fin (min (k.val + 1) 5))
    (h : rawCode (.columnCell v i j) = rawCode (.columnCell w k l)) :
    Var.columnCell v i j = Var.columnCell w k l := by
  have hij := columnRank_lt i j
  have hkl := columnRank_lt k l
  have hranks :
      3190 * v.val + columnRank i j =
        3190 * w.val + columnRank k l := by
    have h' :
        14805 + (3190 * v.val + columnRank i j) =
          14805 + (3190 * w.val + columnRank k l) := by
      simpa only [rawCode, columnRank, Nat.add_assoc] using h
    exact Nat.add_left_cancel h'
  have hv : v = w := Fin.ext (by
    omega)
  subst w
  apply columnCell_eq_of_rank_eq
  exact Nat.add_left_cancel hranks

theorem negativeGuard_eq_of_code_eq
    (i k : Fin 420)
    (h : rawCode (.negativeGuard i) = rawCode (.negativeGuard k)) :
    Var.negativeGuard i = Var.negativeGuard k := by
  congr 1
  apply Fin.ext
  simp only [rawCode] at h
  omega

theorem positiveGuard_eq_of_code_eq
    (i k : Fin 108)
    (h : rawCode (.positiveGuard i) = rawCode (.positiveGuard k)) :
    Var.positiveGuard i = Var.positiveGuard k := by
  congr 1
  apply Fin.ext
  simp only [rawCode] at h
  omega

/-- The exact concrete numbering has no collisions. -/
theorem rawCode_injective : Function.Injective rawCode := by
  intro v w h
  have hblock := blockIndex_eq_of_rawCode_eq h
  cases v <;> cases w <;> simp only [blockIndex] at hblock
  all_goals try omega
  all_goals first
    | exact primary_eq_of_code_eq _ _ h
    | exact edgePrefix_eq_of_code_eq _ _ _ _ h
    | exact selectedCell_eq_of_code_eq _ _ _ _ h
    | exact columnVar_eq_of_code_eq _ _ _ _ _ _ h
    | exact negativeGuard_eq_of_code_eq _ _ h
    | exact positiveGuard_eq_of_code_eq _ _ h

/- The finite constructor namespace has exactly the pinned DIMACS variable
count.  This is a kernel-reduced finite decision, not native code. -/
set_option maxHeartbeats 0 in
set_option maxRecDepth 1000000 in
theorem card_var : Fintype.card Var = 34473 := by
  decide

theorem rawFinCode_injective : Function.Injective rawFinCode := by
  intro v w h
  apply rawCode_injective
  exact congrArg Fin.val h

/-- The exact code is a bijection with all raw variables `0,...,34472`. -/
theorem rawFinCode_bijective : Function.Bijective rawFinCode := by
  apply (Fintype.bijective_iff_injective_and_card rawFinCode).2
  refine ⟨rawFinCode_injective, ?_⟩
  rw [card_var]
  simp

theorem rawFinCode_surjective : Function.Surjective rawFinCode :=
  rawFinCode_bijective.2

end TotalColoring.MinSixConcreteVar
