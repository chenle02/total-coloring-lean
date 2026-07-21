import Mathlib

/-!
# Propositional core for the minimum-six CNF bridge

This file gives a small, solver-independent semantics for CNF formulas and
checks the two auxiliary-variable encodings used by the minimum-six generator:

* the Sinz prefix encoding of at-most-one; and
* the threshold recurrence
  `t(i + 1, j + 1) = t(i, j + 1) || (x(i) && t(i, j))`.

The statements are generic in the primary-variable type and construct all
auxiliary Boolean values from a primary assignment.  They do not identify a
serialized DIMACS variable, enumerate descriptors, import an LRAT proof, or
state that any minimum-six branch is unsatisfiable.
-/

namespace TotalColoring.MinSixCNFCore

/-- A total Boolean assignment to propositional variables. -/
abbrev Assignment (Var : Type*) := Var → Bool

/-- A signed propositional variable. -/
inductive Literal (Var : Type*) where
  | positive : Var → Literal Var
  | negative : Var → Literal Var
  deriving DecidableEq

/-- Boolean evaluation of one signed literal. -/
def Literal.eval {Var : Type*} (σ : Assignment Var) : Literal Var → Bool
  | .positive v => σ v
  | .negative v => !(σ v)

/-- A disjunctive clause. -/
abbrev Clause (Var : Type*) := List (Literal Var)

/-- A conjunctive list of clauses. -/
abbrev Formula (Var : Type*) := List (Clause Var)

namespace Clause

/-- A clause is satisfied when one of its literals evaluates to true. -/
def Satisfied {Var : Type*} (σ : Assignment Var) (C : Clause Var) : Prop :=
  ∃ l ∈ C, l.eval σ = true

end Clause

namespace Formula

/-- A CNF formula is satisfied when each of its clauses is satisfied. -/
def Satisfied {Var : Type*} (σ : Assignment Var) (F : Formula Var) : Prop :=
  ∀ C ∈ F, C.Satisfied σ

end Formula

/-- The clause expressing `a → b`. -/
def implicationClause {Var : Type*} (a b : Var) : Clause Var :=
  [.negative a, .positive b]

/-- The clause expressing that `a` and `b` are not simultaneously true. -/
def mutexClause {Var : Type*} (a b : Var) : Clause Var :=
  [.negative a, .negative b]

@[simp] theorem satisfies_implicationClause_iff
    {Var : Type*} (σ : Assignment Var) (a b : Var) :
    (implicationClause a b).Satisfied σ ↔
      (σ a = true → σ b = true) := by
  cases ha : σ a <;> cases hb : σ b <;>
    simp [Clause.Satisfied, implicationClause, Literal.eval, ha, hb]

@[simp] theorem satisfies_mutexClause_iff
    {Var : Type*} (σ : Assignment Var) (a b : Var) :
    (mutexClause a b).Satisfied σ ↔
      ¬(σ a = true ∧ σ b = true) := by
  cases ha : σ a <;> cases hb : σ b <;>
    simp [Clause.Satisfied, mutexClause, Literal.eval, ha, hb]

/-! ## The four threshold recurrence clause shapes -/

/-- The two clauses used when the threshold recurrence reduces to `y ↔ x`. -/
def copyCNF {Var : Type*} (x y : Var) : Formula Var :=
  [implicationClause x y, implicationClause y x]

/-- The three clauses used when the recurrence reduces to `y ↔ x ∧ b`. -/
def andCNF {Var : Type*} (x b y : Var) : Formula Var :=
  [[.negative x, .negative b, .positive y],
    implicationClause y x,
    implicationClause y b]

/-- The three clauses used when the recurrence reduces to `y ↔ a ∨ x`. -/
def orCNF {Var : Type*} (a x y : Var) : Formula Var :=
  [implicationClause a y,
    implicationClause x y,
    [.negative y, .positive a, .positive x]]

/-- The four clauses for `y ↔ a ∨ (x ∧ b)`. -/
def recurrenceCNF {Var : Type*} (a x b y : Var) : Formula Var :=
  [implicationClause a y,
    [.negative x, .negative b, .positive y],
    [.negative y, .positive a, .positive x],
    [.negative y, .positive a, .positive b]]

@[simp] theorem satisfies_copyCNF_iff
    {Var : Type*} (σ : Assignment Var) (x y : Var) :
    (copyCNF x y).Satisfied σ ↔ σ y = σ x := by
  cases hx : σ x <;> cases hy : σ y <;>
    simp [Formula.Satisfied, Clause.Satisfied, copyCNF,
      implicationClause, Literal.eval, hx, hy]

@[simp] theorem satisfies_andCNF_iff
    {Var : Type*} (σ : Assignment Var) (x b y : Var) :
    (andCNF x b y).Satisfied σ ↔ σ y = (σ x && σ b) := by
  cases hx : σ x <;> cases hb : σ b <;> cases hy : σ y <;>
    simp [Formula.Satisfied, Clause.Satisfied, andCNF,
      implicationClause, Literal.eval, hx, hb, hy]

@[simp] theorem satisfies_orCNF_iff
    {Var : Type*} (σ : Assignment Var) (a x y : Var) :
    (orCNF a x y).Satisfied σ ↔ σ y = (σ a || σ x) := by
  cases ha : σ a <;> cases hx : σ x <;> cases hy : σ y <;>
    simp [Formula.Satisfied, Clause.Satisfied, orCNF,
      implicationClause, Literal.eval, ha, hx, hy]

/-- Soundness and completeness of the four-clause threshold recurrence. -/
@[simp] theorem satisfies_recurrenceCNF_iff
    {Var : Type*} (σ : Assignment Var) (a x b y : Var) :
    (recurrenceCNF a x b y).Satisfied σ ↔
      σ y = (σ a || (σ x && σ b)) := by
  cases ha : σ a <;> cases hx : σ x <;>
    cases hb : σ b <;> cases hy : σ y <;>
    simp [Formula.Satisfied, Clause.Satisfied, recurrenceCNF,
      implicationClause, Literal.eval, ha, hx, hb, hy]

/-! ## Canonical threshold auxiliaries -/

/-- Variables in a threshold extension: old primaries or table entries. -/
inductive ThresholdVar (Primary : Type*) where
  | primary : Primary → ThresholdVar Primary
  | auxiliary : Nat → Nat → ThresholdVar Primary

namespace Threshold

/-- Canonical truth value of “at least `j` among the first `i` inputs”. -/
def value {Primary : Type*}
    (σ : Assignment Primary) (x : Nat → Primary) : Nat → Nat → Bool
  | _, 0 => true
  | 0, _ + 1 => false
  | i + 1, j + 1 => value σ x i (j + 1) || (σ (x i) && value σ x i j)

/-- Extend a primary assignment by all canonical threshold-table values. -/
def extension {Primary : Type*}
    (σ : Assignment Primary) (x : Nat → Primary) :
    Assignment (ThresholdVar Primary)
  | .primary v => σ v
  | .auxiliary i j => value σ x i j

@[simp] theorem extension_primary
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (v : Primary) :
    extension σ x (.primary v) = σ v := rfl

@[simp] theorem extension_auxiliary
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (i j : Nat) :
    extension σ x (.auxiliary i j) = value σ x i j := rfl

@[simp] theorem value_zero
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (i : Nat) :
    value σ x i 0 = true := by
  cases i <;> rfl

@[simp] theorem value_zero_succ
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (j : Nat) :
    value σ x 0 (j + 1) = false := rfl

@[simp] theorem value_succ_succ
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (i j : Nat) :
    value σ x (i + 1) (j + 1) =
      (value σ x i (j + 1) || (σ (x i) && value σ x i j)) := rfl

/-- No prefix of length `i` reaches a threshold strictly larger than `i`. -/
theorem value_eq_false_of_lt
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    {i j : Nat} (hij : i < j) :
    value σ x i j = false := by
  induction i generalizing j with
  | zero =>
      cases j with
      | zero => omega
      | succ j => rfl
  | succ i ih =>
      cases j with
      | zero => omega
      | succ j =>
          simp only [value_succ_succ]
          rw [ih (by omega), ih (by omega)]
          simp

/-- The first generated table cell uses the two-clause copy case. -/
theorem extension_satisfies_first
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary) :
    (copyCNF (.primary (x 0)) (.auxiliary 1 1)).Satisfied
      (extension σ x) := by
  rw [satisfies_copyCNF_iff]
  simp [value]

/-- The `j = i` boundary uses `y ↔ x ∧ b` because the absent `a` value is
false.  The generator invokes this shape for `1 < i`. -/
theorem extension_satisfies_diagonal
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (i : Nat) :
    (andCNF (.primary (x i)) (.auxiliary i i)
        (.auxiliary (i + 1) (i + 1))).Satisfied (extension σ x) := by
  rw [satisfies_andCNF_iff]
  simp [value, value_eq_false_of_lt σ x (Nat.lt_succ_self i)]

/-- The `j = 1` boundary uses `y ↔ a ∨ x` because `t(i,0)` is true. -/
theorem extension_satisfies_first_column
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (i : Nat) :
    (orCNF (.auxiliary i 1) (.primary (x i))
        (.auxiliary (i + 1) 1)).Satisfied (extension σ x) := by
  rw [satisfies_orCNF_iff]
  simp [value]

/-- Every interior table cell satisfies the generator's four-clause
recurrence.  Callers use `1 < j ≤ i`; the identity itself needs no bounds. -/
theorem extension_satisfies_recurrence
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (i j : Nat) :
    (recurrenceCNF (.auxiliary i (j + 1)) (.primary (x i))
        (.auxiliary i j) (.auxiliary (i + 1) (j + 1))).Satisfied
      (extension σ x) := by
  rw [satisfies_recurrenceCNF_iff]
  rfl

end Threshold

/-! ## Sinz at-most-one prefix clauses -/

/-- Variables in a Sinz extension: old primaries or running prefixes. -/
inductive SinzVar (Primary : Type*) where
  | primary : Primary → SinzVar Primary
  | prefix : Nat → SinzVar Primary

namespace Sinz

/-- Canonical running disjunction through input index `i`. -/
def prefixValue {Primary : Type*}
    (σ : Assignment Primary) (x : Nat → Primary) : Nat → Bool
  | 0 => σ (x 0)
  | i + 1 => prefixValue σ x i || σ (x (i + 1))

/-- Extend a primary assignment by the canonical running disjunctions. -/
def extension {Primary : Type*}
    (σ : Assignment Primary) (x : Nat → Primary) :
    Assignment (SinzVar Primary)
  | .primary v => σ v
  | .prefix i => prefixValue σ x i

/-- At most one input through `last` is true. -/
def AtMostOneThrough {Primary : Type*}
    (σ : Assignment Primary) (x : Nat → Primary) (last : Nat) : Prop :=
  ∀ ⦃i j : Nat⦄, i ≤ last → j ≤ last →
    σ (x i) = true → σ (x j) = true → i = j

/-- The three clauses emitted for one interior Sinz prefix index. -/
def stepCNF {Primary : Type*} (x : Nat → Primary) (i : Nat) :
    Formula (SinzVar Primary) :=
  [implicationClause (.primary (x (i + 1))) (.prefix (i + 1)),
    implicationClause (.prefix i) (.prefix (i + 1)),
    mutexClause (.primary (x (i + 1))) (.prefix i)]

/-- Exact semantic shape of the Sinz clauses for inputs `0, ..., n + 1` and
prefix auxiliaries `0, ..., n`. -/
structure Satisfied {Primary : Type*}
    (τ : Assignment (SinzVar Primary)) (x : Nat → Primary) (n : Nat) : Prop where
  first : (implicationClause (.primary (x 0)) (.prefix 0)).Satisfied τ
  steps : ∀ i, i < n → (stepCNF x i).Satisfied τ
  last : (mutexClause (.primary (x (n + 1))) (.prefix n)).Satisfied τ

@[simp] theorem satisfies_stepCNF_iff
    {Primary : Type*} (τ : Assignment (SinzVar Primary))
    (x : Nat → Primary) (i : Nat) :
    (stepCNF x i).Satisfied τ ↔
      ((τ (.primary (x (i + 1))) = true →
          τ (.prefix (i + 1)) = true) ∧
        (τ (.prefix i) = true → τ (.prefix (i + 1)) = true) ∧
        ¬(τ (.primary (x (i + 1))) = true ∧
          τ (.prefix i) = true)) := by
  simp [Formula.Satisfied, stepCNF]

theorem prefixValue_eq_true_iff
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (i : Nat) :
    prefixValue σ x i = true ↔
      ∃ k, k ≤ i ∧ σ (x k) = true := by
  induction i with
  | zero =>
      simp [prefixValue]
  | succ i ih =>
      simp only [prefixValue, Bool.or_eq_true, ih]
      constructor
      · rintro (⟨k, hki, hk⟩ | hi)
        · exact ⟨k, by omega, hk⟩
        · exact ⟨i + 1, le_rfl, hi⟩
      · rintro ⟨k, hki, hk⟩
        by_cases hle : k ≤ i
        · exact Or.inl ⟨k, hle, hk⟩
        · right
          have hEq : k = i + 1 := by omega
          simpa [hEq] using hk

theorem prefixValue_eq_true_of_input
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    {i k : Nat} (hik : i ≤ k) (hi : σ (x i) = true) :
    prefixValue σ x k = true := by
  exact (prefixValue_eq_true_iff σ x k).2 ⟨i, hik, hi⟩

theorem not_input_succ_and_prefix_of_atMostOne
    {Primary : Type*} {σ : Assignment Primary} {x : Nat → Primary}
    {n k : Nat} (hAMO : AtMostOneThrough σ x (n + 1)) (hk : k ≤ n) :
    ¬(σ (x (k + 1)) = true ∧ prefixValue σ x k = true) := by
  rintro ⟨hcurrent, hprefix⟩
  rcases (prefixValue_eq_true_iff σ x k).1 hprefix with ⟨i, hik, hi⟩
  have hEq : i = k + 1 := hAMO (by omega) (by omega) hi hcurrent
  omega

/-- Completeness of the full Sinz prefix block: every at-most-one primary
assignment has the canonical auxiliary extension satisfying every clause. -/
theorem extension_satisfies
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (n : Nat) (hAMO : AtMostOneThrough σ x (n + 1)) :
    Satisfied (extension σ x) x n := by
  refine ⟨?_, ?_, ?_⟩
  · rw [satisfies_implicationClause_iff]
    intro h0
    simpa [extension, prefixValue, h0]
  · intro i hi
    rw [satisfies_stepCNF_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro hcurrent
      exact prefixValue_eq_true_of_input σ x (Nat.le_refl (i + 1)) hcurrent
    · intro hprefix
      change prefixValue σ x i = true at hprefix
      change prefixValue σ x (i + 1) = true
      simp [prefixValue, hprefix]
    · exact not_input_succ_and_prefix_of_atMostOne hAMO (by omega)
  · rw [satisfies_mutexClause_iff]
    exact not_input_succ_and_prefix_of_atMostOne hAMO (Nat.le_refl n)

/-- Any satisfying Sinz block propagates a true input into every later prefix
that exists in the block. -/
theorem prefix_true_of_primary_true
    {Primary : Type*} {τ : Assignment (SinzVar Primary)}
    {x : Nat → Primary} {n i k : Nat}
    (h : Satisfied τ x n) (hik : i ≤ k) (hkn : k ≤ n)
    (hi : τ (.primary (x i)) = true) :
    τ (.prefix k) = true := by
  induction k generalizing i with
  | zero =>
      have hi0 : i = 0 := by omega
      subst i
      exact (satisfies_implicationClause_iff τ _ _).1 h.first hi
  | succ k ih =>
      have hstep := (satisfies_stepCNF_iff τ x k).1 (h.steps k (by omega))
      by_cases hEq : i = k + 1
      · subst i
        exact hstep.1 hi
      · have hik' : i ≤ k := by omega
        exact hstep.2.1 (ih hik' (by omega) hi)

/-- Soundness of the full Sinz prefix block: every satisfying extension has
at most one true primary input, regardless of how its auxiliaries were chosen. -/
theorem atMostOneThrough_of_satisfied
    {Primary : Type*} {τ : Assignment (SinzVar Primary)}
    {x : Nat → Primary} {n : Nat} (h : Satisfied τ x n) :
    AtMostOneThrough (fun v => τ (.primary v)) x (n + 1) := by
  intro i j hiBound hjBound hi hj
  rcases lt_trichotomy i j with hij | hij | hij
  · have hjPos : 0 < j := by omega
    obtain ⟨k, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hjPos)
    have hik : i ≤ k := by omega
    have hkn : k ≤ n := by omega
    have hp : τ (.prefix k) = true :=
      prefix_true_of_primary_true h hik hkn hi
    by_cases hk : k < n
    · have hstep := (satisfies_stepCNF_iff τ x k).1 (h.steps k hk)
      exact False.elim (hstep.2.2 ⟨hj, hp⟩)
    · have hEq : k = n := by omega
      subst k
      exact False.elim ((satisfies_mutexClause_iff τ _ _).1 h.last ⟨hj, hp⟩)
  · exact hij
  · have hji : j < i := hij
    have hiPos : 0 < i := by omega
    obtain ⟨k, rfl⟩ :=
      Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hiPos)
    have hjk : j ≤ k := by omega
    have hkn : k ≤ n := by omega
    have hp : τ (.prefix k) = true :=
      prefix_true_of_primary_true h hjk hkn hj
    by_cases hk : k < n
    · have hstep := (satisfies_stepCNF_iff τ x k).1 (h.steps k hk)
      exact False.elim (hstep.2.2 ⟨hi, hp⟩)
    · have hEq : k = n := by omega
      subst k
      exact False.elim ((satisfies_mutexClause_iff τ _ _).1 h.last ⟨hi, hp⟩)

/-- The Sinz block is satisfiable exactly when its primary inputs are
at-most-one; the forward direction forgets arbitrary auxiliary choices and
the reverse direction supplies the canonical prefix values. -/
theorem exists_satisfying_extension_iff
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (n : Nat) :
    (∃ τ : Assignment (SinzVar Primary),
        (∀ v, τ (.primary v) = σ v) ∧ Satisfied τ x n) ↔
      AtMostOneThrough σ x (n + 1) := by
  constructor
  · rintro ⟨τ, hprimary, hsat⟩
    have hAMO := atMostOneThrough_of_satisfied hsat
    intro i j hiBound hjBound hi hj
    apply hAMO hiBound hjBound
    · simpa [hprimary] using hi
    · simpa [hprimary] using hj
  · intro hAMO
    exact ⟨extension σ x, by intro v; rfl,
      extension_satisfies σ x n hAMO⟩

end Sinz

end TotalColoring.MinSixCNFCore
