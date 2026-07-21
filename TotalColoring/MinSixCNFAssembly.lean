import TotalColoring.MinSixThresholdEncoder

/-!
# Formula assembly for the minimum-six CNF bridge

This file assembles the already checked Sinz clause shapes into one typed CNF
formula.  It also models the generator's two distinct guard namespaces and
assembles its negative-family, positive-family, and role blocks in their
literal order.  The canonical guard extension satisfies the assembled guard
CNF whenever every listed role has the required semantic family implication.

The declarations remain generic in the primary and guard-variable types.
They do not enumerate cage descriptors, lift the separate encodings into one
concrete variable type, assign DIMACS integers, identify serialized CNF bytes,
validate LRAT evidence, or state a graph-theoretic impossibility.
-/

namespace TotalColoring.MinSixCNFCore

namespace Sinz

/-- The complete typed Sinz block for inputs `0, ..., n + 1`.

The formula consists of the initial implication, the three-clause step block
at every index in `List.range n`, and the final mutex clause. -/
def blockCNF {Primary : Type*} (x : Nat → Primary) (n : Nat) :
    Formula (SinzVar Primary) :=
  implicationClause (.primary (x 0)) (.prefix 0) ::
    ((List.range n).flatMap (stepCNF x) ++
      [mutexClause (.primary (x (n + 1))) (.prefix n)])

/-- Formula satisfaction of the assembled block is exactly the earlier
field-wise Sinz satisfaction predicate. -/
@[simp] theorem satisfies_blockCNF_iff
    {Primary : Type*} (τ : Assignment (SinzVar Primary))
    (x : Nat → Primary) (n : Nat) :
    (blockCNF x n).Satisfied τ ↔ Satisfied τ x n := by
  constructor
  · intro h
    refine ⟨h _ (by simp [blockCNF]), ?_, h _ (by simp [blockCNF])⟩
    intro i hi C hC
    apply h C
    simp only [blockCNF, List.mem_cons, List.mem_append]
    exact Or.inr <| Or.inl <|
      List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hC⟩
  · intro h C hC
    simp only [blockCNF, List.mem_cons, List.mem_append,
      List.not_mem_nil, or_false] at hC
    rcases hC with hC | hC
    · subst C
      exact h.first
    · rcases hC with hC | hC
      · rcases List.mem_flatMap.mp hC with ⟨i, hi, hC⟩
        exact h.steps i (List.mem_range.mp hi) C hC
      · subst C
        exact h.last

/-- The assembled Sinz formula has a primary-preserving auxiliary extension
exactly when the inputs are at most one. -/
theorem exists_satisfying_blockCNF_extension_iff
    {Primary : Type*} (σ : Assignment Primary) (x : Nat → Primary)
    (n : Nat) :
    (∃ τ : Assignment (SinzVar Primary),
        (∀ v, τ (.primary v) = σ v) ∧
          (blockCNF x n).Satisfied τ) ↔
      AtMostOneThrough σ x (n + 1) := by
  simpa using exists_satisfying_extension_iff σ x n

end Sinz

/-! ## One-sided family guards and guarded role clauses -/

namespace Guard

/-- Variables in the guarded block: primaries and two deliberately distinct
guard namespaces.  The generator allocates the two guard sorts separately,
even when their underlying member families happen to be extensionally equal. -/
inductive Var (Primary NegGuard PosGuard : Type*) where
  | primary : Primary → Var Primary NegGuard PosGuard
  | negGuard : NegGuard → Var Primary NegGuard PosGuard
  | posGuard : PosGuard → Var Primary NegGuard PosGuard
  deriving DecidableEq

/-- The four guard indices used by one compressed endpoint-role clause. -/
structure Role (NegGuard PosGuard : Type*) where
  activation : NegGuard
  firstDonor : NegGuard
  secondDonor : NegGuard
  sameDonor : PosGuard
  deriving DecidableEq

/-- A family meets a primary assignment when it contains a selected member. -/
def Meets {Primary : Type*}
    (σ : Assignment Primary) (xs : List Primary) : Prop :=
  ∃ x ∈ xs, σ x = true

/-- Canonical Boolean disjunction of all primary values in a family. -/
def familyValue {Primary : Type*}
    (σ : Assignment Primary) (xs : List Primary) : Bool :=
  xs.any σ

/-- Canonically extend primary values by the disjunction of each guard's
member family. -/
def extension {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary) :
    Assignment (Var Primary NegGuard PosGuard)
  | .primary x => σ x
  | .negGuard g => familyValue σ (negMembers g)
  | .posGuard g => familyValue σ (posMembers g)

@[simp] theorem extension_primary
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (x : Primary) :
    extension σ negMembers posMembers (.primary x) = σ x := rfl

@[simp] theorem extension_negGuard
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (g : NegGuard) :
    extension σ negMembers posMembers (.negGuard g) =
      familyValue σ (negMembers g) := rfl

@[simp] theorem extension_posGuard
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (g : PosGuard) :
    extension σ negMembers posMembers (.posGuard g) =
      familyValue σ (posMembers g) := rfl

/-- The canonical family value is true exactly when the family meets the
primary assignment. -/
@[simp] theorem familyValue_eq_true_iff
    {Primary : Type*} (σ : Assignment Primary) (xs : List Primary) :
    familyValue σ xs = true ↔ Meets σ xs := by
  induction xs with
  | nil =>
      simp [familyValue, Meets]
  | cons x xs ih =>
      change
        (σ x || familyValue σ xs) = true ↔ Meets σ (x :: xs)
      rw [Bool.or_eq_true, ih]
      simp [Meets]

/-- For a negative family guard, each selected member forces the guard. -/
def negativeFamilyCNF
    {Primary NegGuard PosGuard : Type*}
    (xs : List Primary) (g : NegGuard) :
    Formula (Var Primary NegGuard PosGuard) :=
  xs.map fun x => implicationClause (.primary x) (.negGuard g)

/-- For a positive family guard, a true guard forces some selected member. -/
def positiveFamilyClause
    {Primary NegGuard PosGuard : Type*}
    (xs : List Primary) (g : PosGuard) :
    Clause (Var Primary NegGuard PosGuard) :=
  .negative (.posGuard g) ::
    xs.map fun x => .positive (.primary x)

/-- The compressed role clause `not z or not first or not second or same`. -/
def roleClause
    {Primary NegGuard PosGuard : Type*}
    (r : Role NegGuard PosGuard) :
    Clause (Var Primary NegGuard PosGuard) :=
  [.negative (.negGuard r.activation),
    .negative (.negGuard r.firstDonor),
    .negative (.negGuard r.secondDonor),
    .positive (.posGuard r.sameDonor)]

/-- Exact semantics of all member-to-negative-guard implications. -/
@[simp] theorem satisfies_negativeFamilyCNF_iff
    {Primary NegGuard PosGuard : Type*}
    (τ : Assignment (Var Primary NegGuard PosGuard))
    (xs : List Primary) (g : NegGuard) :
    (negativeFamilyCNF xs g).Satisfied τ ↔
      ∀ x ∈ xs,
        τ (.primary x) = true → τ (.negGuard g) = true := by
  constructor
  · intro h x hx hselected
    have hClause := h _ (List.mem_map.mpr ⟨x, hx, rfl⟩)
    exact
      (satisfies_implicationClause_iff τ _ _).1 hClause hselected
  · intro h C hC
    rcases List.mem_map.mp hC with ⟨x, hx, rfl⟩
    exact
      (satisfies_implicationClause_iff τ _ _).2 (h x hx)

/-- Exact one-sided semantics of a positive-family clause.  In particular,
an empty member family produces the unit clause refuting its guard. -/
@[simp] theorem satisfies_positiveFamilyClause_iff
    {Primary NegGuard PosGuard : Type*}
    (τ : Assignment (Var Primary NegGuard PosGuard))
    (xs : List Primary) (g : PosGuard) :
    (positiveFamilyClause xs g).Satisfied τ ↔
      (τ (.posGuard g) = true →
        ∃ x ∈ xs, τ (.primary x) = true) := by
  cases hg : τ (.posGuard g) <;>
    simp [positiveFamilyClause, Clause.Satisfied, Literal.eval, hg]

/-- Exact propositional semantics of the four-literal role clause. -/
@[simp] theorem satisfies_roleClause_iff
    {Primary NegGuard PosGuard : Type*}
    (τ : Assignment (Var Primary NegGuard PosGuard))
    (r : Role NegGuard PosGuard) :
    (roleClause r).Satisfied τ ↔
      (τ (.negGuard r.activation) = true →
        τ (.negGuard r.firstDonor) = true →
        τ (.negGuard r.secondDonor) = true →
        τ (.posGuard r.sameDonor) = true) := by
  cases hz : τ (.negGuard r.activation) <;>
    cases hf : τ (.negGuard r.firstDonor) <;>
    cases hs : τ (.negGuard r.secondDonor) <;>
    cases hm : τ (.posGuard r.sameDonor) <;>
    simp [roleClause, Clause.Satisfied, Literal.eval, hz, hf, hs, hm]

/-- Family implication required for a canonical assignment to satisfy one
guarded role clause. -/
def SemanticRole
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (r : Role NegGuard PosGuard) : Prop :=
  Meets σ (negMembers r.activation) →
    Meets σ (negMembers r.firstDonor) →
    Meets σ (negMembers r.secondDonor) →
    Meets σ (posMembers r.sameDonor)

/-- The canonical assignment satisfies every negative-family implication. -/
theorem extension_satisfies_negativeFamilyCNF
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (g : NegGuard) :
    (negativeFamilyCNF (negMembers g) g).Satisfied
      (extension σ negMembers posMembers) := by
  rw [satisfies_negativeFamilyCNF_iff]
  intro x hx hselected
  change σ x = true at hselected
  change familyValue σ (negMembers g) = true
  exact
    (familyValue_eq_true_iff σ (negMembers g)).2
      ⟨x, hx, hselected⟩

/-- The canonical assignment satisfies every positive-family clause. -/
theorem extension_satisfies_positiveFamilyClause
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (g : PosGuard) :
    (positiveFamilyClause (posMembers g) g).Satisfied
      (extension σ negMembers posMembers) := by
  rw [satisfies_positiveFamilyClause_iff]
  intro hg
  change familyValue σ (posMembers g) = true at hg
  rcases (familyValue_eq_true_iff σ (posMembers g)).1 hg with
    ⟨x, hx, hselected⟩
  refine ⟨x, hx, ?_⟩
  change σ x = true
  exact hselected

/-- On the canonical extension, role-clause satisfaction is precisely the
corresponding semantic family implication. -/
@[simp] theorem extension_satisfies_roleClause_iff
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (r : Role NegGuard PosGuard) :
    (roleClause r).Satisfied (extension σ negMembers posMembers) ↔
      SemanticRole σ negMembers posMembers r := by
  rw [satisfies_roleClause_iff]
  simp only [extension, familyValue_eq_true_iff, SemanticRole]

/-- All negative-family blocks, in the supplied guard order. -/
def negativeFamiliesCNF
    {Primary NegGuard PosGuard : Type*}
    (guards : List NegGuard)
    (negMembers : NegGuard → List Primary) :
    Formula (Var Primary NegGuard PosGuard) :=
  guards.flatMap fun g => negativeFamilyCNF (negMembers g) g

/-- All positive-family clauses, in the supplied guard order. -/
def positiveFamiliesCNF
    {Primary NegGuard PosGuard : Type*}
    (guards : List PosGuard)
    (posMembers : PosGuard → List Primary) :
    Formula (Var Primary NegGuard PosGuard) :=
  guards.map fun g => positiveFamilyClause (posMembers g) g

/-- All compressed role clauses, in the supplied role order. -/
def roleClausesCNF
    {Primary NegGuard PosGuard : Type*}
    (roles : List (Role NegGuard PosGuard)) :
    Formula (Var Primary NegGuard PosGuard) :=
  roles.map roleClause

/-- The guarded CNF in the exact three-block order used by the generator. -/
def guardedCNF
    {Primary NegGuard PosGuard : Type*}
    (negGuards : List NegGuard)
    (posGuards : List PosGuard)
    (roles : List (Role NegGuard PosGuard))
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary) :
    Formula (Var Primary NegGuard PosGuard) :=
  negativeFamiliesCNF negGuards negMembers ++
    (positiveFamiliesCNF posGuards posMembers ++ roleClausesCNF roles)

theorem extension_satisfies_negativeFamiliesCNF
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (guards : List NegGuard) :
    (negativeFamiliesCNF guards negMembers).Satisfied
      (extension σ negMembers posMembers) := by
  intro C hC
  rcases List.mem_flatMap.mp hC with ⟨g, _, hC⟩
  exact extension_satisfies_negativeFamilyCNF
    σ negMembers posMembers g C hC

theorem extension_satisfies_positiveFamiliesCNF
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (guards : List PosGuard) :
    (positiveFamiliesCNF guards posMembers).Satisfied
      (extension σ negMembers posMembers) := by
  intro C hC
  rcases List.mem_map.mp hC with ⟨g, _, rfl⟩
  exact extension_satisfies_positiveFamilyClause
    σ negMembers posMembers g

theorem extension_satisfies_roleClausesCNF
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (roles : List (Role NegGuard PosGuard))
    (hroles : ∀ r ∈ roles, SemanticRole σ negMembers posMembers r) :
    (roleClausesCNF roles).Satisfied
      (extension σ negMembers posMembers) := by
  intro C hC
  rcases List.mem_map.mp hC with ⟨r, hr, rfl⟩
  exact (extension_satisfies_roleClause_iff
    σ negMembers posMembers r).2 (hroles r hr)

/-- A semantic family implication for every listed role gives a canonical
satisfying assignment of the complete guarded block.  This is the generic
seam needed by a future blocker-to-CNF theorem. -/
theorem extension_satisfies_guardedCNF
    {Primary NegGuard PosGuard : Type*}
    (σ : Assignment Primary)
    (negMembers : NegGuard → List Primary)
    (posMembers : PosGuard → List Primary)
    (negGuards : List NegGuard)
    (posGuards : List PosGuard)
    (roles : List (Role NegGuard PosGuard))
    (hroles : ∀ r ∈ roles, SemanticRole σ negMembers posMembers r) :
    (guardedCNF negGuards posGuards roles negMembers posMembers).Satisfied
      (extension σ negMembers posMembers) := by
  rw [guardedCNF, Formula.satisfied_append_iff,
    Formula.satisfied_append_iff]
  exact ⟨
    extension_satisfies_negativeFamiliesCNF
      σ negMembers posMembers negGuards,
    extension_satisfies_positiveFamiliesCNF
      σ negMembers posMembers posGuards,
    extension_satisfies_roleClausesCNF
      σ negMembers posMembers roles hroles⟩

end Guard

end TotalColoring.MinSixCNFCore
