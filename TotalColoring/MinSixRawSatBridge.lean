import Mathlib.Tactic.Sat.FromLRAT
import TotalColoring.MinSixCNFCore

/-!
# Generic bridge from typed CNF satisfaction to Mathlib's raw SAT semantics

This file supplies the proof-theoretic seam needed after an exact DIMACS
numbering has been constructed.  An injective variable code maps the typed
minimum-six literals and formulas into the `Sat.Fmla` representation consumed
by Mathlib's LRAT importer.  Every satisfying typed Boolean assignment then
induces a satisfying raw valuation.  Consequently, an LRAT-derived proof of
the empty clause rules out typed satisfaction.

The result is generic.  It does not enumerate minimum-six variables, define a
concrete DIMACS code, identify serialized bytes, import a certificate, rule out
a cage blocker, or prove a graph theorem.
-/

namespace TotalColoring.MinSixCNFCore

namespace RawSat

/-- Encode a typed literal using a zero-based SAT variable number. -/
def encodeLiteral {Var : Type*} (code : Var → Nat) :
    Literal Var → Sat.Literal
  | .positive v => .pos (code v)
  | .negative v => .neg (code v)

/-- Encode one typed clause in the same literal order. -/
def encodeClause {Var : Type*} (code : Var → Nat) (C : Clause Var) :
    Sat.Clause :=
  C.map (encodeLiteral code)

/-- Encode one typed CNF in the same clause order. -/
def encodeFormula {Var : Type*} (code : Var → Nat) (F : Formula Var) :
    Sat.Fmla :=
  F.map (encodeClause code)

/-- The raw propositional valuation induced by a typed Boolean assignment.
Variables outside the image of `code` are false. -/
def valuation {Var : Type*} (code : Var → Nat) (σ : Assignment Var) :
    Sat.Valuation :=
  fun n => ∃ v, code v = n ∧ σ v = true

/-- Injective numbering makes the induced valuation agree with the typed
assignment at every encoded variable. -/
theorem valuation_code_iff
    {Var : Type*} {code : Var → Nat} (hcode : Function.Injective code)
    (σ : Assignment Var) (v : Var) :
    valuation code σ (code v) ↔ σ v = true := by
  constructor
  · rintro ⟨w, hw, hσ⟩
    have : w = v := hcode hw
    simpa [this] using hσ
  · intro hσ
    exact ⟨v, rfl, hσ⟩

/-- A typed-true literal is not falsified by its encoded raw valuation. -/
theorem not_neg_encodeLiteral_of_eval_eq_true
    {Var : Type*} {code : Var → Nat} (hcode : Function.Injective code)
    (σ : Assignment Var) (l : Literal Var) (hl : l.eval σ = true) :
    ¬ Sat.Valuation.neg (valuation code σ) (encodeLiteral code l) := by
  cases l with
  | positive v =>
      change ¬¬ valuation code σ (code v)
      intro hfalse
      exact hfalse ((valuation_code_iff hcode σ v).2 hl)
  | negative v =>
      change ¬ valuation code σ (code v)
      intro htrue
      have hσ : σ v = true := (valuation_code_iff hcode σ v).1 htrue
      simp [Literal.eval, hσ] at hl

/-- Typed clause satisfaction implies satisfaction of the encoded raw clause. -/
theorem satisfies_encodeClause
    {Var : Type*} {code : Var → Nat} (hcode : Function.Injective code)
    (σ : Assignment Var) (C : Clause Var) (hC : C.Satisfied σ) :
    Sat.Valuation.satisfies (valuation code σ) (encodeClause code C) := by
  induction C with
  | nil =>
      rcases hC with ⟨l, hl, _⟩
      simp at hl
  | cons a C ih =>
      rcases hC with ⟨l, hl, heval⟩
      simp only [encodeClause, List.map_cons]
      intro hneg
      rcases List.mem_cons.mp hl with rfl | hl
      · exact (not_neg_encodeLiteral_of_eval_eq_true hcode σ l heval hneg).elim
      · exact ih ⟨l, hl, heval⟩

/-- Typed formula satisfaction implies satisfaction of the encoded raw CNF. -/
theorem satisfies_encodeFormula
    {Var : Type*} {code : Var → Nat} (hcode : Function.Injective code)
    (σ : Assignment Var) (F : Formula Var) (hF : F.Satisfied σ) :
    Sat.Valuation.satisfies_fmla (valuation code σ)
      (encodeFormula code F) := by
  refine ⟨?_⟩
  intro C hC
  rcases List.mem_map.mp hC with ⟨K, hK, rfl⟩
  exact satisfies_encodeClause hcode σ K (hF K hK)

/-- A raw proof of the empty clause for the exact encoding rules out every
typed satisfying assignment. -/
theorem not_satisfiable_of_raw_refutation
    {Var : Type*} {code : Var → Nat} (hcode : Function.Injective code)
    (F : Formula Var) (hrefute : (encodeFormula code F).proof []) :
    ¬ ∃ σ : Assignment Var, F.Satisfied σ := by
  rintro ⟨σ, hσ⟩
  exact hrefute (valuation code σ) (satisfies_encodeFormula hcode σ F hσ)

/-- Equality with an externally imported raw formula is the final identity
needed to reuse its empty-clause proof for the typed formula. -/
theorem not_satisfiable_of_eq_raw_refutation
    {Var : Type*} {code : Var → Nat} (hcode : Function.Injective code)
    (F : Formula Var) (raw : Sat.Fmla)
    (hraw : encodeFormula code F = raw) (hrefute : raw.proof []) :
    ¬ ∃ σ : Assignment Var, F.Satisfied σ := by
  rw [← hraw] at hrefute
  exact not_satisfiable_of_raw_refutation hcode F hrefute

end RawSat

end TotalColoring.MinSixCNFCore
