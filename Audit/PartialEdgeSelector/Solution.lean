/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.PartialEdgeSelector

/-!
# Comparator solution: the partial-edge selector decoder

Same statement as `Audit/PartialEdgeSelector/Challenge.lean`, from
`TotalColoring.partialEdgeSelectorAssignment_valid`: `ValidOutside`,
`EdgeFinsetIsMatching`, `EdgeFinsetAvoids` (with `Incident v e` the abbreviation
`v ∈ (e : Sym2 V)`) and `SelectorOldColorAllowed` are the hypotheses written
out, and `partialEdgeSelectorAssignment` is the decoded assignment.

`Fidelity.not_weaker` derives the library theorem back from the Challenge
statement, so the two statements are equivalent.
-/

namespace TotalColoringAudit.PartialEdgeSelector

theorem partialEdgeSelectorAssignment_valid
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {q : ℕ}
    (fresh : Fin (q + 1)) (phi : G.edgeSet → Fin q)
    (S : Finset V) (F : Finset G.edgeSet) (g : V → Fin q)
    (hphi : ∀ e f : G.edgeSet, e ∉ F → f ∉ F → G.lineGraph.Adj e f → phi e ≠ phi f)
    (hS : G.IsIndepSet (S : Set V))
    (hF : ∀ ⦃e f : G.edgeSet⦄, e ∈ F → f ∈ F → ¬G.lineGraph.Adj e f)
    (havoid : ∀ ⦃v : V⦄, v ∈ S → ∀ ⦃e : G.edgeSet⦄, e ∈ F → v ∉ (e : Sym2 V))
    (hallowed : ∀ v, v ∉ S → ∀ e : G.edgeSet, v ∈ (e : Sym2 V) → e ∉ F → phi e ≠ g v)
    (hproper : ∀ v, v ∉ S → ∀ w, w ∉ S → G.Adj v w → g v ≠ g w) :
    (∀ v w, G.Adj v w →
        (if v ∈ S then fresh else fresh.succAbove (g v)) ≠
          (if w ∈ S then fresh else fresh.succAbove (g w))) ∧
      (∀ e f, G.lineGraph.Adj e f →
        (if e ∈ F then fresh else fresh.succAbove (phi e)) ≠
          (if f ∈ F then fresh else fresh.succAbove (phi f))) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) →
        (if v ∈ S then fresh else fresh.succAbove (g v)) ≠
          (if e ∈ F then fresh else fresh.succAbove (phi e))) :=
  TotalColoring.partialEdgeSelectorAssignment_valid fresh ⟨phi⟩ S F g hphi hS hF havoid
    hallowed hproper

namespace Fidelity

universe u

/-- The Challenge statement implies the library statement. -/
theorem not_weaker (h : type_of% @partialEdgeSelectorAssignment_valid.{u}) :
    type_of% @TotalColoring.partialEdgeSelectorAssignment_valid.{u} := by
  intro V _ G q fresh phi S F g hphi hS hF havoid hallowed hproper
  exact h fresh phi.color S F g hphi hS hF havoid hallowed hproper

end Fidelity

end TotalColoringAudit.PartialEdgeSelector
