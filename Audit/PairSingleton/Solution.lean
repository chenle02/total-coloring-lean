/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.PairSingletonExtension

/-!
# Comparator solution: the pair/singleton auxiliary graph is in the class

Same statement as `Audit/PairSingleton/Challenge.lean`, from
`TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_highDegree`:
a `PairSingletonWitness G` is `partner` with its three facts, and `selector`,
`distinguished`, `matchingPart` and `auxiliaryGraph` are the objects that the
Challenge names by equations; `IsAuxiliaryClassMember` is the nine conditions.

`Fidelity.not_weaker` derives the library theorem back from the Challenge
statement, so the two statements are equivalent.
-/

namespace TotalColoringAudit.PairSingleton

namespace Bridge

open TotalColoring TotalColoring.Auxiliary

variable {V : Type*} {G : SimpleGraph V}

theorem selector_eq (P : PairSingletonWitness G) (v : V) :
    P.selector v = (P.partner v).elim s(none, some v) (fun w ↦ s(some v, some w)) := by
  unfold PairSingletonWitness.selector
  cases P.partner v <;> rfl

theorem matchingPart_eq [Fintype V] [DecidableEq V] (P : PairSingletonWitness G) :
    P.matchingPart = P.distinguished.filter (fun e ↦ (none : Option V) ∉ e) := by
  ext e
  simp [PairSingletonWitness.mem_matchingPart]

end Bridge

theorem isAuxiliaryClassMember_of_highDegree
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (partner : V → Option V)
    (partner_ne : ∀ {v w : V}, partner v = some w → v ≠ w)
    (partner_symm : ∀ {v w : V}, partner v = some w → partner w = some v)
    (partner_nonadjacent : ∀ {v w : V}, partner v = some w → ¬G.Adj v w)
    (selector : V → Sym2 (Option V))
    (hselector : ∀ v, selector v = (partner v).elim s(none, some v) (fun w ↦ s(some v, some w)))
    (J : Finset (Sym2 (Option V))) (hJ : J = Finset.univ.image selector)
    (M : Finset (Sym2 (Option V))) (hM : M = J.filter (fun e ↦ (none : Option V) ∉ e))
    (A : SimpleGraph (Option V))
    (hA : A = G.map Function.Embedding.some ⊔ SimpleGraph.fromEdgeSet (J : Set (Sym2 (Option V))))
    [DecidableRel G.Adj] [DecidableRel A.Adj]
    (hclasses : J.card = G.maxDegree + 1)
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    (∀ ⦃e⦄, e ∈ J → e ∈ A.edgeSet) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f) ∧
      (∀ ⦃e⦄, e ∈ M → (none : Option V) ∉ e) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬A.Adj none v) ∧
      J = M ∪ A.incidenceFinset none ∧
      (∀ v, v ≠ none → ∃! e : Sym2 (Option V), e ∈ J ∧ v ∈ e) ∧
      J.card = G.maxDegree + 1 ∧
      A.maxDegree ≤ G.maxDegree + 1 ∧
      (2 ≤ A.degree none ∧ A.degree none ≤ G.maxDegree + 1) := by
  let P : TotalColoring.Auxiliary.PairSingletonWitness G :=
    ⟨partner, partner_ne, partner_symm, partner_nonadjacent⟩
  have hsel : P.selector = selector := by
    funext v
    rw [Bridge.selector_eq, hselector]
  have hJ' : P.distinguished = J := by
    rw [hJ, ← hsel]
    rfl
  have hM' : P.matchingPart = M := by
    rw [Bridge.matchingPart_eq, hJ', hM]
  have hA' : P.auxiliaryGraph = A := by
    rw [hA, ← hJ']
    rfl
  subst hJ' hM' hA'
  have h := P.isAuxiliaryClassMember_of_highDegree hclasses hdense
  exact ⟨h.distinguished_edges, h.matching, h.matching_off_center,
    h.matching_avoids_center_neighbors, h.decomposition, h.exact_coverage,
    h.card_distinguished, h.maxDegree_bound, h.center_degree⟩

namespace Fidelity

universe u

/-- The Challenge statement implies the library statement. -/
theorem not_weaker (h : type_of% @isAuxiliaryClassMember_of_highDegree.{u}) :
    type_of% @TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_highDegree.{u} := by
  intro V G P _ _ _ _ hclasses hdense
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    h P.partner P.partner_ne P.partner_symm P.partner_nonadjacent P.selector
      (Bridge.selector_eq P) P.distinguished rfl P.matchingPart (Bridge.matchingPart_eq P)
      P.auxiliaryGraph rfl hclasses hdense
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

end Fidelity

end TotalColoringAudit.PairSingleton
