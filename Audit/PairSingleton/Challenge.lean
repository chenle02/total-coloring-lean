/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib

/-!
# Comparator challenge: the pair/singleton auxiliary graph is in the class

Statement only, in Mathlib's vocabulary. A pair/singleton witness for `G` is a
map `partner : V → Option V` (`none` for a singleton class, `some w` for the
pair `{v, w}`) whose pairs are of distinct, mutual, nonadjacent vertices. It
determines, on the vertex type `Option V` with the new center `none`:

* the selector edge of `v`: `s(none, some v)` for a singleton, `s(some v, some w)`
  for a pair (`selector`, fixed by `hselector`);
* the distinguished set `J`, the image of the selector (`hJ`);
* its matching part `M`, the members of `J` not containing `none` (`hM`);
* the auxiliary graph `A`: the copy of `G` on `some` vertices together with the
  edges of `J` (`hA`).

The equations `hselector`, `hJ`, `hM` and `hA` name these objects; they add no
assumption.

Claim: if `J` has exactly `G.maxDegree + 1` members and `G` has at most
`2 * G.maxDegree` vertices, then `(A, J)` with center `none` and matching part
`M` satisfies the nine membership conditions of the auxiliary class with
parameter `G.maxDegree + 1` (as in `Audit/AuxiliaryClass/Challenge.lean`).
-/

namespace TotalColoringAudit.PairSingleton

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
  sorry

end TotalColoringAudit.PairSingleton
