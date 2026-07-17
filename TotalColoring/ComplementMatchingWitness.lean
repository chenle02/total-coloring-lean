import TotalColoring.PairSingletonExtension

/-!
# Pair/singleton witnesses from complement matchings

This module converts a supplied matching graph in the complement of `G` into
the concrete `PairSingletonWitness G` used by the auxiliary construction.
The matching hypothesis is kept explicit: every neighbor set of `H` is
subsingleton.  A later matching-existence module can package that condition
under its own reusable name without creating an import cycle here.

Vertices in the support of `H` choose their unique `H`-neighbor as partner;
vertices outside the support choose no partner.  The resulting witness has
singleton vertices exactly outside `H.support`.  The degree-sum formula then
gives the exact relation between the support and edge counts, and hence the
exact distinguished-selector count needed by the auxiliary class.
-/

namespace TotalColoring.Auxiliary

universe u

variable {V : Type u} {G H : SimpleGraph V}

/-- The optional partner selected by a supplied finite graph.  On the support
of `H`, this chooses an adjacent vertex; off the support, it returns `none`.
Uniqueness of the chosen neighbor is supplied separately when this function is
used to build a pair/singleton witness. -/
noncomputable def complementMatchingPartner
    [Fintype V] (H : SimpleGraph V) [DecidableRel H.Adj] (v : V) : Option V :=
  if hv : v ∈ H.support then
    some (Classical.choose (H.mem_support.mp hv))
  else
    none

section Partner

variable [Fintype V] [DecidableRel H.Adj]

/-- Under the matching hypothesis, selecting `w` is equivalent to adjacency
to `w` in the supplied matching graph. -/
theorem complementMatchingPartner_eq_some_iff
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) {v w : V} :
    complementMatchingPartner H v = some w ↔ H.Adj v w := by
  rw [complementMatchingPartner]
  split_ifs with hv
  · have hchosen :
        H.Adj v (Classical.choose (H.mem_support.mp hv)) :=
      Classical.choose_spec (H.mem_support.mp hv)
    constructor
    · intro h
      have heq : Classical.choose (H.mem_support.mp hv) = w :=
        Option.some.inj h
      subst w
      exact hchosen
    · intro hadj
      apply congrArg some
      apply hmatching v
      · exact (H.mem_neighborSet v _).mpr hchosen
      · exact (H.mem_neighborSet v _).mpr hadj
  · constructor
    · intro h
      cases h
    · intro hadj
      exact (hv hadj.mem_support_left).elim

/-- A vertex has no selected partner exactly when it is outside the support of
the supplied matching graph. -/
theorem complementMatchingPartner_eq_none_iff (v : V) :
    complementMatchingPartner H v = none ↔ v ∉ H.support := by
  rw [complementMatchingPartner]
  split_ifs with hv
  · simp [hv]
  · simp [hv]

/-- A graph lying in `G`'s complement, with at most one neighbor at every
vertex, canonically supplies a pair/singleton witness for `G`. -/
noncomputable def PairSingletonWitness.ofComplementMatching
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) :
    PairSingletonWitness G where
  partner := complementMatchingPartner H
  partner_ne := by
    intro v w hpartner
    exact ((complementMatchingPartner_eq_some_iff hmatching).mp hpartner).ne
  partner_symm := by
    intro v w hpartner
    apply (complementMatchingPartner_eq_some_iff hmatching).mpr
    exact ((complementMatchingPartner_eq_some_iff hmatching).mp hpartner).symm
  partner_nonadjacent := by
    intro v w hpartner
    have hHvw := (complementMatchingPartner_eq_some_iff hmatching).mp hpartner
    exact (G.compl_adj v w).mp (hHK hHvw) |>.2

@[simp]
theorem PairSingletonWitness.ofComplementMatching_partner
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) (v : V) :
    (PairSingletonWitness.ofComplementMatching H hHK hmatching).partner v =
      complementMatchingPartner H v :=
  rfl

/-- Partner normal form for the witness induced by a complement matching. -/
theorem PairSingletonWitness.ofComplementMatching_partner_eq_some_iff
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) {v w : V} :
    (PairSingletonWitness.ofComplementMatching H hHK hmatching).partner v = some w ↔
      H.Adj v w := by
  exact complementMatchingPartner_eq_some_iff hmatching

/-- Singleton normal form for the witness induced by a complement matching. -/
theorem PairSingletonWitness.ofComplementMatching_partner_eq_none_iff
    [DecidableEq V] (H : SimpleGraph V) [DecidableRel H.Adj] (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) (v : V) :
    (PairSingletonWitness.ofComplementMatching H hHK hmatching).partner v = none ↔
      v ∉ H.support := by
  exact complementMatchingPartner_eq_none_iff v

end Partner

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel H.Adj]

omit [DecidableEq V] in
/-- In a finite graph with subsingleton neighbor sets, every supported vertex
has degree exactly one. -/
theorem degree_eq_one_of_mem_support_of_neighborSet_subsingleton
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton)
    {v : V} (hv : v ∈ H.support) :
    H.degree v = 1 := by
  have hpos : 0 < H.degree v := (H.degree_pos_iff_mem_support v).mpr hv
  have hle : H.degree v ≤ 1 := by
    rw [← H.card_neighborFinset_eq_degree]
    apply Finset.card_le_one_iff.mpr
    intro a b ha hb
    apply hmatching v
    · exact (H.mem_neighborSet v a).mpr ((H.mem_neighborFinset v a).mp ha)
    · exact (H.mem_neighborSet v b).mpr ((H.mem_neighborFinset v b).mp hb)
  omega

omit [DecidableEq V] in
/-- A finite matching graph has two supported vertices for every edge. -/
theorem support_card_eq_twice_edge_card_of_neighborSet_subsingleton
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) :
    H.support.toFinset.card = 2 * H.edgeFinset.card := by
  calc
    H.support.toFinset.card =
        ∑ v ∈ H.support.toFinset, 1 := by simp
    _ = ∑ v ∈ H.support.toFinset, H.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      symm
      exact degree_eq_one_of_mem_support_of_neighborSet_subsingleton
        hmatching (Set.mem_toFinset.mp hv)
    _ = 2 * H.edgeFinset.card :=
      H.sum_degrees_support_eq_twice_card_edges

/-- The singleton vertices of the induced pair/singleton witness are exactly
the vertices outside the support of the supplied matching graph. -/
theorem PairSingletonWitness.ofComplementMatching_singletonVertices
    (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) :
    (PairSingletonWitness.ofComplementMatching H hHK hmatching).singletonVertices =
      Finset.univ \ H.support.toFinset := by
  ext v
  simp only [PairSingletonWitness.mem_singletonVertices,
    PairSingletonWitness.ofComplementMatching_partner,
    complementMatchingPartner_eq_none_iff, Finset.mem_sdiff,
    Finset.mem_univ, Set.mem_toFinset, true_and]

/-- Exact singleton count in terms of the support of the supplied matching
graph. -/
theorem PairSingletonWitness.ofComplementMatching_singletonVertices_card
    (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) :
    (PairSingletonWitness.ofComplementMatching H hHK hmatching).singletonVertices.card =
      Fintype.card V - H.support.toFinset.card := by
  rw [PairSingletonWitness.ofComplementMatching_singletonVertices hHK hmatching,
    Finset.card_sdiff_of_subset (Finset.subset_univ H.support.toFinset),
    Finset.card_univ]

/-- The induced witness has one distinguished selector for every unmatched
vertex and one for every matching edge, hence `|V| - |E(H)|` in total. -/
theorem PairSingletonWitness.ofComplementMatching_distinguished_card_eq_card_sub
    (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton) :
    (PairSingletonWitness.ofComplementMatching H hHK hmatching).distinguished.card =
      Fintype.card V - H.edgeFinset.card := by
  let P := PairSingletonWitness.ofComplementMatching H hHK hmatching
  have horbit := P.card_add_singletonVertices_card_eq_two_mul_distinguished_card
  have hsingle :
      P.singletonVertices.card = Fintype.card V - H.support.toFinset.card := by
    simpa [P] using
      PairSingletonWitness.ofComplementMatching_singletonVertices_card
        (G := G) hHK hmatching
  have hsupport :=
    support_card_eq_twice_edge_card_of_neighborSet_subsingleton hmatching
  have hsupport_le : H.support.toFinset.card ≤ Fintype.card V :=
    Finset.card_le_univ H.support.toFinset
  rw [hsingle, hsupport] at horbit
  have hedge_twice_le : 2 * H.edgeFinset.card ≤ Fintype.card V :=
    hsupport ▸ hsupport_le
  apply Nat.mul_left_cancel zero_lt_two
  calc
    2 * P.distinguished.card =
        Fintype.card V + (Fintype.card V - 2 * H.edgeFinset.card) :=
      horbit.symm
    _ = 2 * (Fintype.card V - H.edgeFinset.card) := by
      omega

/-- If the supplied matching has exactly `|V| - D` edges, then the induced
pair/singleton witness has exactly `D` distinguished selector edges. -/
theorem PairSingletonWitness.ofComplementMatching_distinguished_card
    {D : ℕ} (hHK : H ≤ Gᶜ)
    (hmatching : ∀ v, (H.neighborSet v).Subsingleton)
    (hDle : D ≤ Fintype.card V)
    (hcard : H.edgeFinset.card = Fintype.card V - D) :
    (PairSingletonWitness.ofComplementMatching H hHK hmatching).distinguished.card = D := by
  have hdistinguished :=
    PairSingletonWitness.ofComplementMatching_distinguished_card_eq_card_sub
      (G := G) hHK hmatching
  omega

end Finite

end TotalColoring.Auxiliary
