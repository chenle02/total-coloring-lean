import TotalColoring.CriticalState

/-!
# Residual degrees after deleting the distinguished set

This module formalizes the degree bookkeeping for the residual graph
`H.deleteEdges (J : Set (Sym2 V))`.  Its final theorem is conditional on both
an explicit structural witness for the auxiliary class and an explicit
outside-edge-minimal noncolorability witness.  It makes no existence or
all-orders claim.
-/

namespace TotalColoring

universe u

/-- The graph left after all distinguished edges are deleted. -/
abbrev ResidualGraph {V : Type u} (H : SimpleGraph V)
    (J : Finset (Sym2 V)) : SimpleGraph V :=
  H.deleteEdges (J : Set (Sym2 V))

namespace IsAuxiliaryClassMember

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- At every vertex, deleting `J` removes precisely the members of `J` from
the ambient incidence finset. -/
theorem residual_incidenceFinset_eq_sdiff (v : V) :
    (ResidualGraph H J).incidenceFinset v = H.incidenceFinset v \ J := by
  ext e
  simp only [SimpleGraph.mem_incidenceFinset, SimpleGraph.incidenceSet,
    Set.mem_setOf_eq, SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff,
    Finset.mem_sdiff]
  tauto

/-- Exact coverage says that a noncenter vertex sees exactly one member of
`J` in its ambient incidence finset. -/
theorem card_incidenceFinset_inter_distinguished_eq_one
    (h : IsAuxiliaryClassMember D H x J M) (v : V) (hv : v ≠ x) :
    (H.incidenceFinset v ∩ J).card = 1 := by
  rcases h.exact_coverage v hv with ⟨e, he, hunique⟩
  have heIncidence : e ∈ H.incidenceFinset v :=
    (H.mem_incidenceFinset v e).2 ⟨h.distinguished_edges he.1, he.2⟩
  apply Finset.card_eq_one.mpr
  refine ⟨e, ?_⟩
  ext f
  simp only [Finset.mem_inter, Finset.mem_singleton]
  constructor
  · intro hf
    apply hunique f
    exact ⟨hf.2, (H.mem_incidenceFinset v f).1 hf.1 |>.2⟩
  · rintro rfl
    exact ⟨heIncidence, he.1⟩

/-- Every noncenter vertex loses exactly its unique incident distinguished
edge when `J` is deleted. -/
theorem residual_degree_add_one
    (h : IsAuxiliaryClassMember D H x J M) (v : V) (hv : v ≠ x) :
    (ResidualGraph H J).degree v + 1 = H.degree v := by
  calc
    (ResidualGraph H J).degree v + 1 =
        ((ResidualGraph H J).incidenceFinset v).card + 1 := by
      rw [SimpleGraph.card_incidenceFinset_eq_degree]
    _ = (H.incidenceFinset v \ J).card +
        (H.incidenceFinset v ∩ J).card := by
      rw [residual_incidenceFinset_eq_sdiff,
        h.card_incidenceFinset_inter_distinguished_eq_one v hv]
    _ = (H.incidenceFinset v).card :=
      Finset.card_sdiff_add_card_inter (H.incidenceFinset v) J
    _ = H.degree v := H.card_incidenceFinset_eq_degree v

/-- The endpoints of an edge outside `J` are both different from the center:
the entire star at the center lies in `J`. -/
theorem outside_edge_endpoints_ne_center
    (h : IsAuxiliaryClassMember D H x J M) (e : H.edgeSet)
    (heJ : (e : Sym2 V) ∉ J) {u v : V}
    (hends : (e : Sym2 V) = s(u, v)) :
    u ≠ x ∧ v ≠ x := by
  constructor
  · intro hux
    apply heJ
    apply h.center_incident_mem_distinguishedEdgeSet e
    change x ∈ (e : Sym2 V)
    rw [hends, hux]
    exact Sym2.mem_mk_left x v
  · intro hvx
    apply heJ
    apply h.center_incident_mem_distinguishedEdgeSet e
    change x ∈ (e : Sym2 V)
    rw [hends, hvx]
    exact Sym2.mem_mk_right u x

end IsAuxiliaryClassMember

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Residual degree-sum consequence of the critical ambient degree bound.

The structural witness `hstructure` is compatible with `hcritical` by sharing
the same `D`, `H`, and `J`.  It supplies the particular center and matching
witnesses needed to identify the one deleted distinguished edge at each
endpoint.  The theorem is conditional on the hypothetical minimal
noncolorable witness and does not assert that such a witness exists. -/
theorem residual_degree_sum_outside_edge
    (hcritical : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (e : H.edgeSet) (heJ : (e : Sym2 V) ∉ J) {u v : V}
    (hends : (e : Sym2 V) = s(u, v)) :
    D + 2 ≤ (ResidualGraph H J).degree u +
      (ResidualGraph H J).degree v := by
  have hne := hstructure.outside_edge_endpoints_ne_center e heJ hends
  have hu := hstructure.residual_degree_add_one u hne.1
  have hv := hstructure.residual_degree_add_one v hne.2
  have hambient := hcritical.degree_sum_outside_edge e heJ hends
  omega

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
