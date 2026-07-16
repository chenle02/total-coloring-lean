import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# The deletion-closed auxiliary class

This module formalizes the structural hypotheses defining the paper's abstract
class `A_D`.  It deliberately does not assert that a member has a rainbow edge
coloring.

The distinguished edge set and its matching part are represented as finsets of
unordered vertex pairs rather than as subtypes of the ambient graph's edge set.
Consequently they retain the same types when an edge outside the distinguished
set is deleted.  The theorem `IsAuxiliaryClassMember.deleteEdgeOutside` proves
that all structural hypotheses are preserved by that operation.
-/

namespace TotalColoring

universe u

/-- A finite set of unordered pairs is a matching when distinct members have
no common endpoint. -/
def IsEdgeMatching {V : Type u} (M : Finset (Sym2 V)) : Prop :=
  ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f

/-- The structural predicate defining membership in the paper's abstract
auxiliary class `A_D`.

`J` is the distinguished set, `M` is its off-center matching part, and `x` is
the center of the star.  Since the vertex type is a `Fintype`, the graph and all
degrees below are finite.  A `SimpleGraph` is loopless and undirected by
construction.
-/
structure IsAuxiliaryClassMember {V : Type u} [Fintype V] [DecidableEq V]
    (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (x : V) (J M : Finset (Sym2 V)) : Prop where
  /-- Every distinguished pair is an edge of the ambient graph. -/
  distinguished_edges : ∀ ⦃e⦄, e ∈ J → e ∈ H.edgeSet
  /-- The matching part consists of pairwise endpoint-disjoint edges. -/
  matching : IsEdgeMatching M
  /-- No matching edge is incident with the center. -/
  matching_off_center : ∀ ⦃e⦄, e ∈ M → x ∉ e
  /-- No endpoint of a matching edge is a neighbor of the center. -/
  matching_avoids_center_neighbors :
    ∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H.Adj x v
  /-- `J` is exactly the matching together with the full star at `x`. -/
  decomposition : J = M ∪ H.incidenceFinset x
  /-- Every vertex other than `x` is incident with exactly one edge of `J`. -/
  exact_coverage :
    ∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e
  /-- The distinguished set has the class parameter as its cardinality. -/
  card_distinguished : J.card = D
  /-- The ambient graph has maximum degree at most `D`. -/
  maxDegree_bound : H.maxDegree ≤ D
  /-- The center degree lies in the required nondegenerate range. -/
  center_degree : 2 ≤ H.degree x ∧ H.degree x ≤ D

/-- Pair-level membership in the paper's class `A_D`; the center and matching
part are existential structural witnesses rather than part of the pair
`(H, J)` itself. -/
def InAuxiliaryClass {V : Type u} [Fintype V] [DecidableEq V]
    (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (J : Finset (Sym2 V)) : Prop :=
  ∃ x M, IsAuxiliaryClassMember D H x J M

namespace IsAuxiliaryClassMember

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- The star at the center is contained in the distinguished set. -/
theorem incidenceFinset_subset (h : IsAuxiliaryClassMember D H x J M) :
    H.incidenceFinset x ⊆ J := by
  intro e he
  rw [h.decomposition]
  exact Finset.mem_union_right M he

/-- Every member of the matching part is an edge of the ambient graph. -/
theorem matching_edges (h : IsAuxiliaryClassMember D H x J M) :
    ∀ ⦃e⦄, e ∈ M → e ∈ H.edgeSet := by
  intro e he
  apply h.distinguished_edges
  rw [h.decomposition]
  exact Finset.mem_union_left _ he

/-- Pointwise degree control derived from the maximum-degree hypothesis. -/
theorem degree_le_parameter (h : IsAuxiliaryClassMember D H x J M) (v : V) :
    H.degree v ≤ D :=
  (H.degree_le_maxDegree v).trans h.maxDegree_bound

/-- Membership forces the paper's parameter range `D ≥ 2`. -/
theorem two_le_parameter (h : IsAuxiliaryClassMember D H x J M) : 2 ≤ D :=
  h.center_degree.1.trans h.center_degree.2

/-- Deleting a pair outside `J` leaves the center's incidence finset
unchanged.  The pair need not be an edge; the principal deletion theorem adds
the edge-membership hypothesis matching the mathematical use case. -/
theorem incidenceFinset_deleteSingleton_eq
    (h : IsAuxiliaryClassMember D H x J M) {e : Sym2 V} (heJ : e ∉ J) :
    (H.deleteEdges {e}).incidenceFinset x = H.incidenceFinset x := by
  have hIncidenceSet :
      (H.deleteEdges {e}).incidenceSet x = H.incidenceSet x := by
    ext f
    simp only [SimpleGraph.incidenceSet, Set.mem_setOf_eq,
      SimpleGraph.edgeSet_deleteEdges, Set.mem_sdiff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hfH, _⟩, hxf⟩
      exact ⟨hfH, hxf⟩
    · intro hf
      rcases hf with ⟨hfH, hxf⟩
      refine ⟨⟨hfH, ?_⟩, hxf⟩
      intro hfe
      apply heJ
      rw [← hfe]
      apply h.incidenceFinset_subset
      exact (H.mem_incidenceFinset x f).2 ⟨hfH, hxf⟩
  ext f
  simp only [SimpleGraph.mem_incidenceFinset, hIncidenceSet]

/-- The paper's auxiliary class is closed under deletion of an edge outside
the distinguished set.  No coloring-existence assertion is used or produced.
-/
theorem deleteEdgeOutside
    (h : IsAuxiliaryClassMember D H x J M) {e : Sym2 V}
    (_heH : e ∈ H.edgeSet) (heJ : e ∉ J) :
    IsAuxiliaryClassMember D (H.deleteEdges {e}) x J M := by
  have hIncidence := h.incidenceFinset_deleteSingleton_eq heJ
  have hDegree : (H.deleteEdges {e}).degree x = H.degree x := by
    rw [← SimpleGraph.card_incidenceFinset_eq_degree,
      ← SimpleGraph.card_incidenceFinset_eq_degree, hIncidence]
  refine {
    distinguished_edges := ?_
    matching := h.matching
    matching_off_center := h.matching_off_center
    matching_avoids_center_neighbors := ?_
    decomposition := ?_
    exact_coverage := h.exact_coverage
    card_distinguished := h.card_distinguished
    maxDegree_bound := ?_
    center_degree := ?_
  }
  · intro f hf
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨h.distinguished_edges hf, ?_⟩
    simpa only [Set.mem_singleton_iff] using
      (fun hfe : f = e => heJ (hfe ▸ hf))
  · intro f hf v hv hxf
    exact h.matching_avoids_center_neighbors hf hv
      (SimpleGraph.deleteEdges_le ({e} : Set (Sym2 V)) hxf)
  · calc
      J = M ∪ H.incidenceFinset x := h.decomposition
      _ = M ∪ (H.deleteEdges {e}).incidenceFinset x := by rw [hIncidence]
  · apply SimpleGraph.maxDegree_le_of_forall_degree_le
    intro v
    exact (SimpleGraph.degree_le_of_le
      (SimpleGraph.deleteEdges_le ({e} : Set (Sym2 V)))).trans
      (h.degree_le_parameter v)
  · simpa only [hDegree] using h.center_degree

end IsAuxiliaryClassMember

namespace InAuxiliaryClass

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- The pair-level auxiliary class is closed under deletion of an edge outside
the distinguished set. -/
theorem deleteEdgeOutside (h : InAuxiliaryClass D H J) {e : Sym2 V}
    (heH : e ∈ H.edgeSet) (heJ : e ∉ J) :
    InAuxiliaryClass D (H.deleteEdges {e}) J := by
  rcases h with ⟨x, M, hxM⟩
  exact ⟨x, M, hxM.deleteEdgeOutside heH heJ⟩

end InAuxiliaryClass

end TotalColoring
