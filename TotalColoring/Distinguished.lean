import TotalColoring.AuxiliaryClass
import TotalColoring.Total
import Mathlib.Data.Set.Card

/-!
# Distinguished-edge subtype bridge

`TotalColoring.AuxiliaryClass` keeps `J` as a finset of unordered vertex
pairs so that it survives edge deletion without subtype transport.  Coloring
assignments, however, are functions on `H.edgeSet`.  This module supplies the
one-way bridge from the stable structural representation to the edge subtype
used by the coloring API.

No converse construction or coloring-existence statement is asserted.
-/

namespace TotalColoring

universe u

/-- The members of an underlying-pair finset `J` viewed inside the edge
subtype of `H`.  Pairs of `J` which are not edges of `H` have no representative;
the auxiliary-class bridge below assumes the proved containment in `E(H)`. -/
def distinguishedEdgeSet {V : Type u} (H : SimpleGraph V)
    (J : Finset (Sym2 V)) : Set H.edgeSet :=
  {e | (e : Sym2 V) ∈ J}

/-- When every member of `J` is an edge of `H`, the stable pair
representation and the coloring-facing edge-subtype representation are
equivalent. -/
def distinguishedEdgeEquiv {V : Type u} {H : SimpleGraph V}
    {J : Finset (Sym2 V)}
    (hJ : ∀ ⦃e⦄, e ∈ J → e ∈ H.edgeSet) :
    {e : H.edgeSet // e ∈ distinguishedEdgeSet H J} ≃
      {e : Sym2 V // e ∈ J} where
  toFun e := ⟨e.1.1, e.2⟩
  invFun e := ⟨⟨e.1, hJ e.2⟩, e.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

namespace IsAuxiliaryClassMember

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- The coloring-facing distinguished set has exactly `D` members. -/
theorem card_distinguishedEdgeSet
    (h : IsAuxiliaryClassMember D H x J M) :
    (distinguishedEdgeSet H J).ncard = D := by
  calc
    (distinguishedEdgeSet H J).ncard = (J : Set (Sym2 V)).ncard :=
      Set.ncard_congr' (distinguishedEdgeEquiv h.distinguished_edges)
    _ = J.card := Set.ncard_coe_finset J
    _ = D := h.card_distinguished

/-- Every noncenter vertex is incident with exactly one distinguished edge in
the coloring-facing edge subtype. -/
theorem exact_coverage_distinguishedEdgeSet
    (h : IsAuxiliaryClassMember D H x J M) (v : V) (hv : v ≠ x) :
    ∃! e : H.edgeSet, e ∈ distinguishedEdgeSet H J ∧ Incident v e := by
  rcases h.exact_coverage v hv with ⟨e, he, hunique⟩
  let ee : H.edgeSet := ⟨e, h.distinguished_edges he.1⟩
  refine ⟨ee, ⟨he.1, he.2⟩, ?_⟩
  intro f hf
  apply Subtype.ext
  exact hunique f.1 ⟨hf.1, hf.2⟩

/-- Every edge of the full star at the center belongs to the
coloring-facing distinguished set. -/
theorem center_incident_mem_distinguishedEdgeSet
    (h : IsAuxiliaryClassMember D H x J M) (e : H.edgeSet)
    (hxe : Incident x e) : e ∈ distinguishedEdgeSet H J := by
  apply h.incidenceFinset_subset
  exact (H.mem_incidenceFinset x e).2 ⟨e.2, hxe⟩

end IsAuxiliaryClassMember

end TotalColoring
