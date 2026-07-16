import TotalColoring.Partial

/-!
# Oriented center spokes

Edges in a simple graph are unordered pairs.  Fan arguments nevertheless use
a fixed center and repeatedly refer to the other endpoint as a leaf.  A
`CenterSpoke` stores that orientation together with the exact endpoint
equality, avoiding any implicit choice of an endpoint later in the proof.
-/

namespace TotalColoring

universe u

/-- An edge explicitly oriented away from a fixed center. -/
structure CenterSpoke {V : Type u} (G : SimpleGraph V) (center : V) where
  leaf : V
  edge : G.edgeSet
  endpoints : (edge : Sym2 V) = s(center, leaf)

namespace CenterSpoke

variable {V : Type u} {G : SimpleGraph V} {center : V}

/-- The center is incident with its spoke edge. -/
theorem center_incident (spoke : CenterSpoke G center) :
    Incident center spoke.edge := by
  change center ∈ (spoke.edge : Sym2 V)
  rw [spoke.endpoints]
  exact Sym2.mem_mk_left center spoke.leaf

/-- The declared leaf is incident with its spoke edge. -/
theorem leaf_incident (spoke : CenterSpoke G center) :
    Incident spoke.leaf spoke.edge := by
  change spoke.leaf ∈ (spoke.edge : Sym2 V)
  rw [spoke.endpoints]
  exact Sym2.mem_mk_right center spoke.leaf

/-- The only endpoints of a spoke are its fixed center and declared leaf. -/
theorem incident_iff (spoke : CenterSpoke G center) {v : V} :
    Incident v spoke.edge ↔ v = center ∨ v = spoke.leaf := by
  change v ∈ (spoke.edge : Sym2 V) ↔ _
  rw [spoke.endpoints]
  exact Sym2.mem_iff

/-- A spoke records a genuine adjacency from the center to its leaf. -/
theorem adj (spoke : CenterSpoke G center) : G.Adj center spoke.leaf := by
  rw [← G.mem_edgeSet]
  rw [← spoke.endpoints]
  exact spoke.edge.2

/-- The leaf of a simple-graph spoke differs from its center. -/
theorem leaf_ne_center (spoke : CenterSpoke G center) :
    spoke.leaf ≠ center :=
  spoke.adj.ne'

/-- At a fixed center, equality of leaves forces equality of spoke edges. -/
theorem edge_eq_of_leaf_eq {p q : CenterSpoke G center}
    (h : p.leaf = q.leaf) : p.edge = q.edge := by
  apply Subtype.ext
  calc
    (p.edge : Sym2 V) = s(center, p.leaf) := p.endpoints
    _ = s(center, q.leaf) := by rw [h]
    _ = (q.edge : Sym2 V) := q.endpoints.symm

/-- Conversely, at a fixed center the spoke edge determines its leaf. -/
theorem leaf_eq_of_edge_eq {p q : CenterSpoke G center}
    (h : p.edge = q.edge) : p.leaf = q.leaf := by
  apply Sym2.congr_right.mp
  calc
    s(center, p.leaf) = (p.edge : Sym2 V) := p.endpoints.symm
    _ = (q.edge : Sym2 V) := by rw [h]
    _ = s(center, q.leaf) := q.endpoints

@[ext]
theorem ext {p q : CenterSpoke G center} (h : p.leaf = q.leaf) : p = q := by
  cases p with
  | mk pLeaf pEdge pEndpoints =>
      cases q with
      | mk qLeaf qEdge qEndpoints =>
          simp only at h
          subst qLeaf
          have hedge : pEdge = qEdge := by
            apply Subtype.ext
            exact pEndpoints.trans qEndpoints.symm
          subst qEdge
          rfl

/-- Distinct spokes have both distinct leaves and distinct edges. -/
theorem ne_iff_leaf_ne {p q : CenterSpoke G center} :
    p ≠ q ↔ p.leaf ≠ q.leaf := by
  constructor
  · contrapose!
    exact ext
  · contrapose!
    intro h
    rw [h]

theorem ne_iff_edge_ne {p q : CenterSpoke G center} :
    p ≠ q ↔ p.edge ≠ q.edge := by
  constructor
  · contrapose!
    exact fun h ↦ ext (leaf_eq_of_edge_eq h)
  · contrapose!
    intro h
    rw [h]

/-- Distinct spokes are adjacent as vertices of the line graph because they
share the center. -/
theorem lineGraph_adj {p q : CenterSpoke G center} (hne : p ≠ q) :
    G.lineGraph.Adj p.edge q.edge := by
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  exact ⟨(ne_iff_edge_ne.mp hne), center, p.center_incident,
    q.center_incident⟩

/-- A distinct spoke cannot also meet the other spoke's leaf.  Simplicity and
the fixed-center orientation make the declared leaves unique. -/
theorem not_incident_leaf_of_ne {p q : CenterSpoke G center} (hne : p ≠ q) :
    ¬Incident q.leaf p.edge := by
  intro hinc
  rcases p.incident_iff.mp hinc with hcenter | hleaf
  · exact q.leaf_ne_center hcenter
  · apply hne
    exact ext hleaf.symm

end CenterSpoke

end TotalColoring
