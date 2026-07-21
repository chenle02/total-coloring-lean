import TotalColoring.PartialKempe

/-!
# Vertex geometry of partial two-color components

`PartialKempe` realizes a physical two-color component as an edge
reachability class in the line graph.  Fan arguments also need the vertex
view of that same object: a proper two-color subgraph has no branching, a
vertex missing one of the two colors is an endpoint whenever the component
meets it, and swapping the component exchanges which of the two colors is
missing there.

This module proves those local geometric facts directly from incidence,
validity, and full reachability-class closure.  It does not yet choose or
classify a global path/cycle walk, and it makes no maximal-fan or criticality
claim.
-/

namespace TotalColoring

universe u v

/-- An edge set meets a vertex when it contains an incident edge. -/
def EdgeSetMeetsVertex {V : Type u} {G : SimpleGraph V}
    (K : Set G.edgeSet) (v : V) : Prop :=
  ∃ e, e ∈ K ∧ Incident v e

/-- An edge set avoids a vertex when none of its edges is incident there. -/
def EdgeSetAvoidsVertex {V : Type u} {G : SimpleGraph V}
    (K : Set G.edgeSet) (v : V) : Prop :=
  ∀ {e}, e ∈ K → ¬Incident v e

theorem edgeSetAvoidsVertex_iff_not_meets {V : Type u} {G : SimpleGraph V}
    {K : Set G.edgeSet} {v : V} :
    EdgeSetAvoidsVertex K v ↔ ¬EdgeSetMeetsVertex K v := by
  constructor
  · intro havoid hmeet
    rcases hmeet with ⟨e, heK, hev⟩
    exact havoid heK hev
  · intro hnot e heK hev
    exact hnot ⟨e, heK, hev⟩

/-- A vertex is an endpoint of an edge set when exactly one edge of the set
is incident there. -/
def EdgeSetIsEndpoint {V : Type u} {G : SimpleGraph V}
    (K : Set G.edgeSet) (v : V) : Prop :=
  ∃ e, e ∈ K ∧ Incident v e ∧
    ∀ {f}, f ∈ K → Incident v f → f = e

/-- A vertex is internal to an edge set when two distinct edges of the set are
incident there. -/
def EdgeSetIsInternal {V : Type u} {G : SimpleGraph V}
    (K : Set G.edgeSet) (v : V) : Prop :=
  ∃ e f, e ∈ K ∧ f ∈ K ∧ Incident v e ∧ Incident v f ∧ e ≠ f

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Two distinct incident edges are adjacent in the line graph. -/
private theorem lineGraph_adj_of_incident {v : V} {e f : G.edgeSet}
    (hef : e ≠ f) (he : Incident v e) (hf : Incident v f) :
    G.lineGraph.Adj e f := by
  exact SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hef, v, he, hf⟩

/-- Properness makes an incident edge of a fixed actual color unique. -/
theorem edge_eq_of_incident_of_color_eq
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {v : V} {e f : G.edgeSet} {c : C}
    (he : Incident v e) (hf : Incident v f)
    (hec : a.color e = some c) (hfc : a.color f = some c) :
    e = f := by
  by_contra hef
  exact (hvalid e f c (lineGraph_adj_of_incident hef he hf) hec) hfc

/-- Every member of a genuine physical component is supported by one of its
two colors. -/
theorem twoColorSupported_of_mem_component
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {e : G.edgeSet} (heK : e ∈ K) :
    a.TwoColorSupported alpha beta e := by
  rcases hK with ⟨root, hroot, rfl⟩
  exact a.twoColorSupported_of_mem_reachabilityClass alpha beta hroot heK

/-- At a vertex met by a physical component, every other incident supported
edge belongs to that same component.  This is the load-bearing conversion
from line-graph reachability to vertex-component closure. -/
theorem mem_component_of_mem_of_incident_supported
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {v : V} {e f : G.edgeSet} (heK : e ∈ K)
    (he : Incident v e) (hf : Incident v f)
    (hfsupported : a.TwoColorSupported alpha beta f) :
    f ∈ K := by
  rcases hK with ⟨root, hroot, rfl⟩
  have hesupported : a.TwoColorSupported alpha beta e :=
    a.twoColorSupported_of_mem_reachabilityClass alpha beta hroot heK
  by_cases hef : e = f
  · simpa [hef] using heK
  · exact heK.tail
      ⟨lineGraph_adj_of_incident hef he hf, hesupported, hfsupported⟩

/-- A reachability class with a supported root is a genuine physical
component. -/
theorem isTwoColorKempeComponent_reachabilityClass
    (a : PartialEdgeAssignment G C) (alpha beta : C) (root : G.edgeSet)
    (hroot : a.TwoColorSupported alpha beta root) :
    a.IsTwoColorKempeComponent alpha beta
      (a.TwoColorReachabilityClass alpha beta root) :=
  ⟨root, hroot, rfl⟩

/-- A color which is not missing at a vertex is witnessed by an incident edge
of that actual color. -/
theorem exists_incident_colored_edge_of_not_missing
    (a : PartialEdgeAssignment G C) {v : V} {c : C}
    (hnot : ¬a.MissingAt v c) :
    ∃ e : G.edgeSet, Incident v e ∧ a.color e = some c := by
  classical
  rw [MissingAt] at hnot
  push Not at hnot
  exact hnot

/-- Any two edges in one genuine component are mutually reachable in the
supported two-color line graph. -/
theorem twoColorReachable_of_mem_of_mem_component
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {e f : G.edgeSet} (heK : e ∈ K) (hfK : f ∈ K) :
    a.TwoColorReachable alpha beta e f := by
  rcases hK with ⟨root, hroot, rfl⟩
  exact (a.twoColorReachable_symm alpha beta heK).trans hfK

/-- Genuine components for the same ordered color pair which share an edge
are equal. -/
theorem isTwoColorKempeComponent_eq_of_common_member
    (a : PartialEdgeAssignment G C) {alpha beta : C}
    {K L : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (hL : a.IsTwoColorKempeComponent alpha beta L)
    {e : G.edgeSet} (heK : e ∈ K) (heL : e ∈ L) : K = L := by
  apply Set.Subset.antisymm
  · intro f hfK
    rcases hL with ⟨root, hroot, hLdef⟩
    rw [hLdef] at heL ⊢
    exact heL.trans
      (twoColorReachable_of_mem_of_mem_component a hK heK hfK)
  · intro f hfL
    rcases hK with ⟨root, hroot, hKdef⟩
    rw [hKdef] at heK ⊢
    exact heK.trans
      (twoColorReachable_of_mem_of_mem_component a hL heL hfL)

/-- Two genuine components for the same ordered color pair which both meet a
vertex missing the first color are equal.  Validity makes their incident
second-color edges equal, supplying the common member. -/
theorem components_eq_of_meet_vertex_missing_left
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K L : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (hL : a.IsTwoColorKempeComponent alpha beta L)
    {v : V} (hmissing : a.MissingAt v alpha)
    (hKv : EdgeSetMeetsVertex K v) (hLv : EdgeSetMeetsVertex L v) :
    K = L := by
  rcases hKv with ⟨e, heK, hve⟩
  rcases hLv with ⟨f, hfL, hvf⟩
  have hebeta : a.color e = some beta :=
    (twoColorSupported_of_mem_component a hK heK).resolve_left
      (hmissing e hve)
  have hfbeta : a.color f = some beta :=
    (twoColorSupported_of_mem_component a hL hfL).resolve_left
      (hmissing f hvf)
  have hef : e = f :=
    edge_eq_of_incident_of_color_eq hvalid hve hvf hebeta hfbeta
  subst f
  exact isTwoColorKempeComponent_eq_of_common_member a hK hL heK hfL

/-- Local path/cycle geometry: among any three incident edges supported by
two colors in a proper partial coloring, two are equal.  Equivalently, the
physical two-color subgraph has vertex degree at most two and cannot branch.
-/
theorem twoColorSupported_incident_edges_no_branch
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {v : V} {e f g : G.edgeSet}
    (he : Incident v e) (hf : Incident v f) (hg : Incident v g)
    (hes : a.TwoColorSupported alpha beta e)
    (hfs : a.TwoColorSupported alpha beta f)
    (hgs : a.TwoColorSupported alpha beta g) :
    e = f ∨ e = g ∨ f = g := by
  rcases hes with healpha | hebeta
  · rcases hfs with hfalpha | hfbeta
    · exact Or.inl (edge_eq_of_incident_of_color_eq hvalid he hf healpha hfalpha)
    · rcases hgs with hgalpha | hgbeta
      · exact Or.inr <| Or.inl <|
          edge_eq_of_incident_of_color_eq hvalid he hg healpha hgalpha
      · exact Or.inr <| Or.inr <|
          edge_eq_of_incident_of_color_eq hvalid hf hg hfbeta hgbeta
  · rcases hfs with hfalpha | hfbeta
    · rcases hgs with hgalpha | hgbeta
      · exact Or.inr <| Or.inr <|
          edge_eq_of_incident_of_color_eq hvalid hf hg hfalpha hgalpha
      · exact Or.inr <| Or.inl <|
          edge_eq_of_incident_of_color_eq hvalid he hg hebeta hgbeta
    · exact Or.inl (edge_eq_of_incident_of_color_eq hvalid he hf hebeta hfbeta)

/-- A supported two-color edge set that is locally internal or absent cannot
cut an adjacent alpha-beta pair. -/
theorem twoColorBoundaryClosed_of_supported_internal_or_avoids
    (a : PartialEdgeAssignment G C) {alpha beta : C}
    {K : Set G.edgeSet} (hvalid : a.Valid)
    (hsupported :
      ∀ ⦃e⦄, e ∈ K → a.TwoColorSupported alpha beta e)
    (hbalanced :
      ∀ v, EdgeSetIsInternal K v ∨ EdgeSetAvoidsVertex K v) :
    a.TwoColorBoundaryClosed alpha beta K := by
  intro e f hef healpha hfbeta
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hef with
    ⟨_, v, he, hf⟩
  have hes : a.TwoColorSupported alpha beta e := Or.inl healpha
  have hfs : a.TwoColorSupported alpha beta f := Or.inr hfbeta
  rcases hbalanced v with hinternal | havoids
  · rcases hinternal with
      ⟨g, h, hgK, hhK, hvg, hvh, hgh⟩
    have hgs : a.TwoColorSupported alpha beta g := hsupported hgK
    have hhs : a.TwoColorSupported alpha beta h := hsupported hhK
    have heK : e ∈ K := by
      rcases twoColorSupported_incident_edges_no_branch
          hvalid he hvg hvh hes hgs hhs with
        heg | heh | hgh'
      · exact heg.symm ▸ hgK
      · exact heh.symm ▸ hhK
      · exact (hgh hgh').elim
    have hfK : f ∈ K := by
      rcases twoColorSupported_incident_edges_no_branch
          hvalid hf hvg hvh hfs hgs hhs with
        hfg | hfh | hgh'
      · exact hfg.symm ▸ hgK
      · exact hfh.symm ▸ hhK
      · exact (hgh hgh').elim
    exact ⟨fun _ ↦ hfK, fun _ ↦ heK⟩
  · exact ⟨
      fun heK ↦ (havoids heK he).elim,
      fun hfK ↦ (havoids hfK hf).elim
    ⟩

/-- If a genuine two-color component meets a vertex at which the first color
is missing, then that vertex is an endpoint of the component. -/
theorem edgeSetIsEndpoint_of_missing_left_of_component_meets
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet} {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (hmissing : a.MissingAt v alpha)
    (hmeets : EdgeSetMeetsVertex K v) :
    EdgeSetIsEndpoint K v := by
  rcases hmeets with ⟨e, heK, he⟩
  have hes := twoColorSupported_of_mem_component a hK heK
  have hebeta : a.color e = some beta := hes.resolve_left (hmissing e he)
  refine ⟨e, heK, he, ?_⟩
  intro f hfK hf
  have hfs := twoColorSupported_of_mem_component a hK hfK
  have hfbeta : a.color f = some beta := hfs.resolve_left (hmissing f hf)
  exact edge_eq_of_incident_of_color_eq hvalid hf he hfbeta hebeta

/-- Symmetric endpoint statement when the second color is missing. -/
theorem edgeSetIsEndpoint_of_missing_right_of_component_meets
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet} {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (hmissing : a.MissingAt v beta)
    (hmeets : EdgeSetMeetsVertex K v) :
    EdgeSetIsEndpoint K v := by
  rcases hmeets with ⟨e, heK, he⟩
  have hes := twoColorSupported_of_mem_component a hK heK
  have healpha : a.color e = some alpha := hes.resolve_right (hmissing e he)
  refine ⟨e, heK, he, ?_⟩
  intro f hfK hf
  have hfs := twoColorSupported_of_mem_component a hK hfK
  have hfalpha : a.color f = some alpha := hfs.resolve_right (hmissing f hf)
  exact edge_eq_of_incident_of_color_eq hvalid hf he hfalpha healpha

/-- Exact endpoint characterization.  At a met vertex of a proper physical
component, degree one is equivalent to at least one of the two colors being
missing. -/
theorem edgeSetIsEndpoint_iff_meets_and_missing
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet} {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta) :
    EdgeSetIsEndpoint K v ↔
      EdgeSetMeetsVertex K v ∧
        (a.MissingAt v alpha ∨ a.MissingAt v beta) := by
  constructor
  · rintro ⟨e, heK, he, hunique⟩
    refine ⟨⟨e, heK, he⟩, ?_⟩
    rcases twoColorSupported_of_mem_component a hK heK with
      healpha | hebeta
    · right
      intro f hf hfbeta
      have hfK := mem_component_of_mem_of_incident_supported a hK heK he hf
        (Or.inr hfbeta)
      have hfe := hunique hfK hf
      subst f
      exact halphabeta (Option.some.inj (healpha.symm.trans hfbeta))
    · left
      intro f hf hfalpha
      have hfK := mem_component_of_mem_of_incident_supported a hK heK he hf
        (Or.inl hfalpha)
      have hfe := hunique hfK hf
      subst f
      exact halphabeta (Option.some.inj (hfalpha.symm.trans hebeta))
  · rintro ⟨hmeets, hmissing | hmissing⟩
    · exact edgeSetIsEndpoint_of_missing_left_of_component_meets
        hvalid hK hmissing hmeets
    · exact edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK hmissing hmeets

/-- Exact internal-vertex characterization.  A met vertex is internal to a
proper physical component precisely when both component colors occur there.
-/
theorem edgeSetIsInternal_iff_meets_and_present_both
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet} {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta) :
    EdgeSetIsInternal K v ↔
      EdgeSetMeetsVertex K v ∧ ¬a.MissingAt v alpha ∧
        ¬a.MissingAt v beta := by
  constructor
  · rintro ⟨e, f, heK, hfK, he, hf, hef⟩
    refine ⟨⟨e, heK, he⟩, ?_, ?_⟩
    · intro hmissing
      rcases edgeSetIsEndpoint_of_missing_left_of_component_meets
          hvalid hK hmissing ⟨e, heK, he⟩ with
        ⟨carrier, hcarrierK, hcarrier, hunique⟩
      exact hef ((hunique heK he).trans (hunique hfK hf).symm)
    · intro hmissing
      rcases edgeSetIsEndpoint_of_missing_right_of_component_meets
          hvalid hK hmissing ⟨e, heK, he⟩ with
        ⟨carrier, hcarrierK, hcarrier, hunique⟩
      exact hef ((hunique heK he).trans (hunique hfK hf).symm)
  · rintro ⟨⟨e, heK, he⟩, halphaPresent, hbetaPresent⟩
    have hexistsAlpha : ∃ f, Incident v f ∧ a.color f = some alpha := by
      by_contra hno
      apply halphaPresent
      intro f hf hfalpha
      exact hno ⟨f, hf, hfalpha⟩
    have hexistsBeta : ∃ f, Incident v f ∧ a.color f = some beta := by
      by_contra hno
      apply hbetaPresent
      intro f hf hfbeta
      exact hno ⟨f, hf, hfbeta⟩
    rcases hexistsAlpha with ⟨falpha, hfalphaInc, hfalpha⟩
    rcases hexistsBeta with ⟨fbeta, hfbetaInc, hfbeta⟩
    have hfalphaK := mem_component_of_mem_of_incident_supported
      a hK heK he hfalphaInc (Or.inl hfalpha)
    have hfbetaK := mem_component_of_mem_of_incident_supported
      a hK heK he hfbetaInc (Or.inr hfbeta)
    refine ⟨falpha, fbeta, hfalphaK, hfbetaK, hfalphaInc,
      hfbetaInc, ?_⟩
    intro hEq
    subst fbeta
    exact halphabeta (Option.some.inj (hfalpha.symm.trans hfbeta))

/-- Every met vertex of a proper physical two-color component is exactly in
the local path/cycle dichotomy: endpoint or internal. -/
theorem endpoint_or_internal_of_component_meets
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet} {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hmeets : EdgeSetMeetsVertex K v) :
    EdgeSetIsEndpoint K v ∨ EdgeSetIsInternal K v := by
  classical
  by_cases halpha : a.MissingAt v alpha
  · exact Or.inl <|
      edgeSetIsEndpoint_of_missing_left_of_component_meets
        hvalid hK halpha hmeets
  · by_cases hbeta : a.MissingAt v beta
    · exact Or.inl <|
        edgeSetIsEndpoint_of_missing_right_of_component_meets
          hvalid hK hbeta hmeets
    · exact Or.inr <|
        (edgeSetIsInternal_iff_meets_and_present_both
          hvalid hK halphabeta).2 ⟨hmeets, halpha, hbeta⟩

section Swap

variable [DecidableEq C]

/-- Swapping a supported edge set that is locally internal or absent
preserves partial properness. -/
theorem valid_swapOn_of_supported_internal_or_avoids
    (a : PartialEdgeAssignment G C) {alpha beta : C}
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    (hvalid : a.Valid)
    (hsupported :
      ∀ ⦃e⦄, e ∈ K → a.TwoColorSupported alpha beta e)
    (hbalanced :
      ∀ v, EdgeSetIsInternal K v ∨ EdgeSetAvoidsVertex K v) :
    (a.swapOn alpha beta K).Valid :=
  valid_swapOn_of_boundaryClosed a K hvalid
    (twoColorBoundaryClosed_of_supported_internal_or_avoids
      a hvalid hsupported hbalanced)

/-- Swapping an edge set that avoids a vertex preserves every missing-color
predicate at that vertex, in both directions. -/
theorem missingAt_swapOn_iff_of_avoidsVertex
    (a : PartialEdgeAssignment G C) (alpha beta : C) (K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {v : V} (havoid : EdgeSetAvoidsVertex K v)
    (c : C) :
    (a.swapOn alpha beta K).MissingAt v c ↔ a.MissingAt v c := by
  constructor
  · intro hswap e he
    have heK : e ∉ K := fun hmem ↦ havoid hmem he
    simpa [PartialEdgeAssignment.swapOn_color_of_not_mem a alpha beta K heK]
      using hswap e he
  · intro hold e he
    have heK : e ∉ K := fun hmem ↦ havoid hmem he
    simpa [PartialEdgeAssignment.swapOn_color_of_not_mem a alpha beta K heK]
      using hold e he

/-- At a component endpoint missing the first color, a full component swap
makes the second color missing. -/
theorem missingAt_right_swapOn_of_missing_left_of_component_meets
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)] {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta) (hmissing : a.MissingAt v alpha)
    (hmeets : EdgeSetMeetsVertex K v) :
    (a.swapOn alpha beta K).MissingAt v beta := by
  rcases hmeets with ⟨e, heK, he⟩
  intro f hf
  by_cases hfK : f ∈ K
  · have hfs := twoColorSupported_of_mem_component a hK hfK
    rcases hfs with hfalpha | hfbeta
    · exact (hmissing f hf hfalpha).elim
    · rw [PartialEdgeAssignment.swapOn_color_of_mem a alpha beta K hfK, hfbeta]
      simp [halphabeta]
  · rw [PartialEdgeAssignment.swapOn_color_of_not_mem a alpha beta K hfK]
    intro hfbeta
    apply hfK
    exact mem_component_of_mem_of_incident_supported a hK heK he hf
      (Or.inr hfbeta)

/-- At a component endpoint missing the second color, a full component swap
makes the first color missing. -/
theorem missingAt_left_swapOn_of_missing_right_of_component_meets
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)] {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta) (hmissing : a.MissingAt v beta)
    (hmeets : EdgeSetMeetsVertex K v) :
    (a.swapOn alpha beta K).MissingAt v alpha := by
  rcases hmeets with ⟨e, heK, he⟩
  intro f hf
  by_cases hfK : f ∈ K
  · have hfs := twoColorSupported_of_mem_component a hK hfK
    rcases hfs with hfalpha | hfbeta
    · rw [PartialEdgeAssignment.swapOn_color_of_mem a alpha beta K hfK, hfalpha]
      simp [Ne.symm halphabeta]
    · exact (hmissing f hf hfbeta).elim
  · rw [PartialEdgeAssignment.swapOn_color_of_not_mem a alpha beta K hfK]
    intro hfalpha
    apply hfK
    exact mem_component_of_mem_of_incident_supported a hK heK he hf
      (Or.inl hfalpha)

/-- Exact endpoint label transport for the first color.  At every vertex met
by the component, the first color is missing after the swap exactly when the
second color was missing before it. -/
theorem missingAt_left_swapOn_iff_of_component_meets
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)] {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta) (hmeets : EdgeSetMeetsVertex K v) :
    (a.swapOn alpha beta K).MissingAt v alpha ↔ a.MissingAt v beta := by
  constructor
  · intro hswap f hf hfbeta
    rcases hmeets with ⟨e, heK, he⟩
    have hfK := mem_component_of_mem_of_incident_supported
      a hK heK he hf (Or.inr hfbeta)
    apply hswap f hf
    rw [PartialEdgeAssignment.swapOn_color_of_mem a alpha beta K hfK,
      hfbeta]
    simp
  · intro hmissing
    exact missingAt_left_swapOn_of_missing_right_of_component_meets
      a hK halphabeta hmissing hmeets

/-- Exact endpoint label transport for the second color. -/
theorem missingAt_right_swapOn_iff_of_component_meets
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)] {v : V}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta) (hmeets : EdgeSetMeetsVertex K v) :
    (a.swapOn alpha beta K).MissingAt v beta ↔ a.MissingAt v alpha := by
  constructor
  · intro hswap f hf hfalpha
    rcases hmeets with ⟨e, heK, he⟩
    have hfK := mem_component_of_mem_of_incident_supported
      a hK heK he hf (Or.inl hfalpha)
    apply hswap f hf
    rw [PartialEdgeAssignment.swapOn_color_of_mem a alpha beta K hfK,
      hfalpha]
    simp
  · intro hmissing
    exact missingAt_right_swapOn_of_missing_left_of_component_meets
      a hK halphabeta hmissing hmeets

/-- Swapping `alpha` and `beta` leaves every third-color missing predicate
unchanged, whether or not the component meets the vertex. -/
theorem missingAt_other_swapOn_iff
    (a : PartialEdgeAssignment G C) {alpha beta c : C}
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)] {v : V}
    (hcalpha : c ≠ alpha) (hcbeta : c ≠ beta) :
    (a.swapOn alpha beta K).MissingAt v c ↔ a.MissingAt v c := by
  constructor
  · intro hswap e he
    by_cases heK : e ∈ K
    · intro hec
      apply hswap e he
      rw [PartialEdgeAssignment.swapOn_color_of_mem a alpha beta K heK, hec]
      simp [Equiv.swap_apply_of_ne_of_ne hcalpha hcbeta]
    · intro hec
      apply hswap e he
      simpa [PartialEdgeAssignment.swapOn_color_of_not_mem
        a alpha beta K heK] using hec
  · intro hold e he
    by_cases heK : e ∈ K
    · intro hswapc
      apply hold e he
      rw [PartialEdgeAssignment.swapOn_color_of_mem
        a alpha beta K heK] at hswapc
      cases hecolor : a.color e with
      | none => simp [hecolor] at hswapc
      | some d =>
          have hdc : Equiv.swap alpha beta d = c :=
            Option.some.inj (by simpa [hecolor] using hswapc)
          have hdc' : d = c := by
            rw [Equiv.swap_apply_eq_iff,
              Equiv.swap_apply_of_ne_of_ne hcalpha hcbeta] at hdc
            exact hdc
          exact congrArg some hdc'
    · intro hswapc
      apply hold e he
      simpa [PartialEdgeAssignment.swapOn_color_of_not_mem
        a alpha beta K heK] using hswapc

/-- Swapping a genuine two-color component preserves every missing-color
predicate at an internal vertex of that component.

Internality and properness supply one incident edge of each component color.
The swap exchanges those two witnesses, so neither component color becomes
missing; every other color is covered by `missingAt_other_swapOn_iff`. -/
theorem missingAt_swapOn_iff_of_component_internal
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)] {v : V}
    (hvalid : a.Valid)
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hinternal : EdgeSetIsInternal K v) (c : C) :
    (a.swapOn alpha beta K).MissingAt v c ↔ a.MissingAt v c := by
  have hpresent :=
    (edgeSetIsInternal_iff_meets_and_present_both
      hvalid hK halphabeta).1 hinternal
  rcases hpresent.1 with ⟨carrier, hcarrierK, hcarrierInc⟩
  obtain ⟨ealpha, healphaInc, healphaColor⟩ :=
    exists_incident_colored_edge_of_not_missing a hpresent.2.1
  obtain ⟨ebeta, hebetaInc, hebetaColor⟩ :=
    exists_incident_colored_edge_of_not_missing a hpresent.2.2
  have healphaK : ealpha ∈ K :=
    mem_component_of_mem_of_incident_supported a hK hcarrierK hcarrierInc
      healphaInc (Or.inl healphaColor)
  have hebetaK : ebeta ∈ K :=
    mem_component_of_mem_of_incident_supported a hK hcarrierK hcarrierInc
      hebetaInc (Or.inr hebetaColor)
  have hafterAlpha : ¬(a.swapOn alpha beta K).MissingAt v alpha := by
    intro hmissing
    apply hmissing ebeta hebetaInc
    rw [PartialEdgeAssignment.swapOn_color_of_mem
      a alpha beta K hebetaK, hebetaColor]
    simp
  have hafterBeta : ¬(a.swapOn alpha beta K).MissingAt v beta := by
    intro hmissing
    apply hmissing ealpha healphaInc
    rw [PartialEdgeAssignment.swapOn_color_of_mem
      a alpha beta K healphaK, healphaColor]
    simp
  by_cases hcalpha : c = alpha
  · subst c
    constructor
    · exact fun h ↦ (hafterAlpha h).elim
    · exact fun h ↦ (hpresent.2.1 h).elim
  · by_cases hcbeta : c = beta
    · subst c
      constructor
      · exact fun h ↦ (hafterBeta h).elim
      · exact fun h ↦ (hpresent.2.2 h).elim
    · exact missingAt_other_swapOn_iff a K hcalpha hcbeta

/-- A genuine component which is internal at every vertex it meets preserves
the complete missing-color map when swapped.  This is the abstract interface
needed for a whole alternating-cycle exchange; global cycle classification is
kept separate in `TwoColorPath`. -/
theorem missingAt_swapOn_iff_of_component_internal_or_avoids
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)]
    (hvalid : a.Valid)
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hbalanced : ∀ v, EdgeSetIsInternal K v ∨ EdgeSetAvoidsVertex K v)
    (v : V) (c : C) :
    (a.swapOn alpha beta K).MissingAt v c ↔ a.MissingAt v c := by
  rcases hbalanced v with hinternal | havoids
  · exact missingAt_swapOn_iff_of_component_internal
      a hvalid hK halphabeta hinternal c
  · exact missingAt_swapOn_iff_of_avoidsVertex
      a alpha beta K havoids c

/-- Connectedness is unnecessary for missing-map preservation.  If every
selected edge has one of the two swapped colors and a vertex is internal to
the selected set, validity forces its two selected incident edges to have
opposite colors.  Swapping therefore preserves all missing-color predicates
at that vertex. -/
theorem missingAt_swapOn_iff_of_supported_internal
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)] {v : V}
    (hvalid : a.Valid) (_halphabeta : alpha ≠ beta)
    (hsupported : ∀ ⦃e⦄, e ∈ K → a.TwoColorSupported alpha beta e)
    (hinternal : EdgeSetIsInternal K v) (c : C) :
    (a.swapOn alpha beta K).MissingAt v c ↔ a.MissingAt v c := by
  rcases hinternal with
    ⟨e, f, heK, hfK, heInc, hfInc, hef⟩
  have heSupported := hsupported heK
  have hfSupported := hsupported hfK
  have hopposite :
      (a.color e = some alpha ∧ a.color f = some beta) ∨
        (a.color e = some beta ∧ a.color f = some alpha) := by
    rcases heSupported with healpha | hebeta
    · rcases hfSupported with hfalpha | hfbeta
      · exact (hef (edge_eq_of_incident_of_color_eq
          hvalid heInc hfInc healpha hfalpha)).elim
      · exact Or.inl ⟨healpha, hfbeta⟩
    · rcases hfSupported with hfalpha | hfbeta
      · exact Or.inr ⟨hebeta, hfalpha⟩
      · exact (hef (edge_eq_of_incident_of_color_eq
          hvalid heInc hfInc hebeta hfbeta)).elim
  obtain ⟨ealpha, ebeta, healphaK, hebetaK,
      healphaInc, hebetaInc, healphaColor, hebetaColor⟩ :
      ∃ ealpha ebeta,
        ealpha ∈ K ∧ ebeta ∈ K ∧
        Incident v ealpha ∧ Incident v ebeta ∧
        a.color ealpha = some alpha ∧ a.color ebeta = some beta := by
    rcases hopposite with h | h
    · exact ⟨e, f, heK, hfK, heInc, hfInc, h.1, h.2⟩
    · exact ⟨f, e, hfK, heK, hfInc, heInc, h.2, h.1⟩
  have hbeforeAlpha : ¬a.MissingAt v alpha := by
    intro hmissing
    exact hmissing ealpha healphaInc healphaColor
  have hbeforeBeta : ¬a.MissingAt v beta := by
    intro hmissing
    exact hmissing ebeta hebetaInc hebetaColor
  have hafterAlpha : ¬(a.swapOn alpha beta K).MissingAt v alpha := by
    intro hmissing
    apply hmissing ebeta hebetaInc
    rw [PartialEdgeAssignment.swapOn_color_of_mem
      a alpha beta K hebetaK, hebetaColor]
    simp
  have hafterBeta : ¬(a.swapOn alpha beta K).MissingAt v beta := by
    intro hmissing
    apply hmissing ealpha healphaInc
    rw [PartialEdgeAssignment.swapOn_color_of_mem
      a alpha beta K healphaK, healphaColor]
    simp
  by_cases hcalpha : c = alpha
  · subst c
    constructor
    · exact fun h ↦ (hafterAlpha h).elim
    · exact fun h ↦ (hbeforeAlpha h).elim
  · by_cases hcbeta : c = beta
    · subst c
      constructor
      · exact fun h ↦ (hafterBeta h).elim
      · exact fun h ↦ (hbeforeBeta h).elim
    · exact missingAt_other_swapOn_iff a K hcalpha hcbeta

/-- A balanced union of supported two-color components preserves the entire
missing map.  This covers a disjoint union of alternating cycles and is the
form needed to compare an owner-to-owner path swap with the complementary
all-cycle swap.  Properness of the swapped assignment remains the separate
`TwoColorBoundaryClosed` obligation from `PartialSwap`. -/
theorem missingAt_swapOn_iff_of_supported_internal_or_avoids
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    [DecidablePred (· ∈ K)]
    (hvalid : a.Valid) (halphabeta : alpha ≠ beta)
    (hsupported : ∀ ⦃e⦄, e ∈ K → a.TwoColorSupported alpha beta e)
    (hbalanced : ∀ v, EdgeSetIsInternal K v ∨ EdgeSetAvoidsVertex K v)
    (v : V) (c : C) :
    (a.swapOn alpha beta K).MissingAt v c ↔ a.MissingAt v c := by
  rcases hbalanced v with hinternal | havoids
  · exact missingAt_swapOn_iff_of_supported_internal
      a hvalid halphabeta hsupported hinternal c
  · exact missingAt_swapOn_iff_of_avoidsVertex
      a alpha beta K havoids c

end Swap

end PartialEdgeAssignment

end TotalColoring
