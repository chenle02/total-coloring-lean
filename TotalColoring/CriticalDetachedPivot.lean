import TotalColoring.CriticalRootPivot
import TotalColoring.TwoColorPath

/-!
# Detaching the far side of a two-color path under a root pivot

Suppose an `alpha`--`gamma` component `C` contains the colored pivot spoke
`center--q`, and has an endpoint.  Its projected vertex graph is then a path,
so deleting the pivot spoke separates a well-defined `q`-side.  Suppose also
that a disjoint `alpha`--`gamma` component `K` meets the old root leaf.

The literal `gamma` root pivot removes `center--q` and colors the old root
spoke `center--r` with `gamma`.  Every two-color step starting on the `q`-side
therefore remains on that side: it cannot use the removed spoke, and it cannot
use the newly colored old-root spoke because neither endpoint of that spoke is
on the `q`-side.  Consequently the new component rooted at an `alpha`-edge at
`q` is a genuine off-center component contained in `C`.  It is disjoint from
`K`, and hence omits every marked edge of `K`, including a distinguished
`gamma`-carrier supplied by an application.

This is the coloring-specific graph-surgery seam for the `k = 2` branch.  It
does not assert that the two old components or the required endpoint exist;
those facts remain explicit hypotheses.
-/

namespace TotalColoring

universe u

/-- An edge of `C` lies wholly on the side of `q` after the projected edge
`pq` is deleted.  The existential proof records that every endpoint of the
edge is a vertex of the projected component graph. -/
def EdgeInDeletedSide {V : Type u} {G : SimpleGraph V}
    (C : Set G.edgeSet)
    (p q : {v : V // EdgeSetMeetsVertex C v})
    (edge : G.edgeSet) : Prop :=
  edge ∈ C ∧
    ∀ (v : V), Incident v edge →
      ∃ hv : EdgeSetMeetsVertex C v,
        (⟨v, hv⟩ : {w : V // EdgeSetMeetsVertex C w}) ∈
          DeletedEdgeSide (EdgeSetVertexGraph C) p q

/-- Equality of projected endpoint pairs forces equality of the underlying
simple-graph edges. -/
private theorem edge_eq_of_projected_pair_eq
    {V : Type u} {G : SimpleGraph V} {C : Set G.edgeSet}
    {edge cut : G.edgeSet}
    {x y p q : {v : V // EdgeSetMeetsVertex C v}}
    (hxy : x ≠ y) (hpq : p ≠ q)
    (hxEdge : Incident x.1 edge) (hyEdge : Incident y.1 edge)
    (hpCut : Incident p.1 cut) (hqCut : Incident q.1 cut)
    (hpairs : s(x, y) = s(p, q)) :
    edge = cut := by
  have hxyVal : x.1 ≠ y.1 := by
    intro h
    exact hxy (Subtype.ext h)
  have hpqVal : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  have hedgeEnds : (edge : Sym2 V) = s(x.1, y.1) :=
    (Sym2.mem_and_mem_iff hxyVal).mp ⟨hxEdge, hyEdge⟩
  have hcutEnds : (cut : Sym2 V) = s(p.1, q.1) :=
    (Sym2.mem_and_mem_iff hpqVal).mp ⟨hpCut, hqCut⟩
  have hpairsVal : s(x.1, y.1) = s(p.1, q.1) := by
    have hmap := congrArg
      (Sym2.map (fun z : {v : V // EdgeSetMeetsVertex C v} => z.1))
      hpairs
    simpa only [Sym2.map_mk] using hmap
  apply Subtype.ext
  exact hedgeEnds.trans (hpairsVal.trans hcutEnds.symm)

/-- If one endpoint of a component edge is on the deleted-edge side and the
edge is not the deleted edge itself, both endpoints are on that side. -/
theorem edgeInDeletedSide_of_incident
    {V : Type u} {G : SimpleGraph V} {C : Set G.edgeSet}
    {p q x : {v : V // EdgeSetMeetsVertex C v}}
    {cut edge : G.edgeSet}
    (hcutEnds : (cut : Sym2 V) = s(p.1, q.1))
    (hxSide : x ∈ DeletedEdgeSide (EdgeSetVertexGraph C) p q)
    (hedgeC : edge ∈ C) (hedgeCut : edge ≠ cut)
    (hxEdge : Incident x.1 edge) :
    EdgeInDeletedSide C p q edge := by
  have hpq : p ≠ q := by
    intro h
    have hadj : G.Adj p.1 q.1 := by
      rw [← G.mem_edgeSet, ← hcutEnds]
      exact cut.2
    exact hadj.ne (congrArg Subtype.val h)
  have hpCut : Incident p.1 cut := by
    change p.1 ∈ (cut : Sym2 V)
    rw [hcutEnds]
    exact Sym2.mem_mk_left p.1 q.1
  have hqCut : Incident q.1 cut := by
    change q.1 ∈ (cut : Sym2 V)
    rw [hcutEnds]
    exact Sym2.mem_mk_right p.1 q.1
  refine ⟨hedgeC, ?_⟩
  intro v hvEdge
  let y : {w : V // EdgeSetMeetsVertex C w} :=
    ⟨v, ⟨edge, hedgeC, hvEdge⟩⟩
  refine ⟨y.2, ?_⟩
  change y ∈ DeletedEdgeSide (EdgeSetVertexGraph C) p q
  by_cases hxy : x = y
  · simpa [hxy] using hxSide
  · have hxyAdj : (EdgeSetVertexGraph C).Adj x y :=
      ⟨hxy, ⟨edge, hedgeC, hxEdge, hvEdge⟩⟩
    apply mem_deletedEdgeSide_of_mem_of_adj_of_edge_ne hxSide hxyAdj
    intro hpairs
    apply hedgeCut
    exact edge_eq_of_projected_pair_eq hxy hpq hxEdge hvEdge
      hpCut hqCut hpairs

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

omit [Fintype V] [DecidableRel H.Adj] in
/-- A root pivot changes no color on the distinguished edge set: both the old
root and the pivot donor are outside that set. -/
theorem color_rootPivot_eq_of_mem_distinguished
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {edge : H.edgeSet} (hedgeJ : edge ∈ distinguishedEdgeSet H J) :
    (state.rootPivot next hstep).assignment.color edge =
      state.assignment.color edge := by
  classical
  have hedgeRoot : edge ≠ state.root.edge := by
    intro h
    apply state.rootOutside
    simpa [h] using hedgeJ
  have hedgeNext : edge ≠ next.edge := by
    intro h
    apply hstep.target_not_mem
    simpa [h] using hedgeJ
  rw [state.rootPivot_assignment]
  exact PartialEdgeAssignment.moveHole_color_of_ne
    state.assignment hedgeRoot hedgeNext

omit [Fintype V] [DecidableRel H.Adj] in
/-- In particular, every distinguished-set unused color remains unused after
a root pivot (and conversely). -/
theorem colorUnusedOn_rootPivot_iff
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    (color : ExtensionPalette D) :
    (state.rootPivot next hstep).assignment.ColorUnusedOn
        (distinguishedEdgeSet H J) color ↔
      state.assignment.ColorUnusedOn (distinguishedEdgeSet H J) color := by
  constructor
  · intro hnew edge hedgeJ hedgeColor
    apply hnew hedgeJ
    rw [state.color_rootPivot_eq_of_mem_distinguished next hstep hedgeJ]
    exact hedgeColor
  · intro hold edge hedgeJ hedgeColor
    apply hold hedgeJ
    rw [← state.color_rootPivot_eq_of_mem_distinguished next hstep hedgeJ]
    exact hedgeColor

omit [Fintype V] [DecidableRel H.Adj] in
/-- Unique distinguished carriers are unchanged by a root pivot. -/
theorem isUniqueColorOn_rootPivot_iff
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    (color : ExtensionPalette D) (carrier : H.edgeSet) :
    (state.rootPivot next hstep).assignment.IsUniqueColorOn
        (distinguishedEdgeSet H J) color carrier ↔
      state.assignment.IsUniqueColorOn
        (distinguishedEdgeSet H J) color carrier := by
  constructor
  · rintro ⟨hcarrierJ, hcarrierColor, hunique⟩
    refine ⟨hcarrierJ, ?_, ?_⟩
    · rw [← state.color_rootPivot_eq_of_mem_distinguished
        next hstep hcarrierJ]
      exact hcarrierColor
    · intro edge hedgeJ hedgeColor
      apply hunique hedgeJ
      rw [state.color_rootPivot_eq_of_mem_distinguished
        next hstep hedgeJ]
      exact hedgeColor
  · rintro ⟨hcarrierJ, hcarrierColor, hunique⟩
    refine ⟨hcarrierJ, ?_, ?_⟩
    · rw [state.color_rootPivot_eq_of_mem_distinguished
        next hstep hcarrierJ]
      exact hcarrierColor
    · intro edge hedgeJ hedgeColor
      apply hunique hedgeJ
      rw [← state.color_rootPivot_eq_of_mem_distinguished
        next hstep hedgeJ]
      exact hedgeColor

omit [DecidableRel H.Adj] in
/-- Root-pivot detachment.  The old component `C` is cut at the pivot donor,
while the newly colored old-root edge cannot be reached from the `q`-side
because its center endpoint is on the opposite side and its leaf is met by
the disjoint old component `K`.

The returned component is the physical `alpha`--`gamma` reachability class of
an `alpha`-edge at `q`.  It is contained in `C`, avoids the center, is
disjoint from `K`, and has `q` as its `gamma`-missing endpoint. -/
theorem exists_detached_component_rootPivot
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    (hnextColor : state.assignment.color next.edge = some gamma)
    {K C : Set H.edgeSet}
    (hK : state.assignment.IsTwoColorKempeComponent alpha gamma K)
    (hC : state.assignment.IsTwoColorKempeComponent alpha gamma C)
    (hdisjoint : Disjoint K C)
    (hrootK : EdgeSetMeetsVertex K state.root.leaf)
    (hnextC : next.edge ∈ C)
    {componentEndpoint : V}
    (hcomponentEndpoint : EdgeSetIsEndpoint C componentEndpoint)
    (hnextAlpha : ¬state.assignment.MissingAt next.leaf alpha) :
    ∃ Kq : Set H.edgeSet,
      (state.rootPivot next hstep).assignment.IsTwoColorKempeComponent
          alpha gamma Kq ∧
        Kq ⊆ C ∧
        Disjoint K Kq ∧
        EdgeSetIsEndpoint Kq next.leaf ∧
        EdgeSetAvoidsVertex Kq state.center ∧
        (state.rootPivot next hstep).assignment.MissingAt
          next.leaf gamma ∧
        ¬(state.rootPivot next hstep).assignment.MissingAt
          next.leaf alpha := by
  classical
  let pivot := state.rootPivot next hstep
  let a := state.assignment
  have hcenterC : EdgeSetMeetsVertex C state.center :=
    ⟨next.edge, hnextC, next.center_incident⟩
  have hqC : EdgeSetMeetsVertex C next.leaf :=
    ⟨next.edge, hnextC, next.leaf_incident⟩
  let p : {v : V // EdgeSetMeetsVertex C v} :=
    ⟨state.center, hcenterC⟩
  let q : {v : V // EdgeSetMeetsVertex C v} :=
    ⟨next.leaf, hqC⟩
  have hpqNe : p ≠ q := by
    intro h
    exact next.leaf_ne_center (congrArg Subtype.val h).symm
  have hpq : (EdgeSetVertexGraph C).Adj p q := by
    exact ⟨hpqNe,
      ⟨next.edge, hnextC, next.center_incident, next.leaf_incident⟩⟩
  have hbridge : (EdgeSetVertexGraph C).IsBridge s(p, q) :=
    PartialEdgeAssignment.edgeSetVertexGraph_isBridge_of_endpoint
      state.valid hC hcomponentEndpoint hpq
  have hpNotSide :
      p ∉ DeletedEdgeSide (EdgeSetVertexGraph C) p q :=
    left_not_mem_deletedEdgeSide_of_isBridge hbridge
  have hqSide : q ∈ DeletedEdgeSide (EdgeSetVertexGraph C) p q :=
    right_mem_deletedEdgeSide (EdgeSetVertexGraph C) p q
  have hnextEnds : (next.edge : Sym2 V) = s(p.1, q.1) := by
    simpa [p, q] using next.endpoints

  have hCavoidRoot : EdgeSetAvoidsVertex C state.root.leaf := by
    intro edge hedgeC hedgeRoot
    rcases hrootK with ⟨rootEdge, hrootEdgeK, hrootEdgeInc⟩
    have hedgeSupported :
        a.TwoColorSupported alpha gamma edge :=
      PartialEdgeAssignment.twoColorSupported_of_mem_component
        a hC hedgeC
    have hedgeK : edge ∈ K :=
      PartialEdgeAssignment.mem_component_of_mem_of_incident_supported
        a hK hrootEdgeK hrootEdgeInc hedgeRoot hedgeSupported
    exact (Set.disjoint_left.mp hdisjoint hedgeK) hedgeC

  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      a hnextAlpha with ⟨qEdge, hqEdgeInc, hqEdgeColor⟩
  have hqEdgeNeNext : qEdge ≠ next.edge := by
    intro h
    subst qEdge
    exact halphaGamma
      (Option.some.inj (hqEdgeColor.symm.trans hnextColor))
  have hqEdgeNeRoot : qEdge ≠ state.root.edge := by
    intro h
    subst qEdge
    have hrootNone : a.color state.root.edge = none :=
      (state.oneHole state.root.edge).2 rfl
    rw [hrootNone] at hqEdgeColor
    simp at hqEdgeColor
  have hqEdgeC : qEdge ∈ C :=
    PartialEdgeAssignment.mem_component_of_mem_of_incident_supported
      a hC hnextC next.leaf_incident hqEdgeInc (Or.inl hqEdgeColor)
  have hqEdgeSide : EdgeInDeletedSide C p q qEdge := by
    apply edgeInDeletedSide_of_incident hnextEnds hqSide hqEdgeC
      hqEdgeNeNext
    exact hqEdgeInc
  have hqEdgeColorPivot : pivot.assignment.color qEdge = some alpha := by
    change (state.rootPivot next hstep).assignment.color qEdge = some alpha
    rw [state.rootPivot_assignment]
    exact (PartialEdgeAssignment.moveHole_color_of_ne
      a hqEdgeNeRoot hqEdgeNeNext).trans hqEdgeColor

  have hnextNone : pivot.assignment.color next.edge = none := by
    change (state.rootPivot next hstep).assignment.color next.edge = none
    rw [state.rootPivot_assignment]
    exact PartialEdgeAssignment.moveHole_color_donor a
      (CenterSpoke.ne_iff_edge_ne.mp hstep.ne).symm

  have hsideStep : ∀ {edge nextEdge : H.edgeSet},
      EdgeInDeletedSide C p q edge →
      pivot.assignment.TwoColorStep alpha gamma edge nextEdge →
      EdgeInDeletedSide C p q nextEdge := by
    intro edge nextEdge hedgeSide htwoStep
    rcases SimpleGraph.lineGraph_adj_iff_exists.mp htwoStep.1 with
      ⟨_hedgesNe, shared, hsharedEdge, hsharedNext⟩
    rcases hedgeSide.2 shared hsharedEdge with
      ⟨hsharedC, hsharedSide⟩
    have hnextEdgeNeDonor : nextEdge ≠ next.edge := by
      intro h
      subst nextEdge
      rcases htwoStep.2.2 with hcolor | hcolor
      · rw [hnextNone] at hcolor
        simp at hcolor
      · rw [hnextNone] at hcolor
        simp at hcolor
    have hnextEdgeNeRoot : nextEdge ≠ state.root.edge := by
      intro h
      subst nextEdge
      rcases state.root.incident_iff.mp hsharedNext with
        hsharedCenter | hsharedRoot
      · apply hpNotSide
        subst shared
        have hEq :
            (⟨state.center, hsharedC⟩ :
              {v : V // EdgeSetMeetsVertex C v}) = p :=
          Subtype.ext rfl
        exact hEq ▸ hsharedSide
      · subst shared
        exact (edgeSetAvoidsVertex_iff_not_meets.mp hCavoidRoot) hsharedC
    have hcolorSame :
        pivot.assignment.color nextEdge = a.color nextEdge := by
      change (state.rootPivot next hstep).assignment.color nextEdge =
        a.color nextEdge
      rw [state.rootPivot_assignment]
      exact PartialEdgeAssignment.moveHole_color_of_ne a
        hnextEdgeNeRoot hnextEdgeNeDonor
    have hnextSupportedOld :
        a.TwoColorSupported alpha gamma nextEdge := by
      rcases htwoStep.2.2 with hcolor | hcolor
      · exact Or.inl (hcolorSame.symm.trans hcolor)
      · exact Or.inr (hcolorSame.symm.trans hcolor)
    have hnextEdgeC : nextEdge ∈ C :=
      PartialEdgeAssignment.mem_component_of_mem_of_incident_supported
        a hC hedgeSide.1 hsharedEdge hsharedNext hnextSupportedOld
    apply edgeInDeletedSide_of_incident hnextEnds hsharedSide hnextEdgeC
      hnextEdgeNeDonor
    exact hsharedNext

  let Kq := pivot.assignment.TwoColorReachabilityClass alpha gamma qEdge
  have hKq : pivot.assignment.IsTwoColorKempeComponent alpha gamma Kq :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      pivot.assignment alpha gamma qEdge (Or.inl hqEdgeColorPivot)
  have hKqSide : ∀ {edge : H.edgeSet}, edge ∈ Kq →
      EdgeInDeletedSide C p q edge := by
    intro edge hedgeKq
    change pivot.assignment.TwoColorReachable alpha gamma qEdge edge at hedgeKq
    induction hedgeKq with
    | refl => exact hqEdgeSide
    | tail hreach htwoStep ih => exact hsideStep ih htwoStep
  have hKqSubset : Kq ⊆ C := by
    intro edge hedgeKq
    exact (hKqSide hedgeKq).1
  have hKKq : Disjoint K Kq := by
    apply Set.disjoint_left.mpr
    intro edge hedgeK hedgeKq
    exact (Set.disjoint_left.mp hdisjoint hedgeK) (hKqSubset hedgeKq)
  have hqEdgeKq : qEdge ∈ Kq :=
    pivot.assignment.root_mem_twoColorReachabilityClass alpha gamma qEdge
  have hqMeetsKq : EdgeSetMeetsVertex Kq next.leaf :=
    ⟨qEdge, hqEdgeKq, hqEdgeInc⟩
  have hqGamma : pivot.assignment.MissingAt next.leaf gamma := by
    have hmissing := (state.missingAt_pivotColor_rootPivot_iff
      next hstep hnextColor next.leaf).2 (Or.inl rfl)
    simpa [pivot] using hmissing
  have hqAlpha : ¬pivot.assignment.MissingAt next.leaf alpha := by
    intro hmissing
    apply hnextAlpha
    exact (state.missingAt_otherColor_rootPivot_iff
      next hstep hnextColor halphaGamma next.leaf).1 (by
        simpa [pivot] using hmissing)
  have hqEndpoint : EdgeSetIsEndpoint Kq next.leaf :=
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
      pivot.valid hKq hqGamma hqMeetsKq
  have hKqAvoidCenter : EdgeSetAvoidsVertex Kq state.center := by
    intro edge hedgeKq hedgeCenter
    rcases (hKqSide hedgeKq).2 state.center hedgeCenter with
      ⟨hcenterMeet, hcenterSide⟩
    apply hpNotSide
    have hEq :
        (⟨state.center, hcenterMeet⟩ :
          {v : V // EdgeSetMeetsVertex C v}) = p :=
      Subtype.ext rfl
    exact hEq ▸ hcenterSide
  exact ⟨Kq, hKq, hKqSubset, hKKq, hqEndpoint,
    hKqAvoidCenter, hqGamma, hqAlpha⟩

omit [DecidableRel H.Adj] in
/-- Marked-edge form of root-pivot detachment.  In the `k = 2` application,
`marked` is the unique distinguished `gamma`-carrier `j_gamma` contained in
the old off-center component `K`. -/
theorem exists_detached_component_rootPivot_omits_marked
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    (hnextColor : state.assignment.color next.edge = some gamma)
    {K C : Set H.edgeSet}
    (hK : state.assignment.IsTwoColorKempeComponent alpha gamma K)
    (hC : state.assignment.IsTwoColorKempeComponent alpha gamma C)
    (hdisjoint : Disjoint K C)
    (hrootK : EdgeSetMeetsVertex K state.root.leaf)
    (hnextC : next.edge ∈ C)
    {componentEndpoint : V}
    (hcomponentEndpoint : EdgeSetIsEndpoint C componentEndpoint)
    (hnextAlpha : ¬state.assignment.MissingAt next.leaf alpha)
    {marked : H.edgeSet} (hmarkedK : marked ∈ K)
    (halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha) :
    ∃ Kq : Set H.edgeSet,
      (state.rootPivot next hstep).assignment.IsTwoColorKempeComponent
          alpha gamma Kq ∧
        EdgeSetIsEndpoint Kq next.leaf ∧
        EdgeSetAvoidsVertex Kq state.center ∧
        marked ∉ Kq ∧
        (state.rootPivot next hstep).assignment.MissingAt
          next.leaf gamma ∧
        ¬(state.rootPivot next hstep).assignment.MissingAt
          next.leaf alpha ∧
        (state.rootPivot next hstep).assignment.ColorUnusedOn
          (distinguishedEdgeSet H J) alpha := by
  rcases state.exists_detached_component_rootPivot next hstep
      halphaGamma hnextColor hK hC hdisjoint hrootK hnextC
      hcomponentEndpoint hnextAlpha with
    ⟨Kq, hKq, _hKqSubset, hKKq, hqEndpoint, hqAvoid,
      hqGamma, hqAlpha⟩
  have hmarkedNot : marked ∉ Kq :=
    (Set.disjoint_left.mp hKKq hmarkedK)
  have halphaUnusedPivot :
      (state.rootPivot next hstep).assignment.ColorUnusedOn
        (distinguishedEdgeSet H J) alpha :=
    (state.colorUnusedOn_rootPivot_iff next hstep alpha).2 halphaUnused
  exact ⟨Kq, hKq, hqEndpoint, hqAvoid, hmarkedNot,
    hqGamma, hqAlpha, halphaUnusedPivot⟩

end OrientedOneHoleState

end TotalColoring
