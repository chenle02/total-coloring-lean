import TotalColoring.FanReachability
import TotalColoring.TwoColorEndpointCapacity

/-!
# Dependency transport through two-color exchanges

This module isolates the relation-theoretic part of the recentering and
crossing arguments.  A swap preserves an old center dependency whenever the
dependency color is different from both exchanged colors.  Two useful
criteria force that difference:

* neither exchanged color is missing at the old source; or
* the first color is present at the old source and no non-distinguished
  center edge has the second color.

The corresponding lemmas lift step preservation to the entire old canonical
reachable set.  A final location lemma says that the head of a colored center
edge cannot already be reachable when its color is missing nowhere on the
old reachable set.

These statements are purely local.  They make no maximality, criticality, or
coloring-existence claim.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Swapping two colors preserves a center dependency whose source misses
neither of the exchanged colors. -/
theorem centerDependency_swapOn_of_source_present
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center source target : V} {alpha beta : C}
    (hdep : a.CenterDependency J center source target)
    (halpha : ¬a.MissingAt source alpha)
    (hbeta : ¬a.MissingAt source beta) :
    (a.swapOn alpha beta K).CenterDependency J center source target := by
  rcases hdep with ⟨edge, color, hends, hedgeJ, hedgeColor, hmissing⟩
  have hcolorAlpha : color ≠ alpha := by
    intro hEq
    subst color
    exact halpha hmissing
  have hcolorBeta : color ≠ beta := by
    intro hEq
    subst color
    exact hbeta hmissing
  refine ⟨edge, color, hends, hedgeJ, ?_, ?_⟩
  · by_cases hedgeK : edge ∈ K
    · rw [swapOn_color_of_mem a alpha beta K hedgeK, hedgeColor]
      simp [Equiv.swap_apply_of_ne_of_ne hcolorAlpha hcolorBeta]
    · simpa [swapOn_color_of_not_mem a alpha beta K hedgeK] using hedgeColor
  · exact (missingAt_other_swapOn_iff
      a K hcolorAlpha hcolorBeta).2 hmissing

/-- A full component swap cannot create a hole of either exchanged color at
a vertex which saw both colors before the swap. -/
theorem swapOn_component_preserves_present_both
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) {alpha beta : C}
    {K : Set G.edgeSet} [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphaBeta : alpha ≠ beta) {vertex : V}
    (halpha : ¬a.MissingAt vertex alpha)
    (hbeta : ¬a.MissingAt vertex beta) :
    ¬(a.swapOn alpha beta K).MissingAt vertex alpha ∧
      ¬(a.swapOn alpha beta K).MissingAt vertex beta := by
  by_cases hmeets : EdgeSetMeetsVertex K vertex
  · constructor
    · intro hnew
      exact hbeta
        ((missingAt_left_swapOn_iff_of_component_meets
          a hK halphaBeta hmeets).1 hnew)
    · intro hnew
      exact halpha
        ((missingAt_right_swapOn_iff_of_component_meets
          a hK halphaBeta hmeets).1 hnew)
  · have havoid : EdgeSetAvoidsVertex K vertex :=
      edgeSetAvoidsVertex_iff_not_meets.mpr hmeets
    constructor
    · intro hnew
      exact halpha
        ((missingAt_swapOn_iff_of_avoidsVertex
          a alpha beta K havoid alpha).1 hnew)
    · intro hnew
      exact hbeta
        ((missingAt_swapOn_iff_of_avoidsVertex
          a alpha beta K havoid beta).1 hnew)

/-- A valid coloring with an incident carrier of `beta` has no other
incident `beta`-edge.  In particular, if that carrier lies in `J`, no
non-`J` center edge has color `beta`. -/
theorem no_outside_center_color_of_incident_carrier
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {J : Set G.edgeSet} {center : V} {beta : C} {carrier : G.edgeSet}
    (hcarrierCenter : Incident center carrier)
    (hcarrierJ : carrier ∈ J)
    (hcarrierColor : a.color carrier = some beta) :
    ∀ ⦃edge : G.edgeSet⦄, Incident center edge → edge ∉ J →
      a.color edge ≠ some beta := by
  intro edge hedgeCenter hedgeJ hedgeColor
  have hedgeEq : edge = carrier :=
    edge_eq_of_incident_of_color_eq hvalid hedgeCenter hcarrierCenter
      hedgeColor hcarrierColor
  exact hedgeJ (hedgeEq ▸ hcarrierJ)

/-- A center dependency survives a swap when the first color is present at
its source and the second color occurs on no non-`J` center edge. -/
theorem centerDependency_swapOn_of_source_present_left_of_no_outside_right
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center source target : V} {alpha beta : C}
    (hdep : a.CenterDependency J center source target)
    (halpha : ¬a.MissingAt source alpha)
    (hnoBeta : ∀ ⦃edge : G.edgeSet⦄, Incident center edge → edge ∉ J →
      a.color edge ≠ some beta) :
    (a.swapOn alpha beta K).CenterDependency J center source target := by
  rcases hdep with ⟨edge, color, hends, hedgeJ, hedgeColor, hmissing⟩
  have hedgeCenter : Incident center edge := by
    change center ∈ (edge : Sym2 V)
    rw [hends]
    exact Sym2.mem_mk_left center target
  have hcolorAlpha : color ≠ alpha := by
    intro hEq
    subst color
    exact halpha hmissing
  have hcolorBeta : color ≠ beta := by
    intro hEq
    subst color
    exact hnoBeta hedgeCenter hedgeJ hedgeColor
  refine ⟨edge, color, hends, hedgeJ, ?_, ?_⟩
  · by_cases hedgeK : edge ∈ K
    · rw [swapOn_color_of_mem a alpha beta K hedgeK, hedgeColor]
      simp [Equiv.swap_apply_of_ne_of_ne hcolorAlpha hcolorBeta]
    · simpa [swapOn_color_of_not_mem a alpha beta K hedgeK] using hedgeColor
  · exact (missingAt_other_swapOn_iff
      a K hcolorAlpha hcolorBeta).2 hmissing

/-- If both swap colors are present at every old reachable source, every old
reachable vertex remains reachable after the swap. -/
theorem centerReachable_swapOn_of_reachable_sources_present
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center root target : V} {alpha beta : C}
    (hpresent : ∀ ⦃source : V⦄,
      a.CenterReachable J center root source →
        ¬a.MissingAt source alpha ∧ ¬a.MissingAt source beta)
    (hreach : a.CenterReachable J center root target) :
    (a.swapOn alpha beta K).CenterReachable J center root target := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (centerDependency_swapOn_of_source_present
          a J K hstep (hpresent hprefix).1 (hpresent hprefix).2)

/-- A source-sensitive transport of every old dependency step lifts to a
transport of the whole old reachable relation.  The source reachability
hypothesis is deliberately stated in the old assignment; this supports
composing several swaps while retaining one fixed old path. -/
theorem centerReachable_of_dependency_transport
    {a b : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root target : V}
    (htransport : ∀ ⦃source next : V⦄,
      a.CenterReachable J center root source →
        a.CenterDependency J center source next →
          b.CenterDependency J center source next)
    (hreach : a.CenterReachable J center root target) :
    b.CenterReachable J center root target := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      exact Relation.ReflTransGen.tail ih (htransport hprefix hstep)

/-- If the first swap color is present at every old reachable source and the
second occurs on no non-`J` center edge, every old reachable vertex remains
reachable after the swap. -/
theorem centerReachable_swapOn_of_reachable_sources_present_left_of_no_outside_right
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center root target : V} {alpha beta : C}
    (halpha : ∀ ⦃source : V⦄,
      a.CenterReachable J center root source →
        ¬a.MissingAt source alpha)
    (hnoBeta : ∀ ⦃edge : G.edgeSet⦄, Incident center edge → edge ∉ J →
      a.color edge ≠ some beta)
    (hreach : a.CenterReachable J center root target) :
    (a.swapOn alpha beta K).CenterReachable J center root target := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | tail hprefix hstep ih =>
      exact Relation.ReflTransGen.tail ih
        (centerDependency_swapOn_of_source_present_left_of_no_outside_right
          a J K hstep (halpha hprefix) hnoBeta)

/-- A colored center edge cannot have the root of a one-hole edge as its
other endpoint. -/
theorem centerTarget_ne_root_of_colored_of_oneHoleAt
    {a : PartialEdgeAssignment G C} {center root target : V}
    {hole edge : G.edgeSet} {color : C}
    (hholeEnds : (hole : Sym2 V) = s(center, root))
    (hhole : a.OneHoleAt hole)
    (hedgeEnds : (edge : Sym2 V) = s(center, target))
    (hedgeColor : a.color edge = some color) :
    target ≠ root := by
  intro htarget
  subst target
  have hedgeEq : edge = hole := centerEdge_eq_of_endpoints hedgeEnds hholeEnds
  have hnone : a.color hole = none := (hhole hole).2 rfl
  rw [hedgeEq, hnone] at hedgeColor
  simp at hedgeColor

/-- If a colored center edge has color `color`, and `color` is present at
every vertex of the old reachable set, then its nonroot head is not already
reachable.  Otherwise the final dependency into that head would use the same
simple center edge and exhibit an old reachable source missing `color`. -/
theorem not_centerReachable_of_center_edge_color_present_on_reachable
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root target : V} {edge : G.edgeSet} {color : C}
    (htargetRoot : target ≠ root)
    (hedgeEnds : (edge : Sym2 V) = s(center, target))
    (hedgeColor : a.color edge = some color)
    (hpresent : ∀ ⦃source : V⦄,
      a.CenterReachable J center root source →
        ¬a.MissingAt source color) :
    ¬a.CenterReachable J center root target := by
  intro hreach
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | htail
  · exact htargetRoot hEq
  · rcases htail with ⟨source, hsource, hstep⟩
    rcases hstep with
      ⟨witness, witnessColor, hwitnessEnds, _hwitnessJ,
        hwitnessColor, hmissing⟩
    have hwitnessEq : witness = edge :=
      centerEdge_eq_of_endpoints hwitnessEnds hedgeEnds
    subst witness
    have hcolorEq : witnessColor = color :=
      Option.some.inj (hwitnessColor.symm.trans hedgeColor)
    subst witnessColor
    exact hpresent hsource hmissing

/-- Among three distinct vertices which miss `beta` but see `alpha`, one
`alpha`-`beta` component avoids a prescribed vertex at which `alpha` is
present.  Otherwise all three components contain the same incident
`alpha`-edge at the prescribed vertex and hence coincide, contradicting the
two-endpoint capacity of one finite physical component. -/
theorem exists_component_avoiding_vertex_of_three_missing
    [Fintype V] [DecidableEq V]
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {T : Set V} {center : V}
    (hthree : 3 ≤ T.ncard)
    (hbeta : ∀ ⦃leaf : V⦄, leaf ∈ T → a.MissingAt leaf beta)
    (halpha : ∀ ⦃leaf : V⦄, leaf ∈ T → ¬a.MissingAt leaf alpha)
    (hcenterAlpha : ¬a.MissingAt center alpha) :
    ∃ (leaf : V) (K : Set G.edgeSet),
      leaf ∈ T ∧
        a.IsTwoColorKempeComponent alpha beta K ∧
        EdgeSetIsEndpoint K leaf ∧
        EdgeSetAvoidsVertex K center := by
  classical
  have hgt : 2 < T.ncard := by omega
  rcases (Set.two_lt_ncard_iff (s := T)).mp hgt with
    ⟨p, q, r, hpT, hqT, hrT, hpq, hpr, hqr⟩
  have hdatum : ∀ ⦃leaf : V⦄, leaf ∈ T →
      ∃ K : Set G.edgeSet,
        a.IsTwoColorKempeComponent alpha beta K ∧
          EdgeSetIsEndpoint K leaf := by
    intro leaf hleaf
    rcases exists_incident_colored_edge_of_not_missing
        a (halpha hleaf) with ⟨edge, hedgeLeaf, hedgeColor⟩
    let K := a.TwoColorReachabilityClass alpha beta edge
    have hedgeSupported : a.TwoColorSupported alpha beta edge :=
      Or.inl hedgeColor
    have hK : a.IsTwoColorKempeComponent alpha beta K :=
      isTwoColorKempeComponent_reachabilityClass
        a alpha beta edge hedgeSupported
    have hedgeK : edge ∈ K :=
      root_mem_twoColorReachabilityClass a alpha beta edge
    have hmeets : EdgeSetMeetsVertex K leaf :=
      ⟨edge, hedgeK, hedgeLeaf⟩
    exact ⟨K, hK,
      edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK (hbeta hleaf) hmeets⟩
  rcases hdatum hpT with ⟨Kp, hKp, hpEnd⟩
  rcases hdatum hqT with ⟨Kq, hKq, hqEnd⟩
  rcases hdatum hrT with ⟨Kr, hKr, hrEnd⟩
  by_cases hpAvoid : EdgeSetAvoidsVertex Kp center
  · exact ⟨p, Kp, hpT, hKp, hpEnd, hpAvoid⟩
  by_cases hqAvoid : EdgeSetAvoidsVertex Kq center
  · exact ⟨q, Kq, hqT, hKq, hqEnd, hqAvoid⟩
  by_cases hrAvoid : EdgeSetAvoidsVertex Kr center
  · exact ⟨r, Kr, hrT, hKr, hrEnd, hrAvoid⟩
  have hpMeets : EdgeSetMeetsVertex Kp center :=
    not_not.mp (fun hnot ↦ hpAvoid
      (edgeSetAvoidsVertex_iff_not_meets.mpr hnot))
  have hqMeets : EdgeSetMeetsVertex Kq center :=
    not_not.mp (fun hnot ↦ hqAvoid
      (edgeSetAvoidsVertex_iff_not_meets.mpr hnot))
  have hrMeets : EdgeSetMeetsVertex Kr center :=
    not_not.mp (fun hnot ↦ hrAvoid
      (edgeSetAvoidsVertex_iff_not_meets.mpr hnot))
  rcases exists_incident_colored_edge_of_not_missing
      a hcenterAlpha with ⟨centerEdge, hcenterEdgeInc, hcenterEdgeColor⟩
  have hcenterEdgeMem : ∀ ⦃K : Set G.edgeSet⦄,
      a.IsTwoColorKempeComponent alpha beta K →
        EdgeSetMeetsVertex K center → centerEdge ∈ K := by
    intro K hK hmeets
    rcases hmeets with ⟨edge, hedgeK, hedgeInc⟩
    exact mem_component_of_mem_of_incident_supported
      a hK hedgeK hedgeInc hcenterEdgeInc (Or.inl hcenterEdgeColor)
  have hpCenter := hcenterEdgeMem hKp hpMeets
  have hqCenter := hcenterEdgeMem hKq hqMeets
  have hrCenter := hcenterEdgeMem hKr hrMeets
  have hKpq : Kp = Kq :=
    isTwoColorKempeComponent_eq_of_common_member
      a hKp hKq hpCenter hqCenter
  have hKpr : Kp = Kr :=
    isTwoColorKempeComponent_eq_of_common_member
      a hKp hKr hpCenter hrCenter
  rw [← hKpq] at hqEnd
  rw [← hKpr] at hrEnd
  rcases endpoint_triple_has_repetition_of_component
      hvalid hKp hpEnd hqEnd hrEnd with h | h | h
  · exact (hpq h).elim
  · exact (hpr h).elim
  · exact (hqr h).elim

end PartialEdgeAssignment

end TotalColoring
