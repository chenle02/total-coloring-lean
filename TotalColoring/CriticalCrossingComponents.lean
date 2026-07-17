import TotalColoring.CriticalCrossingExternality

/-!
# Physical component placement in the `k = 2` crossing branch

This module turns the exact three-hole/two-external-source data into the two
physical components required before the root-pivot detachment step.

First, among three `gamma`-holes at which `alpha` is present, endpoint
capacity produces an `alpha`--`gamma` component avoiding the center.  The
crossing externality theorem then makes its affected endpoint set exactly the
two external sources.  In particular it meets the old root and crosses the
unique distinguished `gamma`-carrier.

Second, root a component at the literal center `alpha`-edge.  The literal
center `gamma`-target edge belongs to that same component.  A third
`gamma`-hole exists outside the two-source external finset.  Its own physical
component is either the center component or disjoint from it.  In the
disjoint branch it avoids the center, so crossing externality would make that
third hole external, a contradiction.  Hence the third hole is an endpoint
of the through-center component.

The hypotheses are exactly the post-rotation direct-entry interface used in
the hand audit.  No claim is made that an arbitrary component meeting a
triple is automatically off-center or external.
-/

namespace TotalColoring

universe u v

/-- An endpoint is, in particular, met by its edge set. -/
theorem edgeSetMeetsVertex_of_edgeSetIsEndpoint
    {V : Type u} {G : SimpleGraph V} {K : Set G.edgeSet} {vertex : V}
    (hendpoint : EdgeSetIsEndpoint K vertex) :
    EdgeSetMeetsVertex K vertex := by
  rcases hendpoint with ⟨edge, hedgeK, hedgeVertex, _hunique⟩
  exact ⟨edge, hedgeK, hedgeVertex⟩

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Genuine components for one ordered color pair are equal or edge-disjoint.
This is the set-theoretic partition form of component uniqueness. -/
theorem isTwoColorKempeComponent_eq_or_disjoint
    (a : PartialEdgeAssignment G C) {alpha beta : C}
    {K L : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (hL : a.IsTwoColorKempeComponent alpha beta L) :
    K = L ∨ Disjoint K L := by
  classical
  by_cases hcommon : ∃ edge, edge ∈ K ∧ edge ∈ L
  · rcases hcommon with ⟨edge, hedgeK, hedgeL⟩
    exact Or.inl
      (a.isTwoColorKempeComponent_eq_of_common_member
        hK hL hedgeK hedgeL)
  · right
    apply Set.disjoint_left.mpr
    intro edge hedgeK hedgeL
    exact hcommon ⟨edge, hedgeK, hedgeL⟩

end PartialEdgeAssignment

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

omit [DecidableRel H.Adj] in
/-- Three reachable `gamma`-holes, with `alpha` present throughout the old
reachable set and on a center edge, force an off-center physical
`alpha`--`gamma` component meeting one of those holes. -/
theorem exists_offCenter_component_of_three_missingSources
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    {alphaTarget : V}
    (halphaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center alphaTarget alpha)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha)
    (htriple : (state.missingSourceFinset gamma).card = 3) :
    ∃ (source : V) (K : Set H.edgeSet),
      source ∈ state.missingSourceFinset gamma ∧
        state.assignment.IsTwoColorKempeComponent alpha gamma K ∧
        EdgeSetIsEndpoint K source ∧
        EdgeSetAvoidsVertex K state.center := by
  classical
  have hcenterAlpha : ¬state.assignment.MissingAt state.center alpha := by
    intro hmissing
    rcases halphaTarget with ⟨edge, hedgeEnds, _hedgeJ, hedgeColor⟩
    apply hmissing edge
    · change state.center ∈ (edge : Sym2 V)
      rw [hedgeEnds]
      exact Sym2.mem_mk_left state.center alphaTarget
    · exact hedgeColor
  have hthree : 3 ≤
      (↑(state.missingSourceFinset gamma) : Set V).ncard := by
    simpa only [Set.ncard_coe_finset, htriple] using (Nat.le_refl 3)
  have hgamma : ∀ ⦃source : V⦄,
      source ∈ (↑(state.missingSourceFinset gamma) : Set V) →
        state.assignment.MissingAt source gamma := by
    intro source hsource
    change source ∈ state.missingSourceFinset gamma at hsource
    exact ((state.mem_missingSourceFinset_iff gamma source).1 hsource).2
  have halpha : ∀ ⦃source : V⦄,
      source ∈ (↑(state.missingSourceFinset gamma) : Set V) →
        ¬state.assignment.MissingAt source alpha := by
    intro source hsource
    change source ∈ state.missingSourceFinset gamma at hsource
    exact halphaPresent
      ((state.mem_missingSourceFinset_iff gamma source).1 hsource).1
  rcases
      PartialEdgeAssignment.exists_component_avoiding_vertex_of_three_missing
        state.valid hthree hgamma halpha hcenterAlpha with
    ⟨source, K, hsource, hK, hsourceEndpoint, hcenterAvoid⟩
  change source ∈ state.missingSourceFinset gamma at hsource
  exact ⟨source, K, hsource, hK, hsourceEndpoint, hcenterAvoid⟩

end OrientedOneHoleState

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A reachable `gamma`-hole outside the two external sources lies in every
through-center component containing a specified center `alpha`-edge.  More
precisely, it is an endpoint of that component.

The equality-or-disjointness dichotomy is load-bearing: a disjoint component
through the remaining hole must avoid the center, and crossing externality
would then incorrectly place that hole in the external-source finset. -/
theorem edgeSetIsEndpoint_throughCenterComponent_of_internalMissingSource
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {gammaTarget : V} {gammaCarrier alphaEdge : H.edgeSet}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center gammaTarget gamma)
    (halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha)
    (hGamma : state.assignment.IsUniqueColorOn
      (distinguishedEdgeSet H J) gamma gammaCarrier)
    (halphaEdgeCenter : Incident state.center alphaEdge)
    (halphaEdgeColor : state.assignment.color alphaEdge = some alpha)
    {C : Set H.edgeSet}
    (hC : state.assignment.IsTwoColorKempeComponent alpha gamma C)
    (halphaEdgeC : alphaEdge ∈ C)
    (htwoExternal :
      (state.externalMissingSourceFinset gammaTarget gamma).card = 2)
    {remaining : V}
    (hremaining : remaining ∈ state.missingSourceFinset gamma)
    (hremainingInternal :
      remaining ∉ state.externalMissingSourceFinset gammaTarget gamma) :
    EdgeSetIsEndpoint C remaining := by
  classical
  have hremainingParts :=
    (state.mem_missingSourceFinset_iff gamma remaining).1 hremaining
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      state.assignment (halphaPresent hremainingParts.1) with
    ⟨remainingEdge, hremainingEdgeIncident, hremainingEdgeColor⟩
  let L := state.assignment.TwoColorReachabilityClass
    alpha gamma remainingEdge
  have hL : state.assignment.IsTwoColorKempeComponent alpha gamma L :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      state.assignment alpha gamma remainingEdge
        (Or.inl hremainingEdgeColor)
  have hremainingEdgeL : remainingEdge ∈ L :=
    state.assignment.root_mem_twoColorReachabilityClass
      alpha gamma remainingEdge
  have hremainingMeetsL : EdgeSetMeetsVertex L remaining :=
    ⟨remainingEdge, hremainingEdgeL, hremainingEdgeIncident⟩
  have hremainingEndpointL : EdgeSetIsEndpoint L remaining :=
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
      state.valid hL hremainingParts.2 hremainingMeetsL
  have hremainingAffectedL :
      remaining ∈ state.affectedMissingSourceFinset gamma L :=
    (state.mem_affectedMissingSourceFinset_iff gamma L remaining).2
      ⟨hremaining, hremainingMeetsL⟩
  rcases state.assignment.isTwoColorKempeComponent_eq_or_disjoint hL hC with
    hLC | hLCdisjoint
  · simpa only [hLC] using hremainingEndpointL
  · have hLavoidCenter : EdgeSetAvoidsVertex L state.center := by
      apply edgeSetAvoidsVertex_iff_not_meets.mpr
      intro hLmeetsCenter
      rcases hLmeetsCenter with ⟨edge, hedgeL, hedgeCenter⟩
      have halphaEdgeL : alphaEdge ∈ L :=
        PartialEdgeAssignment.mem_component_of_mem_of_incident_supported
          state.assignment hL hedgeL hedgeCenter halphaEdgeCenter
            (Or.inl halphaEdgeColor)
      exact (Set.disjoint_left.mp hLCdisjoint halphaEdgeL) halphaEdgeC
    have hLeqExternal :=
      h.affectedMissingSourceFinset_eq_external_of_two_external_crossing
        hstructure state halphaGamma hgammaTarget halphaUnused
        halphaPresent hGamma hL hLavoidCenter htwoExternal
        ⟨remaining, hremainingAffectedL⟩
    exfalso
    apply (hremainingInternal :
      remaining ∉ state.externalMissingSourceFinset gammaTarget gamma)
    rw [← hLeqExternal]
    exact hremainingAffectedL

/-- Full physical placement certificate for the exact direct-entry `k = 2`
state after the centered label rotation.

The off-center component meets the old root and contains the literal unique
`gamma`-carrier.  The through-center component contains both literal center
edges, is disjoint from the off-center component, and has the third
`gamma`-hole as an endpoint.  The `gamma` target also still sees `alpha`,
which is the final local premise needed by root-pivot detachment. -/
theorem exists_crossing_components_of_exactTriple_twoExternal
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {alphaTarget gammaTarget : V} {gammaCarrier : H.edgeSet}
    (halphaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center alphaTarget alpha)
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center gammaTarget gamma)
    (halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha)
    (hGamma : state.assignment.IsUniqueColorOn
      (distinguishedEdgeSet H J) gamma gammaCarrier)
    (hrootGamma : state.assignment.MissingAt state.root.leaf gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3)
    (htwoExternal :
      (state.externalMissingSourceFinset gammaTarget gamma).card = 2) :
    ∃ (remaining : V) (K C : Set H.edgeSet)
        (alphaEdge gammaEdge : H.edgeSet),
      remaining ∈ state.missingSourceFinset gamma ∧
      remaining ∉ state.externalMissingSourceFinset gammaTarget gamma ∧
      state.assignment.IsTwoColorKempeComponent alpha gamma K ∧
      EdgeSetAvoidsVertex K state.center ∧
      EdgeSetMeetsVertex K state.root.leaf ∧
      state.affectedMissingSourceFinset gamma K =
        state.externalMissingSourceFinset gammaTarget gamma ∧
      gammaCarrier ∈ K ∧
      state.assignment.IsTwoColorKempeComponent alpha gamma C ∧
      alphaEdge ∈ C ∧
      (alphaEdge : Sym2 V) = s(state.center, alphaTarget) ∧
      alphaEdge ∉ distinguishedEdgeSet H J ∧
      state.assignment.color alphaEdge = some alpha ∧
      gammaEdge ∈ C ∧
      (gammaEdge : Sym2 V) = s(state.center, gammaTarget) ∧
      gammaEdge ∉ distinguishedEdgeSet H J ∧
      state.assignment.color gammaEdge = some gamma ∧
      Disjoint K C ∧
      EdgeSetIsEndpoint C remaining ∧
      ¬state.assignment.MissingAt gammaTarget alpha := by
  classical
  rcases state.exists_offCenter_component_of_three_missingSources
      halphaTarget halphaPresent htriple with
    ⟨source, K, hsource, hK, hsourceEndpoint, hKavoidCenter⟩
  have hsourceParts :=
    (state.mem_missingSourceFinset_iff gamma source).1 hsource
  have hsourceMeetsK : EdgeSetMeetsVertex K source :=
    edgeSetMeetsVertex_of_edgeSetIsEndpoint hsourceEndpoint
  have hsourceAffectedK :
      source ∈ state.affectedMissingSourceFinset gamma K :=
    (state.mem_affectedMissingSourceFinset_iff gamma K source).2
      ⟨hsource, hsourceMeetsK⟩
  have hKaffectedEq :
      state.affectedMissingSourceFinset gamma K =
        state.externalMissingSourceFinset gammaTarget gamma :=
    h.affectedMissingSourceFinset_eq_external_of_two_external_crossing
      hstructure state halphaGamma hgammaTarget halphaUnused
      halphaPresent hGamma hK hKavoidCenter htwoExternal
      ⟨source, hsourceAffectedK⟩
  have hcarrierK : gammaCarrier ∈ K :=
    h.uniqueGammaCarrier_mem_offCenterComponent_of_reachable_gammaEndpoint
      hstructure state halphaGamma hgammaTarget halphaUnused halphaPresent
      hGamma hK hKavoidCenter hsourceParts.1 hsourceParts.2
      hsourceMeetsK
  have hrootSource :
      state.root.leaf ∈ state.missingSourceFinset gamma :=
    (state.mem_missingSourceFinset_iff gamma state.root.leaf).2
      ⟨PartialEdgeAssignment.centerReachable_refl state.assignment
        (distinguishedEdgeSet H J) state.center state.root.leaf,
        hrootGamma⟩
  have hrootExternal : state.root.leaf ∈
      state.externalMissingSourceFinset gammaTarget gamma :=
    (state.mem_externalMissingSourceFinset_iff
      gammaTarget gamma state.root.leaf).2
      ⟨hrootSource,
        DirectedDominator.root_not_mem_dominatorRegion
          (state.assignment.CenterDependency
            (distinguishedEdgeSet H J) state.center)
          state.root.leaf gammaTarget⟩
  have hrootAffected : state.root.leaf ∈
      state.affectedMissingSourceFinset gamma K := by
    rw [hKaffectedEq]
    exact hrootExternal
  have hrootMeetsK : EdgeSetMeetsVertex K state.root.leaf :=
    ((state.mem_affectedMissingSourceFinset_iff gamma K
      state.root.leaf).1 hrootAffected).2

  rcases halphaTarget with
    ⟨alphaEdge, halphaEdgeEnds, halphaEdgeOutside, halphaEdgeColor⟩
  have halphaEdgeCenter : Incident state.center alphaEdge := by
    change state.center ∈ (alphaEdge : Sym2 V)
    rw [halphaEdgeEnds]
    exact Sym2.mem_mk_left state.center alphaTarget
  let C := state.assignment.TwoColorReachabilityClass
    alpha gamma alphaEdge
  have hC : state.assignment.IsTwoColorKempeComponent alpha gamma C :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      state.assignment alpha gamma alphaEdge (Or.inl halphaEdgeColor)
  have halphaEdgeC : alphaEdge ∈ C :=
    state.assignment.root_mem_twoColorReachabilityClass
      alpha gamma alphaEdge
  have hCmeetsCenter : EdgeSetMeetsVertex C state.center :=
    ⟨alphaEdge, halphaEdgeC, halphaEdgeCenter⟩
  rcases hgammaTarget with
    ⟨gammaEdge, hgammaEdgeEnds, hgammaEdgeOutside, hgammaEdgeColor⟩
  have hgammaEdgeCenter : Incident state.center gammaEdge := by
    change state.center ∈ (gammaEdge : Sym2 V)
    rw [hgammaEdgeEnds]
    exact Sym2.mem_mk_left state.center gammaTarget
  have hgammaEdgeC : gammaEdge ∈ C :=
    PartialEdgeAssignment.mem_component_of_mem_of_incident_supported
      state.assignment hC halphaEdgeC halphaEdgeCenter hgammaEdgeCenter
        (Or.inr hgammaEdgeColor)
  have hKCne : K ≠ C := by
    intro hKC
    have hKmeetsCenter : EdgeSetMeetsVertex K state.center := by
      rw [hKC]
      exact hCmeetsCenter
    exact (edgeSetAvoidsVertex_iff_not_meets.mp hKavoidCenter)
      hKmeetsCenter
  have hKCdisjoint : Disjoint K C :=
    (state.assignment.isTwoColorKempeComponent_eq_or_disjoint hK hC).resolve_left
      hKCne

  have hsourcesNotSubsetExternal :
      ¬state.missingSourceFinset gamma ⊆
        state.externalMissingSourceFinset gammaTarget gamma := by
    intro hsubset
    have hcard := Finset.card_le_card hsubset
    rw [htriple, htwoExternal] at hcard
    omega
  rcases Finset.not_subset.mp hsourcesNotSubsetExternal with
    ⟨remaining, hremaining, hremainingInternal⟩
  have hremainingEndpointC : EdgeSetIsEndpoint C remaining :=
    h.edgeSetIsEndpoint_throughCenterComponent_of_internalMissingSource
      hstructure state halphaGamma
      ⟨gammaEdge, hgammaEdgeEnds, hgammaEdgeOutside, hgammaEdgeColor⟩
      halphaUnused halphaPresent hGamma halphaEdgeCenter halphaEdgeColor
      hC halphaEdgeC htwoExternal hremaining hremainingInternal
  have hgammaTarget' : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center gammaTarget gamma :=
    ⟨gammaEdge, hgammaEdgeEnds, hgammaEdgeOutside, hgammaEdgeColor⟩
  have hrootToGammaTarget : state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center state.root.leaf
        gammaTarget :=
    (hgammaTarget'.centerDependency_iff_missingAt state.root.leaf).2
      hrootGamma
  have hgammaTargetReach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf
        gammaTarget :=
    PartialEdgeAssignment.centerReachable_tail
      (PartialEdgeAssignment.centerReachable_refl state.assignment
        (distinguishedEdgeSet H J) state.center state.root.leaf)
      hrootToGammaTarget
  have hgammaTargetAlpha :
      ¬state.assignment.MissingAt gammaTarget alpha :=
    halphaPresent hgammaTargetReach
  exact ⟨remaining, K, C, alphaEdge, gammaEdge,
    hremaining, hremainingInternal, hK, hKavoidCenter, hrootMeetsK,
    hKaffectedEq, hcarrierK, hC, halphaEdgeC, halphaEdgeEnds,
    halphaEdgeOutside, halphaEdgeColor, hgammaEdgeC, hgammaEdgeEnds,
    hgammaEdgeOutside, hgammaEdgeColor, hKCdisjoint,
    hremainingEndpointC, hgammaTargetAlpha⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
