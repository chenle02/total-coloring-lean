import TotalColoring.CriticalCrossingComponents
import TotalColoring.CriticalDetachedPivot
import TotalColoring.CriticalRobustColumn

/-!
# Elimination of the two-external-source case

This module assembles the `k = 2` branch of the direct-entry argument.  First,
an off-center component meeting a reachable `gamma`-hole is forced by fresh
location to cross the unique distinguished `gamma` carrier.  Exact crossing
externality then says that this component meets both external sources.

There is a third reachable `gamma`-hole outside the two-source external
finset.  Its `alpha`--`gamma` component must meet the center: if it avoided the
center, the same crossing-externality theorem would make the third hole
external.  Hence that component contains the direct `gamma` spoke and is
disjoint from the first component.

The literal `gamma` root pivot now detaches the far side of this through-center
path.  The detached component omits the distinguished `gamma` carrier, while
fresh carrier placement in the pivoted state says that every such off-center
component through the new root must contain it.  This contradiction eliminates
cardinality two.

No centered rotation is needed for this shorter assembly: one of the two
colors unused on the distinguished set can be chosen distinct from `gamma`.
Fresh reachable-hole location makes it present both at the center and on the
whole canonical reachable set.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V}
variable {J M : Finset (Sym2 V)} [DecidableRel H.Adj]

/-- Final physical contradiction for the crossing/detachment configuration.
`K` is the off-center component through the old root and the unique
distinguished `gamma` carrier.  `C` is a disjoint component through the pivot
donor and has a physical endpoint. -/
theorem false_of_detached_crossing_configuration
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    (next : CenterSpoke H state.center)
    (hnextOutside : next.edge ∉ distinguishedEdgeSet H J)
    (hnextColor : state.assignment.color next.edge = some gamma)
    (hrootMissing : state.assignment.MissingAt state.root.leaf gamma)
    {gammaCarrier : H.edgeSet}
    (hGamma : state.assignment.IsUniqueColorOn
      (distinguishedEdgeSet H J) gamma gammaCarrier)
    {K C : Set H.edgeSet}
    (hK : state.assignment.IsTwoColorKempeComponent alpha gamma K)
    (hC : state.assignment.IsTwoColorKempeComponent alpha gamma C)
    (hdisjoint : Disjoint K C)
    (hrootK : EdgeSetMeetsVertex K state.root.leaf)
    (hnextC : next.edge ∈ C)
    {componentEndpoint : V}
    (hcomponentEndpoint : EdgeSetIsEndpoint C componentEndpoint)
    (hnextAlpha : ¬state.assignment.MissingAt next.leaf alpha)
    (hcarrierK : gammaCarrier ∈ K)
    (halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha) : False := by
  classical
  let hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next :=
    ⟨gamma, hnextOutside, hnextColor, hrootMissing⟩
  let pivot := state.rootPivot next hstep
  rcases state.exists_detached_component_rootPivot_omits_marked
      next hstep halphaGamma hnextColor hK hC hdisjoint hrootK hnextC
      hcomponentEndpoint hnextAlpha hcarrierK halphaUnused with
    ⟨Kq, hKq, hqEndpoint, hqAvoid, hcarrierNotKq,
      hqGamma, _hqAlpha, halphaUnusedPivot⟩

  have hqMeets : EdgeSetMeetsVertex Kq next.leaf :=
    ⟨hqEndpoint.choose, hqEndpoint.choose_spec.1,
      hqEndpoint.choose_spec.2.1⟩
  have hGammaPivot : pivot.assignment.IsUniqueColorOn
      (distinguishedEdgeSet H J) gamma gammaCarrier := by
    simpa [pivot] using
      (state.isUniqueColorOn_rootPivot_iff
        next hstep gamma gammaCarrier).2 hGamma
  have hpivotRootColor :
      pivot.assignment.color state.root.edge = some gamma := by
    change (state.assignment.moveHole state.root.edge next.edge).color
      state.root.edge = some gamma
    exact (PartialEdgeAssignment.moveHole_color_hole
      state.assignment state.root.edge next.edge).trans hnextColor
  have hpivotTarget : pivot.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) pivot.center state.root.leaf gamma :=
    ⟨state.root.edge, by simpa [pivot] using state.root.endpoints,
      state.rootOutside, hpivotRootColor⟩
  have halphaPresentPivot : ∀ ⦃vertex : V⦄,
      pivot.assignment.CenterReachable (distinguishedEdgeSet H J)
          pivot.center pivot.root.leaf vertex →
        ¬pivot.assignment.MissingAt vertex alpha := by
    intro vertex hreach
    exact h.not_missingAt_centerReachable_of_unused hstructure
      pivot.root pivot.rootOutside pivot.valid pivot.oneHole pivot.rainbow
      halphaUnusedPivot hreach
  have hpivotRootReach : pivot.assignment.CenterReachable
      (distinguishedEdgeSet H J) pivot.center pivot.root.leaf
        pivot.root.leaf :=
    PartialEdgeAssignment.centerReachable_refl pivot.assignment
      (distinguishedEdgeSet H J) pivot.center pivot.root.leaf
  have hpivotRootGamma :
      pivot.assignment.MissingAt pivot.root.leaf gamma := by
    simpa [pivot] using hqGamma
  have hpivotRootMeets : EdgeSetMeetsVertex Kq pivot.root.leaf := by
    simpa [pivot] using hqMeets
  have hqAvoidPivot : EdgeSetAvoidsVertex Kq pivot.center := by
    intro edge hedgeKq hedgeCenter
    apply hqAvoid hedgeKq
    simpa [pivot] using hedgeCenter
  have hcarrierKq : gammaCarrier ∈ Kq :=
    h.uniqueGammaCarrier_mem_offCenterComponent_of_reachable_gammaEndpoint
      hstructure pivot halphaGamma hpivotTarget halphaUnusedPivot
      halphaPresentPivot hGammaPivot hKq hqAvoidPivot
      hpivotRootReach hpivotRootGamma hpivotRootMeets
  exact hcarrierNotKq hcarrierKq

/-- Eliminate `k = 2` once an unused color distinct from `gamma` has been
selected.  This theorem derives both physical components needed by the final
detachment lemma. -/
theorem externalMissingSourceFinset_card_ne_two_of_unusedColor_exactTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {q : V} {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma)
    (hrootMissing : state.assignment.MissingAt state.root.leaf gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3)
    (halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha)
    {gammaCarrier : H.edgeSet}
    (hGamma : state.assignment.IsUniqueColorOn
      (distinguishedEdgeSet H J) gamma gammaCarrier) :
    (state.externalMissingSourceFinset q gamma).card ≠ 2 := by
  classical
  intro htwoExternal
  have halphaCenter : ¬state.assignment.MissingAt state.center alpha :=
    h.not_missingAt_center_of_unused state.root state.rootOutside
      state.valid state.oneHole state.rainbow halphaUnused
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      state.assignment halphaCenter with
    ⟨alphaEdge, halphaEdgeCenter, halphaEdgeColor⟩
  have halphaEdgeOutside :
      alphaEdge ∉ distinguishedEdgeSet H J := by
    intro halphaEdgeJ
    exact halphaUnused halphaEdgeJ halphaEdgeColor
  rcases Sym2.mem_iff_exists.mp halphaEdgeCenter with
    ⟨alphaTarget, halphaEdgeEnds⟩
  have halphaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center alphaTarget alpha :=
    ⟨alphaEdge, halphaEdgeEnds, halphaEdgeOutside, halphaEdgeColor⟩
  rcases h.exists_crossing_components_of_exactTriple_twoExternal
      hstructure state halphaGamma halphaTarget hgammaTarget
      halphaUnused halphaPresent hGamma hrootMissing htriple
      htwoExternal with
    ⟨remaining, K, C, _alphaEdge, gammaEdge,
      _hremaining, _hremainingInternal, hK, _hKavoid, hrootK,
      _haffectedEq, hcarrierK, hC, _halphaEdgeC, _halphaEnds,
      _halphaOutside, _halphaColor, hgammaEdgeC, hgammaEnds,
      hgammaOutside, hgammaColor, hKCdisjoint, hremainingEndpoint,
      hqAlpha⟩
  let next : CenterSpoke H state.center :=
    {
      leaf := q
      edge := gammaEdge
      endpoints := hgammaEnds
    }
  exact h.false_of_detached_crossing_configuration hstructure state
    halphaGamma next (by simpa [next] using hgammaOutside)
      (by simpa [next] using hgammaColor) hrootMissing hGamma
      hK hC hKCdisjoint hrootK (by simpa [next] using hgammaEdgeC)
      hremainingEndpoint (by simpa [next] using hqAlpha) hcarrierK
      halphaUnused

/-- Complete elimination of the two-external-source branch for a globally
reach-card-maximal direct exact-triple state.  The maximality hypothesis is
kept in the common branch interface, although this final `k = 2` assembly
uses only criticality, the direct exact triple, and fresh location. -/
theorem externalMissingSourceFinset_card_ne_two_of_exactTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (_hmaximal : state.IsGloballyReachCardMaximal)
    {q : V} {gamma : ExtensionPalette D}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma)
    (hrootMissing : state.assignment.MissingAt state.root.leaf gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3) :
    (state.externalMissingSourceFinset q gamma).card ≠ 2 := by
  classical
  have hrootReach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf
        state.root.leaf :=
    PartialEdgeAssignment.centerReachable_refl state.assignment
      (distinguishedEdgeSet H J) state.center state.root.leaf
  rcases h.exists_matching_carrier_of_missingAt_centerReachable
      hstructure state.root state.rootOutside state.valid state.oneHole
      state.rainbow hrootReach hrootMissing with
    ⟨gammaCarrier, hGamma, _hgammaCarrierM⟩

  let U := state.assignment.colorUnusedOnFinset
    (distinguishedEdgeSet H J)
  have hUcard : U.card = 2 := by
    simpa [U] using h.card_colorUnusedOnFinset_eq_two state.rainbow
  have hUlarge : 1 < U.card := by omega
  rcases Finset.one_lt_card.mp hUlarge with
    ⟨alpha₀, halpha₀U, alpha₁, halpha₁U, halpha₀alpha₁⟩
  obtain ⟨alpha, halphaU, halphaGamma⟩ :
      ∃ alpha : ExtensionPalette D, alpha ∈ U ∧ alpha ≠ gamma := by
    by_cases halpha₀Gamma : alpha₀ ≠ gamma
    · exact ⟨alpha₀, halpha₀U, halpha₀Gamma⟩
    · refine ⟨alpha₁, halpha₁U, ?_⟩
      intro halpha₁Gamma
      apply halpha₀alpha₁
      exact (of_not_not halpha₀Gamma).trans halpha₁Gamma.symm
  have halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha := by
    change alpha ∈ state.assignment.colorUnusedOnFinset
      (distinguishedEdgeSet H J) at halphaU
    exact (PartialEdgeAssignment.mem_colorUnusedOnFinset_iff
      state.assignment (distinguishedEdgeSet H J) alpha).mp halphaU
  have halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha := by
    intro vertex hreach
    exact h.not_missingAt_centerReachable_of_unused hstructure
      state.root state.rootOutside state.valid state.oneHole state.rainbow
      halphaUnused hreach
  exact h.externalMissingSourceFinset_card_ne_two_of_unusedColor_exactTriple
    hstructure state halphaGamma hgammaTarget hrootMissing htriple
      halphaUnused halphaPresent hGamma

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
