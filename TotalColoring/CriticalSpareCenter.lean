import TotalColoring.CriticalThroughCenter
import TotalColoring.FanCount
import TotalColoring.FanLeaves
import TotalColoring.TwoColorEndpointCapacity

/-!
# Spare colors at the center of a critical fan

Suppose a color `delta` unused on the distinguished edge set is missing at
the fan center.  For every color `gamma`, exact through-center closure puts
every dependency-reachable `gamma`-hole into the same physical two-color
component through the center.  Since the center is already an endpoint,
global two-endpoint capacity permits at most one such leaf.  The coincident-
color case is even stronger and follows immediately from center--reachable
elementarity.

Consequently, if any color is missing at two reachable leaves, no color
unused on the distinguished set can be missing at the center.  In particular
this proves the spare-center exclusion in the triply missing residual used by
the proof program.  It does not assert that such a repeated or triply missing
color always exists; that later bridge requires the maximal-fan counting
layer.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- If a color unused on the distinguished set is missing at the center,
then every palette color is missing at at most one dependency-reachable leaf.
This structural bound assumes neither fan maximality nor the existence of a
triply missing color. -/
theorem ncard_missingAt_centerReachable_le_one_of_unused_missingAt_center
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {delta : ExtensionPalette D}
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    (hcenter : a.MissingAt center delta)
    (gamma : ExtensionPalette D) :
    ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard ≤ 1 := by
  classical
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf ∧
      a.MissingAt leaf gamma}
  change S.ncard ≤ 1
  apply Set.ncard_le_one_iff_subsingleton.mpr
  by_cases hdeltagamma : delta = gamma
  · intro v hv w hw
    subst gamma
    exact (h.center_reachable_elementary root hrootJ hvalid hhole
      hrainbow hv.1 delta ⟨hcenter, hv.2⟩).elim
  · intro v hv w hw
    have hnotGammaCenter : ¬a.MissingAt center gamma := by
      intro hgamma
      exact h.center_reachable_elementary root hrootJ hvalid hhole
        hrainbow hv.1 gamma ⟨hgamma, hv.2⟩
    rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
        a hnotGammaCenter with ⟨centerEdge, hcenterIncident, hcenterColor⟩
    let K := a.TwoColorReachabilityClass delta gamma centerEdge
    have hcenterSupported : a.TwoColorSupported delta gamma centerEdge :=
      Or.inr hcenterColor
    have hK : a.IsTwoColorKempeComponent delta gamma K :=
      PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
        a delta gamma centerEdge hcenterSupported
    have hcenterEdgeK : centerEdge ∈ K :=
      a.root_mem_twoColorReachabilityClass delta gamma centerEdge
    have hKcenter : EdgeSetMeetsVertex K center :=
      ⟨centerEdge, hcenterEdgeK, hcenterIncident⟩
    have hcompatible :
        a.SwapCompatibleOn (distinguishedEdgeSet H J) delta gamma K :=
      PartialEdgeAssignment.swapCompatibleOn_of_unused_left
        a (distinguishedEdgeSet H J) K hunused
    have hcenterEnd :=
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_left_of_component_meets
        hvalid hK hcenter hKcenter
    have hKv :=
      h.component_meets_centerReachable_missing_right_of_swapCompatible
        root hrootJ hvalid hhole hrainbow hK hdeltagamma hcenter
        hKcenter hcompatible hv.1 hv.2
    have hKw :=
      h.component_meets_centerReachable_missing_right_of_swapCompatible
        root hrootJ hvalid hhole hrainbow hK hdeltagamma hcenter
        hKcenter hcompatible hw.1 hw.2
    have hvEnd :=
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK hv.2 hKv
    have hwEnd :=
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK hw.2 hKw
    rcases PartialEdgeAssignment.endpoint_triple_has_repetition_of_component
        hvalid hK hcenterEnd hvEnd hwEnd with hcv | hcw | hvw
    · exact (PartialEdgeAssignment.centerReachable_ne_center a
        (distinguishedEdgeSet H J) root.leaf_ne_center hv.1) hcv.symm |>.elim
    · exact (PartialEdgeAssignment.centerReachable_ne_center a
        (distinguishedEdgeSet H J) root.leaf_ne_center hw.1) hcw.symm |>.elim
    · exact hvw

/-- If some color is missing at two dependency-reachable leaves, a color
unused on the distinguished set cannot be missing at the fan center. -/
theorem not_missingAt_center_of_unused_of_two_missing_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {delta gamma : ExtensionPalette D}
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    (htwo : 2 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard) :
    ¬a.MissingAt center delta := by
  intro hcenter
  have hone :=
    h.ncard_missingAt_centerReachable_le_one_of_unused_missingAt_center
      root hrootJ hvalid hhole hrainbow hunused hcenter gamma
  omega

/-- Triply missing residual form of spare-center exclusion.  This is an
immediate corollary of the stronger two-leaf threshold above. -/
theorem not_missingAt_center_of_unused_of_three_missing_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {delta gamma : ExtensionPalette D}
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    (hthree : 3 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard) :
    ¬a.MissingAt center delta := by
  apply h.not_missingAt_center_of_unused_of_two_missing_centerReachable
    (delta := delta) (gamma := gamma)
    root hrootJ hvalid hhole hrainbow hunused
  omega

/-- Finite selected-fan form of the same multiplicity-one bound. -/
theorem colorMultiplicity_leafFinset_le_one_of_unused_missingAt_center
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {delta : ExtensionPalette D}
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    (hcenter : a.MissingAt center delta)
    (gamma : ExtensionPalette D) :
    FanCount.colorMultiplicity F.leafFinset a.MissingAt gamma ≤ 1 := by
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center F.root.leaf leaf ∧
      a.MissingAt leaf gamma}
  have hsubset :
      (↑(F.leafFinset.filter fun leaf ↦ a.MissingAt leaf gamma) : Set V) ⊆
        S := by
    intro leaf hleaf
    have hparts := Finset.mem_filter.mp hleaf
    exact ⟨F.centerReachable_of_mem_leafFinset hparts.1, hparts.2⟩
  have hmono := Set.ncard_le_ncard hsubset
  have hbound : S.ncard ≤ 1 :=
    h.ncard_missingAt_centerReachable_le_one_of_unused_missingAt_center
      F.root F.root_not_mem hvalid hhole hrainbow hunused hcenter gamma
  change (F.leafFinset.filter fun leaf ↦ a.MissingAt leaf gamma).card ≤ 1
  rw [← Set.ncard_coe_finset]
  exact hmono.trans hbound

/-- Selected-fan form of spare-center exclusion at the sharp two-leaf
threshold. -/
theorem not_missingAt_center_of_unused_of_two_missing_leafFinset
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {delta gamma : ExtensionPalette D}
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    (htwo : 2 ≤ FanCount.colorMultiplicity
      F.leafFinset a.MissingAt gamma) :
    ¬a.MissingAt center delta := by
  intro hcenter
  have hone :=
    h.colorMultiplicity_leafFinset_le_one_of_unused_missingAt_center
      F hvalid hhole hrainbow hunused hcenter gamma
  omega

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
