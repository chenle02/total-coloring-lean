import TotalColoring.CriticalAllLeaf
import TotalColoring.CriticalThroughCenter
import TotalColoring.TwoColorEndpointCapacity

/-!
# Critical component closure at reachable fan leaves

This module packages the two complementary closure directions used by the
critical fan argument.  A component rooted at a reachable leaf either meets
the fan center or is unsafe to swap.  Conversely, an exactly swap-compatible
component through the center meets every reachable leaf missing its
right-hand color; that companion theorem is supplied by
`CriticalThroughCenter`.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A terminal missing the right-hand color has a genuine component which
meets it and which either reaches the center or fails exact swap
compatibility. -/
theorem exists_terminal_component_dichotomy
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha gamma : ExtensionPalette D} (halphagamma : alpha ≠ gamma)
    (hcenter : a.MissingAt center alpha)
    (hterminal : a.MissingAt F.terminal.leaf gamma) :
    ∃ K : Set H.edgeSet,
      a.IsTwoColorKempeComponent alpha gamma K ∧
      EdgeSetMeetsVertex K F.terminal.leaf ∧
      (EdgeSetMeetsVertex K center ∨
        ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha gamma K) := by
  classical
  have hnotAlpha : ¬a.MissingAt F.terminal.leaf alpha := by
    intro hterminalAlpha
    exact h.center_terminal_elementary F hvalid hhole hrainbow alpha
      ⟨hcenter, hterminalAlpha⟩
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      a hnotAlpha with ⟨root, hrootTerminal, hrootColor⟩
  let K := a.TwoColorReachabilityClass alpha gamma root
  have hrootSupported : a.TwoColorSupported alpha gamma root :=
    Or.inl hrootColor
  have hK : a.IsTwoColorKempeComponent alpha gamma K :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      a alpha gamma root hrootSupported
  have hrootK : root ∈ K :=
    a.root_mem_twoColorReachabilityClass alpha gamma root
  have hmeetsTerminal : EdgeSetMeetsVertex K F.terminal.leaf :=
    ⟨root, hrootK, hrootTerminal⟩
  exact ⟨K, hK, hmeetsTerminal,
    h.component_meets_center_or_not_swapCompatible F hvalid hhole
      hrainbow hK halphagamma hcenter hterminal hmeetsTerminal⟩

/-- Reachability form of the leaf-component dichotomy.  The chosen leaf is
recorded as an actual endpoint of the returned component. -/
theorem exists_centerReachable_component_dichotomy
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha gamma : ExtensionPalette D} (halphagamma : alpha ≠ gamma)
    (hcenter : a.MissingAt center alpha)
    {leaf : V}
    (hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf leaf)
    (hleaf : a.MissingAt leaf gamma) :
    ∃ K : Set H.edgeSet,
      a.IsTwoColorKempeComponent alpha gamma K ∧
      EdgeSetIsEndpoint K leaf ∧
      (EdgeSetMeetsVertex K center ∨
        ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha gamma K) := by
  classical
  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      root hrootJ hreach with ⟨F, hFroot, hFterminal⟩
  have hFhole : a.OneHoleAt F.root.edge := by
    simpa [hFroot] using hhole
  have hFmissing : a.MissingAt F.terminal.leaf gamma := by
    simpa [hFterminal] using hleaf
  rcases h.exists_terminal_component_dichotomy F hvalid hFhole
      hrainbow halphagamma hcenter hFmissing with
    ⟨K, hK, hmeets, hdichotomy⟩
  refine ⟨K, hK, ?_, hdichotomy⟩
  simpa [hFterminal] using
    (PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
      hvalid hK hFmissing hmeets)

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
