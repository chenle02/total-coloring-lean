import TotalColoring.CriticalFan
import TotalColoring.FanPrefixRepair

/-!
# Critical all-leaf Kempe closure

This module combines the structural prefix-repair lemma with ambient
noncolorability.  In a supplied outside-edge-minimal noncolorable state, fix a
linear fan path, a color `alpha` missing at its center, and a distinct color
`beta` missing at its terminal leaf.  Any genuine physical
`alpha`-`beta` component meeting that terminal leaf must either meet the fan
center or fail the exact `SwapCompatibleOn` condition.

The proof does not assume fan maximality.  It also does not replace exact
distinguished-edge compatibility by the stronger and generally false slogan
that a safe component avoids `J`.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Exact all-leaf closure for an arbitrary genuine physical component.
Safety is the carrier-free `SwapCompatibleOn` predicate already proved
equivalent to preservation of the partial `J`-rainbow invariant. -/
theorem component_meets_center_or_not_swapCompatible
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    {alpha beta : ExtensionPalette D} {K : Set H.edgeSet}
    [DecidablePred (· ∈ K)]
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hcenter : a.MissingAt center alpha)
    (hterminal : a.MissingAt F.terminal.leaf beta)
    (hmeetsTerminal : EdgeSetMeetsVertex K F.terminal.leaf) :
    EdgeSetMeetsVertex K center ∨
      ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha beta K := by
  by_cases hmeetsCenter : EdgeSetMeetsVertex K center
  · exact Or.inl hmeetsCenter
  · right
    intro hcompatible
    have havoid : EdgeSetAvoidsVertex K center :=
      edgeSetAvoidsVertex_iff_not_meets.mpr hmeetsCenter
    have hswap :=
      (PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_iff
        a (distinguishedEdgeSet H J) K hvalid hrainbow halphabeta hK).2
        hcompatible
    have hholeSwap :
        (a.swapOn alpha beta K).OneHoleAt F.root.edge :=
      (PartialEdgeAssignment.swapOn_oneHoleAt_iff
        a alpha beta K F.root.edge).2 hhole
    have hcenterSwap :
        (a.swapOn alpha beta K).MissingAt center alpha :=
      (PartialEdgeAssignment.missingAt_swapOn_iff_of_avoidsVertex
        a alpha beta K havoid alpha).2 hcenter
    rcases PartialEdgeAssignment.exists_prefix_after_component_swap
        a (distinguishedEdgeSet H J) F hK halphabeta havoid hcenter
        hterminal hmeetsTerminal with
      ⟨Q, hQroot, hQprefix, hQterminal⟩
    have hQhole : (a.swapOn alpha beta K).OneHoleAt Q.root.edge := by
      simpa [hQroot] using hholeSwap
    exact h.center_terminal_elementary Q hswap.1 hQhole hswap.2 alpha
      ⟨hcenterSwap, hQterminal⟩

/-- When one of the two colors is unused on `J`, exact compatibility is
automatic, so every such terminal component must meet the center. -/
theorem component_meets_center_of_one_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    {alpha beta : ExtensionPalette D} {K : Set H.edgeSet}
    [DecidablePred (· ∈ K)]
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hcenter : a.MissingAt center alpha)
    (hterminal : a.MissingAt F.terminal.leaf beta)
    (hmeetsTerminal : EdgeSetMeetsVertex K F.terminal.leaf)
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) alpha ∨
      a.ColorUnusedOn (distinguishedEdgeSet H J) beta) :
    EdgeSetMeetsVertex K center := by
  rcases h.component_meets_center_or_not_swapCompatible F hvalid hhole
      hrainbow hK halphabeta hcenter hterminal hmeetsTerminal with
    hmeets | hunsafe
  · exact hmeets
  · exfalso
    apply hunsafe
    rcases hunused with hunused | hunused
    · exact PartialEdgeAssignment.swapCompatibleOn_of_unused_left
        a (distinguishedEdgeSet H J) K hunused
    · exact PartialEdgeAssignment.swapCompatibleOn_of_unused_right
        a (distinguishedEdgeSet H J) K hunused

/-- Canonical rooted form: a supported edge incident with the terminal leaf
defines the physical component to which the all-leaf dichotomy applies.  The
explicit support hypothesis prevents an uncolored or third-colored root from
being treated as a fake singleton component. -/
theorem terminal_reachabilityClass_meets_center_or_not_swapCompatible
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    {alpha beta : ExtensionPalette D} (componentRoot : H.edgeSet)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (halphabeta : alpha ≠ beta)
    (hcenter : a.MissingAt center alpha)
    (hterminal : a.MissingAt F.terminal.leaf beta)
    (hrootSupported : a.TwoColorSupported alpha beta componentRoot)
    (hrootTerminal : Incident F.terminal.leaf componentRoot) :
    EdgeSetMeetsVertex
        (a.TwoColorReachabilityClass alpha beta componentRoot) center ∨
      ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha beta
        (a.TwoColorReachabilityClass alpha beta componentRoot) := by
  classical
  let K := a.TwoColorReachabilityClass alpha beta componentRoot
  have hK : a.IsTwoColorKempeComponent alpha beta K :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      a alpha beta componentRoot hrootSupported
  have hrootK : componentRoot ∈ K :=
    PartialEdgeAssignment.root_mem_twoColorReachabilityClass
      a alpha beta componentRoot
  exact h.component_meets_center_or_not_swapCompatible F hvalid hhole
    hrainbow hK halphabeta hcenter hterminal
      ⟨componentRoot, hrootK, hrootTerminal⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
