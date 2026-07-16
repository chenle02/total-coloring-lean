import TotalColoring.CriticalFan
import TotalColoring.FanPrefixRepairThroughCenter

/-!
# Critical through-center Kempe closure

Fix a linear fan path, a color `alpha` missing at its center, and a distinct
color `beta` missing at its terminal leaf.  If a genuine physical
`alpha`-`beta` component meets the center, then it must either meet the
terminal leaf or fail the exact `SwapCompatibleOn` condition.

This is the through-center companion to `CriticalAllLeaf`.  Its proof swaps a
safe component assumed to avoid the terminal, repairs a literal fan prefix,
and contradicts center--terminal elementarity for `beta`.  It assumes neither
fan maximality nor any carrier-location result.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A genuine component which meets the fan center must meet the chosen
terminal unless swapping it would violate the exact distinguished-rainbow
compatibility condition. -/
theorem component_meets_terminal_or_not_swapCompatible_of_meets_center
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
    (hmeetsCenter : EdgeSetMeetsVertex K center) :
    EdgeSetMeetsVertex K F.terminal.leaf ∨
      ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha beta K := by
  by_cases hmeetsTerminal : EdgeSetMeetsVertex K F.terminal.leaf
  · exact Or.inl hmeetsTerminal
  · right
    intro hcompatible
    have havoidTerminal : EdgeSetAvoidsVertex K F.terminal.leaf :=
      edgeSetAvoidsVertex_iff_not_meets.mpr hmeetsTerminal
    have hswap :=
      (PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_iff
        a (distinguishedEdgeSet H J) K hvalid hrainbow halphabeta hK).2
        hcompatible
    have hholeSwap :
        (a.swapOn alpha beta K).OneHoleAt F.root.edge :=
      (PartialEdgeAssignment.swapOn_oneHoleAt_iff
        a alpha beta K F.root.edge).2 hhole
    have hcenterSwap :
        (a.swapOn alpha beta K).MissingAt center beta :=
      PartialEdgeAssignment.missingAt_right_swapOn_of_missing_left_of_component_meets
        a hK halphabeta hcenter hmeetsCenter
    rcases PartialEdgeAssignment.exists_prefix_after_component_swap_of_meets_center
        a (distinguishedEdgeSet H J) F hK halphabeta hmeetsCenter
        havoidTerminal hcenter hterminal with
      ⟨Q, hQroot, hQprefix, hQterminal⟩
    have hQhole : (a.swapOn alpha beta K).OneHoleAt Q.root.edge := by
      simpa [hQroot] using hholeSwap
    exact h.center_terminal_elementary Q hswap.1 hQhole hswap.2 beta
      ⟨hcenterSwap, hQterminal⟩

/-- Reachability wrapper for the through-center closure theorem.  A safe
component through the center contains every dependency-reachable leaf which
misses its right-hand color. -/
theorem component_meets_centerReachable_missing_right_of_swapCompatible
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha beta : ExtensionPalette D} {K : Set H.edgeSet}
    [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hcenter : a.MissingAt center alpha)
    (hmeetsCenter : EdgeSetMeetsVertex K center)
    (hcompatible :
      a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha beta K)
    {target : V}
    (hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf target)
    (hmissing : a.MissingAt target beta) :
    EdgeSetMeetsVertex K target := by
  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      root hrootJ hreach with ⟨F, hFroot, hFterminal⟩
  have hFhole : a.OneHoleAt F.root.edge := by
    simpa [hFroot] using hhole
  have hFmissing : a.MissingAt F.terminal.leaf beta := by
    simpa [hFterminal] using hmissing
  rcases h.component_meets_terminal_or_not_swapCompatible_of_meets_center
      F hvalid hFhole hrainbow hK halphabeta hcenter hFmissing
      hmeetsCenter with hmeets | hunsafe
  · simpa [hFterminal] using hmeets
  · exact (hunsafe hcompatible).elim

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
