import TotalColoring.CriticalState
import TotalColoring.FanReachability
import TotalColoring.FanShift

/-!
# Critical-state bridges for fan moves

The deletion construction in `CriticalState` produces one particular blocked
one-hole coloring.  Fan shifts and root pivots produce new partial colorings
with a hole elsewhere.  This module first records the general bridge needed
after any such move: noncolorability of the ambient graph rules out a valid,
complete, distinguished-rainbow fill of *every* partial assignment.

The fan-shift consequences are added only after their preservation hypotheses
have been formalized explicitly.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Ambient noncolorability blocks a direct valid, complete, rainbow fill of
any partial assignment.  This is deliberately more general than the
deletion-produced witness in `exists_blocked_oneHoleState`; later legal fan
moves may change the location of the unique hole. -/
theorem noValidCompleteRainbowFill
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (a : PartialEdgeAssignment H (ExtensionPalette D)) (e : H.edgeSet) :
    a.NoValidCompleteRainbowFill Finset.univ e
      (distinguishedEdgeSet H J) := by
  intro c _hc hfill
  apply h.noncolorable
  let full := (a.fill e c).toEdgeAssignment hfill.2.1
  exact ⟨full,
    PartialEdgeAssignment.toEdgeAssignment_valid hfill.2.1 hfill.1,
    PartialEdgeAssignment.toEdgeAssignment_rainbowOn hfill.2.1 hfill.2.2⟩

/-- Center--terminal elementarity along a simple linear fan path.

If one palette color were missing both at the fan center and at the terminal
leaf, shift the unique hole along the path.  The shift remains valid and
distinguished-rainbow, preserves the center hole color, and preserves every
old terminal-leaf hole color.  That common color would then fill the terminal
hole, contradicting ambient noncolorability. -/
theorem center_terminal_elementary
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (c : ExtensionPalette D) :
    ¬(a.MissingAt center c ∧ a.MissingAt F.terminal.leaf c) := by
  rintro ⟨hcenter, hterminal⟩
  have hshift := F.valid_oneHoleAt_rainbowOn_shift hvalid hhole hrainbow
  have hcenterShift : F.shift.MissingAt center c :=
    (F.missingAt_center_shift_iff c).2 hcenter
  have hterminalShift : F.shift.MissingAt F.terminal.leaf c :=
    F.missingAt_terminal_shift hhole hterminal
  have hendpoints : F.shift.MissingAtEndpoints F.terminal.edge c := by
    intro v hv
    rcases F.terminal.incident_iff.mp hv with hvc | hvt
    · subst v
      exact hcenterShift
    · subst v
      exact hterminalShift
  have hfill :=
    PartialEdgeAssignment.fill_valid_complete_rainbowOn_of_oneHoleAt_missingAtEndpoints
      hshift.1 hshift.2.1 hendpoints hshift.2.2
        F.terminal_edge_not_mem
  exact h.noValidCompleteRainbowFill F.shift F.terminal.edge c
    (Finset.mem_univ c) hfill

/-- Reachability form of center--leaf elementarity.  Abstract dependency
reachability is first converted to a duplicate-free linear fan path; hence no
arbitrary walk is shifted. -/
theorem center_reachable_elementary
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {target : V}
    (hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf target)
    (c : ExtensionPalette D) :
    ¬(a.MissingAt center c ∧ a.MissingAt target c) := by
  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      root hrootJ hreach with ⟨F, hFroot, hFterminal⟩
  have hFhole : a.OneHoleAt F.root.edge := by
    simpa [hFroot] using hhole
  intro hboth
  apply h.center_terminal_elementary F hvalid hFhole hrainbow c
  exact ⟨hboth.1, by simpa [hFterminal] using hboth.2⟩

/-- Finset form of center--reachable-leaf elementarity for the full extension
palette. -/
theorem disjoint_missingColorsAt_center_reachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {target : V}
    (hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf target) :
    Disjoint (a.missingColorsAt Finset.univ center)
      (a.missingColorsAt Finset.univ target) := by
  classical
  refine Finset.disjoint_left.mpr ?_
  intro c hcenter htarget
  apply h.center_reachable_elementary root hrootJ hvalid hhole
    hrainbow hreach c
  exact ⟨(PartialEdgeAssignment.mem_missingColorsAt.mp hcenter).2,
    (PartialEdgeAssignment.mem_missingColorsAt.mp htarget).2⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
