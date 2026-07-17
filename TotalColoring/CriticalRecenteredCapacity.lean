import TotalColoring.CriticalFanCapacity
import TotalColoring.CriticalRecenteredLocation

/-!
# Recentered zero-hole and capacity consequences

Fresh endpoint matching location, transported along a legal fan shift, shows
that a color unused on the distinguished set cannot be missing at any
dependency-reachable vertex.  This module packages that pointwise statement
as the literal finite equality `z = 0` and removes the `z` term from the
earlier state-local fan-capacity inequality.

These are still conditional consequences inside a supplied outside-edge-
minimal noncolorable state.  They do not prove mobility of every triple,
cross-state maximality, a pivot, crossing, or the all-orders extension.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- No color unused on `J` occurs as a missing color on the canonical
dependency-reachable set.  This is the literal finite-set form of `z = 0`. -/
theorem occurringUnused_centerReachable_eq_empty
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    FanCount.occurringColors
        (a.centerReachableFinset (distinguishedEdgeSet H J)
          center root.leaf)
        (a.colorUnusedOnFinset (distinguishedEdgeSet H J))
        a.MissingAt = ∅ := by
  classical
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  let U := a.colorUnusedOnFinset (distinguishedEdgeSet H J)
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro color hcolor
  have hparts := (FanCount.mem_occurringColors_iff
    W U a.MissingAt color).mp (by simpa [W, U] using hcolor)
  have hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) color :=
    (PartialEdgeAssignment.mem_colorUnusedOnFinset_iff
      a (distinguishedEdgeSet H J) color).mp hparts.1
  have hpositive : 0 <
      (W.filter fun leaf ↦ a.MissingAt leaf color).card := hparts.2
  rcases Finset.card_pos.mp hpositive with ⟨leaf, hleaf⟩
  have hleafParts := Finset.mem_filter.mp hleaf
  have hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf leaf := by
    simpa [W] using hleafParts.1
  exact h.not_missingAt_centerReachable_of_unused hstructure
    root hrootJ hvalid hhole hrainbow hunused hreach hleafParts.2

/-- Cardinal form of the recentered zero-hole theorem. -/
theorem card_occurringUnused_centerReachable_eq_zero
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    (FanCount.occurringColors
        (a.centerReachableFinset (distinguishedEdgeSet H J)
          center root.leaf)
        (a.colorUnusedOnFinset (distinguishedEdgeSet H J))
        a.MissingAt).card = 0 := by
  rw [h.occurringUnused_centerReachable_eq_empty hstructure
    root hrootJ hvalid hhole hrainbow]
  rfl

/-- Recentered fan capacity with the old unused-hole correction removed. -/
theorem card_centerReachable_add_centerMissing_le_parameter
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    (a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf).card +
        (a.missingColorsAt Finset.univ center).card ≤ D := by
  have hcapacity :=
    h.card_centerReachable_add_centerMissing_le_parameter_add_occurringUnused
      root hrootJ hvalid hhole hrainbow
  have hzero := h.card_occurringUnused_centerReachable_eq_zero hstructure
    root hrootJ hvalid hhole hrainbow
  omega

/-- The center-missing colors and all distinct reachable missing colors fit
inside the matching, whose complement in the distinguished set is the full
auxiliary-center star. -/
theorem card_centerMissing_add_occurringColors_add_auxiliaryCenterDegree_le_parameter
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    let W := a.centerReachableFinset (distinguishedEdgeSet H J)
      center root.leaf
    let A := a.missingColorsAt Finset.univ center
    let R := FanCount.occurringColors W Finset.univ a.MissingAt
    A.card + R.card + H.degree x ≤ D := by
  have hmatching :=
    h.card_centerMissing_add_occurringColors_le_card_matching hstructure
      root hrootJ hvalid hhole hrainbow
  have hpartition := hstructure.card_matching_add_center_degree_eq_parameter
  omega

/-- When the occurring-color injection is saturated, recentered matching
capacity bounds the reachable set, the center holes, and the auxiliary star
simultaneously. -/
theorem card_centerReachable_add_centerMissing_add_auxiliaryCenterDegree_le_parameter_of_saturated
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (hsaturated :
      (FanCount.occurringColors
        (a.centerReachableFinset (distinguishedEdgeSet H J)
          center root.leaf)
        Finset.univ a.MissingAt).card =
      (a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf).card) :
    (a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf).card +
        (a.missingColorsAt Finset.univ center).card + H.degree x ≤ D := by
  have hcapacity :=
    h.card_centerMissing_add_occurringColors_add_auxiliaryCenterDegree_le_parameter
      hstructure root hrootJ hvalid hhole hrainbow
  omega

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
