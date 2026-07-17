import TotalColoring.CriticalMatchingCarriers
import TotalColoring.CriticalReachableCount

/-!
# Fresh-centered endpoint matching location

The exact-triple count is available for every supplied valid rainbow one-hole
state and every orientation of its hole.  Combining that fresh triple with
the local two-carrier matching theorem shows that every color missing at the
chosen center is carried by the matching part of the distinguished set.
Reversing the same literal spoke gives the corresponding conclusion at the
other endpoint.

The continuation transports the literal matching carrier back through a fan
shift, proving matching location for every dependency-reachable missing
color in the original state.  It does not compare canonical reachable sets
from different states, construct a globally maximal state, formalize root
pivots, or prove the later crossing argument.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Every color missing at the chosen endpoint of a critical hole has a
unique distinguished carrier, and that carrier belongs to the matching part
of the supplied auxiliary presentation. -/
theorem exists_matching_carrier_of_missingAt_center
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha : ExtensionPalette D} (hcenter : a.MissingAt center alpha) :
    ∃ eAlpha : H.edgeSet,
      a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha eAlpha ∧
        (eAlpha : Sym2 V) ∈ M := by
  rcases h.exists_eq_three_missing_centerReachable root hrootJ
      hvalid hhole hrainbow with ⟨gamma, hgammaThree⟩
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf ∧
      a.MissingAt leaf gamma}
  have hpositive : 0 < S.ncard := by
    change S.ncard = 3 at hgammaThree
    omega
  rcases (Set.ncard_pos (s := S)).mp hpositive with ⟨leaf, hleaf⟩
  have hnotGammaCenter : ¬a.MissingAt center gamma := by
    intro hcenterGamma
    exact h.center_reachable_elementary root hrootJ hvalid hhole
      hrainbow hleaf.1 gamma ⟨hcenterGamma, hleaf.2⟩
  have halphaGamma : alpha ≠ gamma := by
    intro hEq
    subst alpha
    exact hnotGammaCenter hcenter
  have hthree : 3 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard := by
    omega
  rcases h.exists_matching_carriers_of_three_missing_centerReachable
      hstructure root hrootJ hvalid hhole hrainbow halphaGamma
        hcenter hthree with
    ⟨eAlpha, _eGamma, hAlpha, _hGamma, heAlphaM, _heGammaM⟩
  exact ⟨eAlpha, hAlpha, heAlphaM⟩

/-- The same endpoint-location theorem at the other endpoint of the literal
hole edge, obtained by reversing its orientation. -/
theorem exists_matching_carrier_of_missingAt_leaf
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha : ExtensionPalette D} (hleaf : a.MissingAt root.leaf alpha) :
    ∃ eAlpha : H.edgeSet,
      a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha eAlpha ∧
        (eAlpha : Sym2 V) ∈ M := by
  exact h.exists_matching_carrier_of_missingAt_center hstructure
    root.reverse (by simpa using hrootJ) hvalid (by simpa using hhole)
      hrainbow hleaf

/-- Combined fresh-centered location theorem for both endpoints of the
critical hole. -/
theorem endpoint_missing_colors_have_matching_carriers
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    (∀ {alpha : ExtensionPalette D}, a.MissingAt center alpha →
      ∃ eAlpha : H.edgeSet,
        a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha eAlpha ∧
          (eAlpha : Sym2 V) ∈ M) ∧
    (∀ {alpha : ExtensionPalette D}, a.MissingAt root.leaf alpha →
      ∃ eAlpha : H.edgeSet,
        a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha eAlpha ∧
          (eAlpha : Sym2 V) ∈ M) := by
  exact ⟨
    fun hcenter ↦ h.exists_matching_carrier_of_missingAt_center
      hstructure root hrootJ hvalid hhole hrainbow hcenter,
    fun hleaf ↦ h.exists_matching_carrier_of_missingAt_leaf
      hstructure root hrootJ hvalid hhole hrainbow hleaf⟩

/-- Every color missing at any dependency-reachable leaf has its unique
distinguished carrier in the matching.  The proof shifts the hole along a
simple fan path to that leaf, applies the fresh-centered endpoint theorem,
and transports the unchanged distinguished carrier back through the shift. -/
theorem exists_matching_carrier_of_missingAt_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {target : V}
    (hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf target)
    {alpha : ExtensionPalette D} (hmissing : a.MissingAt target alpha) :
    ∃ eAlpha : H.edgeSet,
      a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha eAlpha ∧
        (eAlpha : Sym2 V) ∈ M := by
  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      root hrootJ hreach with ⟨F, hFroot, hFterminal⟩
  have hFhole : a.OneHoleAt F.root.edge := by
    simpa [hFroot] using hhole
  have hshift := F.valid_oneHoleAt_rainbowOn_shift
    hvalid hFhole hrainbow
  have hmissingShift : F.shift.MissingAt F.terminal.leaf alpha :=
    F.missingAt_terminal_shift hFhole (by
      simpa [hFterminal] using hmissing)
  rcases h.exists_matching_carrier_of_missingAt_center hstructure
      F.terminal.reverse (by exact F.terminal_edge_not_mem)
        hshift.1 (by simpa using hshift.2.1) hshift.2.2
        hmissingShift with
    ⟨eAlpha, hAlphaShift, heAlphaM⟩
  exact ⟨eAlpha, (F.isUniqueColorOn_shift_iff).1 hAlphaShift,
    heAlphaM⟩

/-- A color unused on the distinguished set has no hole anywhere in the
canonical dependency-reachable set.  This is the formal `z = 0` consequence
of fresh recentering. -/
theorem not_missingAt_centerReachable_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {delta : ExtensionPalette D}
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    {target : V}
    (hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf target) :
    ¬a.MissingAt target delta := by
  intro hmissing
  rcases h.exists_matching_carrier_of_missingAt_centerReachable
      hstructure root hrootJ hvalid hhole hrainbow hreach hmissing with
    ⟨carrier, hcarrier, _hcarrierM⟩
  exact hunused hcarrier.1 hcarrier.2.1

/-- Distinct colors missing at the center or somewhere in the canonical
reachable set inject into distinct edges of the matching.  Center--reachable
elementarity makes the two color finsets disjoint, so their cardinalities
add. -/
theorem card_centerMissing_add_occurringColors_le_card_matching
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    [DecidableRel a.MissingAt]
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    let W := a.centerReachableFinset (distinguishedEdgeSet H J)
      center root.leaf
    let A := a.missingColorsAt Finset.univ center
    let R := FanCount.occurringColors W Finset.univ a.MissingAt
    A.card + R.card ≤ M.card := by
  classical
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  let A := a.missingColorsAt Finset.univ center
  let R := FanCount.occurringColors W Finset.univ a.MissingAt
  have hdatum (color : ExtensionPalette D)
      (hcolor : color ∈ A ∪ R) :
      ∃ carrier : H.edgeSet,
        a.IsUniqueColorOn (distinguishedEdgeSet H J) color carrier ∧
          (carrier : Sym2 V) ∈ M := by
    rcases Finset.mem_union.mp hcolor with hcolorA | hcolorR
    · exact h.exists_matching_carrier_of_missingAt_center hstructure
        root hrootJ hvalid hhole hrainbow
          (PartialEdgeAssignment.mem_missingColorsAt.mp hcolorA).2
    · have hocc := (FanCount.mem_occurringColors_iff
        W Finset.univ a.MissingAt color).mp hcolorR
      have hpositive : 0 <
          (W.filter fun leaf ↦ a.MissingAt leaf color).card := hocc.2
      rcases Finset.card_pos.mp hpositive with ⟨leaf, hleaf⟩
      have hleafParts := Finset.mem_filter.mp hleaf
      have hreach : a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf := by
        simpa [W] using hleafParts.1
      exact h.exists_matching_carrier_of_missingAt_centerReachable
        hstructure root hrootJ hvalid hhole hrainbow hreach hleafParts.2
  let carrier (color : {color // color ∈ A ∪ R}) : H.edgeSet :=
    Classical.choose (hdatum color.1 color.2)
  have hcarrierSpec (color : {color // color ∈ A ∪ R}) :
      a.IsUniqueColorOn (distinguishedEdgeSet H J) color.1
          (carrier color) ∧
        ((carrier color : H.edgeSet) : Sym2 V) ∈ M :=
    Classical.choose_spec (hdatum color.1 color.2)
  let embed : {color // color ∈ A ∪ R} → {edge // edge ∈ M} :=
    fun color ↦ ⟨(carrier color : Sym2 V), (hcarrierSpec color).2⟩
  have hinjective : Function.Injective embed := by
    intro color color' heq
    apply Subtype.ext
    have hpairs : ((carrier color : H.edgeSet) : Sym2 V) =
        ((carrier color' : H.edgeSet) : Sym2 V) :=
      congrArg (fun edge : {edge // edge ∈ M} ↦ edge.1) heq
    have hedges : carrier color = carrier color' := Subtype.ext hpairs
    apply Option.some.inj
    calc
      some color.1 = a.color (carrier color) :=
        (hcarrierSpec color).1.2.1.symm
      _ = a.color (carrier color') := by rw [hedges]
      _ = some color'.1 := (hcarrierSpec color').1.2.1
  have hunionCard : (A ∪ R).card ≤ M.card := by
    simpa only [Fintype.card_coe] using
      (Fintype.card_le_of_injective embed hinjective)
  have hdisjoint : Disjoint A R := by
    apply Finset.disjoint_left.mpr
    intro color hcolorA hcolorR
    have hcenter : a.MissingAt center color :=
      (PartialEdgeAssignment.mem_missingColorsAt.mp hcolorA).2
    have hocc := (FanCount.mem_occurringColors_iff
      W Finset.univ a.MissingAt color).mp hcolorR
    have hpositive : 0 <
        (W.filter fun leaf ↦ a.MissingAt leaf color).card := hocc.2
    rcases Finset.card_pos.mp hpositive with ⟨leaf, hleaf⟩
    have hleafParts := Finset.mem_filter.mp hleaf
    have hreach : a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf := by
      simpa [W] using hleafParts.1
    exact h.center_reachable_elementary root hrootJ hvalid hhole
      hrainbow hreach color ⟨hcenter, hleafParts.2⟩
  change A.card + R.card ≤ M.card
  rw [← Finset.card_union_of_disjoint hdisjoint]
  exact hunionCard

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
