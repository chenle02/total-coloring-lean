import TotalColoring.CriticalFanCapacity
import TotalColoring.CriticalMatchingCarriers

/-!
# State-local exact-triple dichotomy

In a supplied critical one-hole state, choose the exact triply missing color
provided by the full reachable-set count and expose its center carrier.  If
that carrier lies outside the distinguished set, the mobile-triple theorem
forces four reachable vertices.  If it lies in the distinguished set, the
local three-leaf theorem identifies that literal carrier as a member of the
matching part of the supplied auxiliary presentation.

The second branch is not a contradiction.  The matching is off the auxiliary
star center `x`, not the current fan center `center`; its returned carrier is
explicitly incident with `center`.  This result chooses one exact triple and
asserts neither mobility of an arbitrary triple nor cross-state or global
maximality of the reachable set.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A chosen exact triply missing color has a literal center carrier which is
either mobile outside `J`, forcing `4 ≤ |W|`, or is the unique distinguished
carrier and belongs to the matching part `M` of the supplied presentation.

The common incidence conclusion refers to the current fan center `center`.
Membership in `M` refers instead to the auxiliary star center `x`, so the
second branch is a live frozen-carrier branch rather than a contradiction. -/
theorem exists_exactTriple_mobile_or_centerMatchingCarrier
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    ∃ (gamma : ExtensionPalette D) (eGamma : H.edgeSet),
      ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf gamma} : Set V).ncard = 3 ∧
      Incident center eGamma ∧
      a.color eGamma = some gamma ∧
      ((eGamma ∉ distinguishedEdgeSet H J ∧
          4 ≤ (a.centerReachableFinset (distinguishedEdgeSet H J)
            center root.leaf).card) ∨
        (eGamma ∈ distinguishedEdgeSet H J ∧
          a.IsUniqueColorOn (distinguishedEdgeSet H J) gamma eGamma ∧
          (eGamma : Sym2 V) ∈ M)) := by
  classical
  rcases h.exists_eq_three_missing_centerReachable root hrootJ
      hvalid hhole hrainbow with ⟨gamma, hgammaThree⟩
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf ∧
      a.MissingAt leaf gamma}
  have hthree : 3 ≤ S.ncard := by
    change S.ncard = 3 at hgammaThree
    omega
  have hpositiveTriple : 0 < S.ncard := by omega
  rcases (Set.ncard_pos (s := S)).mp hpositiveTriple with ⟨leaf, hleaf⟩
  have hnotGammaCenter : ¬a.MissingAt center gamma := by
    intro hcenterGamma
    exact h.center_reachable_elementary root hrootJ hvalid hhole
      hrainbow hleaf.1 gamma ⟨hcenterGamma, hleaf.2⟩
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      a hnotGammaCenter with ⟨eGamma, heGammaIncident, heGammaColor⟩
  refine ⟨gamma, eGamma, hgammaThree, heGammaIncident, heGammaColor, ?_⟩
  by_cases heGammaJ : eGamma ∈ distinguishedEdgeSet H J
  · right
    have hGammaLiteral :
        a.IsUniqueColorOn (distinguishedEdgeSet H J) gamma eGamma :=
      PartialEdgeAssignment.isUniqueColorOn_of_rainbowOn
        a (distinguishedEdgeSet H J) hrainbow heGammaJ heGammaColor
    have htwoMissing :
        2 ≤ (a.missingColorsAt Finset.univ center).card :=
      PartialEdgeAssignment.two_le_missingColorsAt_card_of_palette_card_eq_of_degree_le
        a Finset.univ center D (by simp [ExtensionPalette])
          (hstructure.degree_le_parameter center)
    have hpositive :
        0 < (a.missingColorsAt Finset.univ center).card := by omega
    rcases Finset.card_pos.mp hpositive with ⟨alpha, halphaMem⟩
    have halphaMissing : a.MissingAt center alpha :=
      (PartialEdgeAssignment.mem_missingColorsAt.mp halphaMem).2
    have halphagamma : alpha ≠ gamma := by
      intro heq
      exact hnotGammaCenter (heq ▸ halphaMissing)
    rcases h.exists_matching_carriers_of_three_missing_centerReachable
        hstructure root hrootJ hvalid hhole hrainbow halphagamma
        halphaMissing hthree with
      ⟨eAlpha, eGamma', hAlpha, hGamma', heAlphaM, heGammaM⟩
    have heq : eGamma = eGamma' :=
      hGamma'.2.2 heGammaJ heGammaColor
    exact ⟨heGammaJ, hGammaLiteral, heq ▸ heGammaM⟩
  · left
    refine ⟨heGammaJ, ?_⟩
    exact
      PartialEdgeAssignment.four_le_card_centerReachableFinset_of_three_missing_of_mobile
        a (distinguishedEdgeSet H J) hthree heGammaIncident heGammaJ
          heGammaColor

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
