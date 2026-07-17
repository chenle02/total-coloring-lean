import TotalColoring.CriticalFanCapacity
import TotalColoring.CriticalMatchingCarriers

/-!
# State-local triple-carrier dichotomy

In a supplied critical one-hole state, every supplied color missing on at
least three reachable leaves has a center carrier.  If that carrier lies
outside the distinguished set, the mobile-triple theorem forces four
reachable vertices.
If it lies in the distinguished set, the local three-leaf theorem identifies
that literal carrier as a member of the matching part of the supplied
auxiliary presentation.  The exact triple provided by the full reachable-set
count is an immediate corollary.

The second branch is not a contradiction.  The matching is off the auxiliary
star center `x`, not the current fan center `center`; its returned carrier is
explicitly incident with `center`.  Matching edges incident with one fixed
vertex carry at most one color, so among two distinct triply missing colors at
least one is mobile.  This permits one exceptional frozen color and asserts
neither all-triple mobility nor cross-state or global maximality of the
reachable set.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x center : V}
variable {J M : Finset (Sym2 V)} [DecidableRel H.Adj]

/-- At a fixed vertex, the colors carried there by edges of the matching part
of an auxiliary presentation form a subsingleton set.  This is purely
state-local: distinct matching edges cannot share the fixed vertex, so the
literal carrier edges, and hence their colors, must coincide. -/
theorem centerMatchingCarrierColors_subsingleton
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {C : Type v} (a : PartialEdgeAssignment H C) (center : V) :
    ({color : C | ∃ edge : H.edgeSet,
      Incident center edge ∧
      a.color edge = some color ∧
      (edge : Sym2 V) ∈ M} : Set C).Subsingleton := by
  intro alpha halpha gamma hgamma
  rcases halpha with ⟨eAlpha, heAlphaCenter, heAlphaColor, heAlphaM⟩
  rcases hgamma with ⟨eGamma, heGammaCenter, heGammaColor, heGammaM⟩
  have hedgePair : (eAlpha : Sym2 V) = (eGamma : Sym2 V) := by
    by_contra hne
    exact (hstructure.matching heAlphaM heGammaM hne heAlphaCenter)
      heGammaCenter
  have hedge : eAlpha = eGamma := Subtype.ext hedgePair
  subst eGamma
  exact Option.some.inj (heAlphaColor.symm.trans heGammaColor)

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Every supplied color missing on at least three reachable leaves has a
literal center carrier which is either mobile outside `J`, forcing
`4 ≤ |W|`, or is the unique distinguished carrier and belongs to the matching
part `M` of the supplied presentation.

The common incidence conclusion refers to the current fan center `center`.
Membership in `M` refers instead to the auxiliary star center `x`, so the
second branch is a live frozen-carrier branch rather than a contradiction. -/
theorem exists_centerCarrier_mobile_or_matching_of_three_missing_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {gamma : ExtensionPalette D}
    (hthree : 3 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard) :
    ∃ eGamma : H.edgeSet,
      Incident center eGamma ∧
      a.color eGamma = some gamma ∧
      ((eGamma ∉ distinguishedEdgeSet H J ∧
          4 ≤ (a.centerReachableFinset (distinguishedEdgeSet H J)
            center root.leaf).card) ∨
        (eGamma ∈ distinguishedEdgeSet H J ∧
          a.IsUniqueColorOn (distinguishedEdgeSet H J) gamma eGamma ∧
          (eGamma : Sym2 V) ∈ M)) := by
  classical
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf ∧
      a.MissingAt leaf gamma}
  have hpositiveTriple : 0 < S.ncard := by
    change 3 ≤ S.ncard at hthree
    omega
  rcases (Set.ncard_pos (s := S)).mp hpositiveTriple with ⟨leaf, hleaf⟩
  have hnotGammaCenter : ¬a.MissingAt center gamma := by
    intro hcenterGamma
    exact h.center_reachable_elementary root hrootJ hvalid hhole
      hrainbow hleaf.1 gamma ⟨hcenterGamma, hleaf.2⟩
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      a hnotGammaCenter with ⟨eGamma, heGammaIncident, heGammaColor⟩
  refine ⟨eGamma, heGammaIncident, heGammaColor, ?_⟩
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

/-- Of two distinct colors each missing on at least three reachable leaves,
at least one has a non-distinguished center carrier and hence forces four
reachable vertices.  The matching argument rules out two frozen branches but
still allows one exceptional frozen color. -/
theorem exists_mobile_centerCarrier_of_two_distinct_three_missing_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha gamma : ExtensionPalette D} (halphagamma : alpha ≠ gamma)
    (hthreeAlpha : 3 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf alpha} : Set V).ncard)
    (hthreeGamma : 3 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard) :
    ∃ (theta : ExtensionPalette D) (eTheta : H.edgeSet),
      (theta = alpha ∨ theta = gamma) ∧
      Incident center eTheta ∧
      a.color eTheta = some theta ∧
      eTheta ∉ distinguishedEdgeSet H J ∧
      4 ≤ (a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf).card := by
  rcases h.exists_centerCarrier_mobile_or_matching_of_three_missing_centerReachable
      hstructure root hrootJ hvalid hhole hrainbow hthreeAlpha with
    ⟨eAlpha, heAlphaCenter, heAlphaColor, hAlphaMobile | hAlphaMatching⟩
  · exact ⟨alpha, eAlpha, Or.inl rfl, heAlphaCenter, heAlphaColor,
      hAlphaMobile.1, hAlphaMobile.2⟩
  rcases h.exists_centerCarrier_mobile_or_matching_of_three_missing_centerReachable
      hstructure root hrootJ hvalid hhole hrainbow hthreeGamma with
    ⟨eGamma, heGammaCenter, heGammaColor, hGammaMobile | hGammaMatching⟩
  · exact ⟨gamma, eGamma, Or.inr rfl, heGammaCenter, heGammaColor,
      hGammaMobile.1, hGammaMobile.2⟩
  exfalso
  apply halphagamma
  apply PartialEdgeAssignment.centerMatchingCarrierColors_subsingleton
    hstructure a center
  · exact ⟨eAlpha, heAlphaCenter, heAlphaColor, hAlphaMatching.2.2⟩
  · exact ⟨eGamma, heGammaCenter, heGammaColor, hGammaMatching.2.2⟩

/-- The exact triple forced by the reachable-set count satisfies the universal
supplied-color carrier dichotomy. -/
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
  rcases h.exists_eq_three_missing_centerReachable root hrootJ
      hvalid hhole hrainbow with ⟨gamma, hgammaThree⟩
  have hthree : 3 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard := by omega
  rcases h.exists_centerCarrier_mobile_or_matching_of_three_missing_centerReachable
      hstructure root hrootJ hvalid hhole hrainbow hthree with
    ⟨eGamma, heGammaCenter, heGammaColor, hdichotomy⟩
  exact ⟨gamma, eGamma, hgammaThree, heGammaCenter, heGammaColor, hdichotomy⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
