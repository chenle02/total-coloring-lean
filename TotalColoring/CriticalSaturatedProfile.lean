import TotalColoring.CriticalTripleDichotomy
import TotalColoring.FanSaturatedProfile

/-!
# Saturation of the exceptional frozen-triple profile

On the canonical center-reachable set, the critical incidence lower bound is
`2 * |W| + 1`, occurring missing colors inject into `W`, and every color has
multiplicity at most three.  This module identifies the equality case: if
there are not two distinct triply missing colors, then there is exactly one
triple, every other occurring color is missing exactly twice, the occurring-
color injection is cardinality-tight, and the incidence lower bound is an
equality.

The final wrapper derives the no-two-triples premise when every triply missing
color is assumed frozen, meaning that it has no non-distinguished center
carrier.  This is the precise state-local saturation forced by the one
exceptional branch left by `CriticalTripleDichotomy`.  It does not contradict
that branch and proves no recentering, pivot, crossing, or all-orders theorem.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- If a supplied exact triple is the only triply missing color on the
canonical reachable set, then the full missing-incidence profile is
saturated. -/
theorem saturated_centerReachable_profile_of_unique_triple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    [DecidableRel a.MissingAt]
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {gamma : ExtensionPalette D}
    (hgammaThree :
      ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf gamma} : Set V).ncard = 3)
    (hunique : ∀ theta : ExtensionPalette D,
      ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf theta} : Set V).ncard = 3 →
      theta = gamma) :
    let W := a.centerReachableFinset (distinguishedEdgeSet H J)
      center root.leaf
    let R := FanCount.occurringColors W Finset.univ a.MissingAt
    R.card = W.card ∧
      (∑ leaf ∈ W, (a.missingColorsAt Finset.univ leaf).card) =
        2 * W.card + 1 ∧
      ∀ theta ∈ R, theta ≠ gamma →
        ({leaf : V |
          a.CenterReachable (distinguishedEdgeSet H J)
              center root.leaf leaf ∧
            a.MissingAt leaf theta} : Set V).ncard = 2 := by
  classical
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  let R := FanCount.occurringColors W Finset.univ a.MissingAt
  have hgammaMultiplicity :
      FanCount.colorMultiplicity W a.MissingAt gamma = 3 := by
    rw [PartialEdgeAssignment.colorMultiplicity_centerReachableFinset_eq_ncard]
    exact hgammaThree
  have hgammaOccurs : gamma ∈ R := by
    apply (FanCount.mem_occurringColors_iff
      W Finset.univ a.MissingAt gamma).2
    exact ⟨Finset.mem_univ _, by omega⟩
  have hother : ∀ theta ∈ R, theta ≠ gamma →
      FanCount.colorMultiplicity W a.MissingAt theta ≤ 2 := by
    intro theta htheta hne
    have hleThree :
        FanCount.colorMultiplicity W a.MissingAt theta ≤ 3 := by
      rw [PartialEdgeAssignment.colorMultiplicity_centerReachableFinset_eq_ncard]
      exact h.ncard_missingAt_centerReachable_le_three
        root hrootJ hvalid hhole hrainbow theta
    have hnotThree :
        FanCount.colorMultiplicity W a.MissingAt theta ≠ 3 := by
      intro hthetaThree
      apply hne
      apply hunique theta
      rw [← PartialEdgeAssignment.colorMultiplicity_centerReachableFinset_eq_ncard]
      exact hthetaThree
    omega
  have hoccurring : R.card ≤ W.card := by
    simpa [W, R] using
      h.card_occurringColors_centerReachableFinset_le_card
        root hrootJ hvalid hhole hrainbow
  have hincidences : 2 * W.card + 1 ≤
      FanCount.incidenceCount W Finset.univ a.MissingAt := by
    rw [PartialEdgeAssignment.fanMissing_incidenceCount_eq_sum_missingColorsAt_card]
    simpa [W] using
      h.two_mul_card_centerReachableFinset_add_one_le_sum_missingColorsAt
        root hhole
  rcases FanCount.saturatedProfile_of_one_three
      W Finset.univ a.MissingAt hgammaOccurs hgammaMultiplicity
        hother hoccurring hincidences with
    ⟨hcard, hincidenceEq, hothersExact⟩
  rw [PartialEdgeAssignment.fanMissing_incidenceCount_eq_sum_missingColorsAt_card]
      at hincidenceEq
  refine ⟨hcard, hincidenceEq, ?_⟩
  intro theta htheta hne
  rw [← PartialEdgeAssignment.colorMultiplicity_centerReachableFinset_eq_ncard]
  exact hothersExact theta htheta hne

/-- If two distinct triply missing colors are excluded, the exact triple
forced by the canonical count has the saturated profile. -/
theorem exists_saturated_centerReachable_profile_of_no_two_triples
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    [DecidableRel a.MissingAt]
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (hnoTwo : ∀ alpha gamma : ExtensionPalette D, alpha ≠ gamma →
      ¬(3 ≤ ({leaf : V |
          a.CenterReachable (distinguishedEdgeSet H J)
              center root.leaf leaf ∧
            a.MissingAt leaf alpha} : Set V).ncard ∧
        3 ≤ ({leaf : V |
          a.CenterReachable (distinguishedEdgeSet H J)
              center root.leaf leaf ∧
            a.MissingAt leaf gamma} : Set V).ncard)) :
    ∃ gamma : ExtensionPalette D,
      ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf gamma} : Set V).ncard = 3 ∧
      let W := a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf
      let R := FanCount.occurringColors W Finset.univ a.MissingAt
      R.card = W.card ∧
        (∑ leaf ∈ W, (a.missingColorsAt Finset.univ leaf).card) =
          2 * W.card + 1 ∧
        ∀ theta ∈ R, theta ≠ gamma →
          ({leaf : V |
            a.CenterReachable (distinguishedEdgeSet H J)
                center root.leaf leaf ∧
              a.MissingAt leaf theta} : Set V).ncard = 2 := by
  rcases h.exists_eq_three_missing_centerReachable root hrootJ
      hvalid hhole hrainbow with ⟨gamma, hgammaThree⟩
  have hunique : ∀ theta : ExtensionPalette D,
      ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf theta} : Set V).ncard = 3 →
      theta = gamma := by
    intro theta hthetaThree
    by_contra hne
    exact hnoTwo theta gamma hne
      ⟨by omega, by omega⟩
  exact ⟨gamma, hgammaThree,
    h.saturated_centerReachable_profile_of_unique_triple
      root hrootJ hvalid hhole hrainbow hgammaThree hunique⟩

/-- If every triply missing color lacks a mobile non-distinguished center
carrier, the one exceptional frozen branch is forced into the saturated
profile: there is one triple, all other occurring colors are double, and both
cardinality inequalities are equalities. -/
theorem exists_saturated_centerReachable_profile_of_all_triples_frozen
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {x : V} {M : Finset (Sym2 V)}
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    [DecidableRel a.MissingAt]
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (hnoMobile : ∀ theta : ExtensionPalette D,
      3 ≤ ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf theta} : Set V).ncard →
      ¬∃ eTheta : H.edgeSet,
        Incident center eTheta ∧
        a.color eTheta = some theta ∧
        eTheta ∉ distinguishedEdgeSet H J) :
    ∃ gamma : ExtensionPalette D,
      ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf gamma} : Set V).ncard = 3 ∧
      let W := a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf
      let R := FanCount.occurringColors W Finset.univ a.MissingAt
      R.card = W.card ∧
        (∑ leaf ∈ W, (a.missingColorsAt Finset.univ leaf).card) =
          2 * W.card + 1 ∧
        ∀ theta ∈ R, theta ≠ gamma →
          ({leaf : V |
            a.CenterReachable (distinguishedEdgeSet H J)
                center root.leaf leaf ∧
              a.MissingAt leaf theta} : Set V).ncard = 2 := by
  have hnoTwo : ∀ alpha gamma : ExtensionPalette D, alpha ≠ gamma →
      ¬(3 ≤ ({leaf : V |
          a.CenterReachable (distinguishedEdgeSet H J)
              center root.leaf leaf ∧
            a.MissingAt leaf alpha} : Set V).ncard ∧
        3 ≤ ({leaf : V |
          a.CenterReachable (distinguishedEdgeSet H J)
              center root.leaf leaf ∧
            a.MissingAt leaf gamma} : Set V).ncard) := by
    intro alpha gamma hne hboth
    rcases h.exists_mobile_centerCarrier_of_two_distinct_three_missing_centerReachable
        hstructure root hrootJ hvalid hhole hrainbow hne hboth.1 hboth.2 with
      ⟨theta, eTheta, htheta, hcenter, hcolor, houtside, _hfour⟩
    have hthetaThree : 3 ≤ ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf theta} : Set V).ncard := by
      rcases htheta with rfl | rfl
      · exact hboth.1
      · exact hboth.2
    exact hnoMobile theta hthetaThree
      ⟨eTheta, hcenter, hcolor, houtside⟩
  exact h.exists_saturated_centerReachable_profile_of_no_two_triples
    root hrootJ hvalid hhole hrainbow hnoTwo

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
