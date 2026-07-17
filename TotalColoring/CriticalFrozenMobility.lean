import TotalColoring.CriticalGlobalMaximal
import TotalColoring.CriticalCenteredRotation
import TotalColoring.CriticalRecenteredLocation
import TotalColoring.CriticalTripleDichotomy
import TotalColoring.DependencySwap

/-!
# Elimination of the frozen triple at a global reachable maximum

Let a valid rainbow one-hole state maximize the cardinality of its canonical
center-reachable set over all oriented one-hole states of the fixed critical
member.  If a triply missing color has its center carrier in the
distinguished set, then every color unused there must occur as a missing color
on the old reachable set.

The proof is the strict-growth argument from the companion proof program.  A
center-hole/unused-color component first rotates the unused label onto the
center-hole carrier.  Among three holes of the frozen color, endpoint capacity
then supplies an off-center component.  Swapping it preserves every old
dependency and adds the external head of the first component as a new
reachable vertex, contradicting global maximality.

Fresh recentered carrier location says that an unused color cannot have such
a reachable hole.  Therefore no triply missing color is frozen: every one has
a non-distinguished center carrier and hence forces four reachable vertices.

No saturated-profile arithmetic, bound on `D`, or matching membership of the
frozen carrier is used in the strict-growth lemma.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- At a globally reach-card-maximal oriented one-hole state, a triply
missing color whose center carrier lies in `J` forces every supplied
unused-on-`J` color to have a hole on the canonical reachable set.

The conclusion is intentionally existential.  Its negation is precisely the
zero-hole premise under which the two exchanges construct a strictly larger
oriented state. -/
theorem exists_reachable_missing_of_unused_of_frozenTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {gamma delta : ExtensionPalette D} {gammaCarrier : H.edgeSet}
    (hthree : 3 ≤ ({leaf : V |
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf leaf ∧
        state.assignment.MissingAt leaf gamma} : Set V).ncard)
    (hgammaCenter : Incident state.center gammaCarrier)
    (hgammaCarrier : state.assignment.IsUniqueColorOn
      (distinguishedEdgeSet H J) gamma gammaCarrier)
    (hdeltaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) delta) :
    ∃ leaf : V,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf leaf ∧
        state.assignment.MissingAt leaf delta := by
  classical
  let a := state.assignment
  let center := state.center
  let root := state.root
  let J₀ := distinguishedEdgeSet H J
  by_contra hnoDeltaHole
  have hdeltaPresent : ∀ ⦃leaf : V⦄,
      a.CenterReachable J₀ center root.leaf leaf →
        ¬a.MissingAt leaf delta := by
    intro leaf hreach hmissing
    apply hnoDeltaHole
    exact ⟨leaf, by simpa [a, center, root, J₀] using hreach,
      by simpa [a] using hmissing⟩
  rcases h.member with ⟨x, M, hstructure⟩
  have htwoCenter :
      2 ≤ (a.missingColorsAt Finset.univ center).card :=
    PartialEdgeAssignment.two_le_missingColorsAt_card_of_palette_card_eq_of_degree_le
      a Finset.univ center D (by simp [ExtensionPalette])
        (hstructure.degree_le_parameter center)
  have hpositiveCenter :
      0 < (a.missingColorsAt Finset.univ center).card := by omega
  rcases Finset.card_pos.mp hpositiveCenter with ⟨alpha, halphaMem⟩
  have halphaCenter : a.MissingAt center alpha :=
    (PartialEdgeAssignment.mem_missingColorsAt.mp halphaMem).2
  have halphaNotUnused : ¬a.ColorUnusedOn J₀ alpha := by
    intro halphaUnused
    exact (h.not_missingAt_center_of_unused root
      (by simpa [root, J₀] using state.rootOutside)
      (by simpa [a] using state.valid)
      (by simpa [a, root] using state.oneHole)
      (by simpa [a, J₀] using state.rainbow)
      halphaUnused) halphaCenter
  rcases PartialEdgeAssignment.exists_uniqueColorOn_of_not_colorUnusedOn
      a J₀ (by simpa [a, J₀] using state.rainbow) halphaNotUnused with
    ⟨alphaCarrier, halphaCarrier⟩
  have halphaDelta : alpha ≠ delta := by
    intro hEq
    subst delta
    exact hdeltaUnused halphaCarrier.1 halphaCarrier.2.1
  have hgammaAlpha : gamma ≠ alpha := by
    intro hEq
    apply halphaCenter gammaCarrier (by simpa [center] using hgammaCenter)
    simpa [a, hEq] using hgammaCarrier.2.1
  have hgammaDelta : gamma ≠ delta := by
    intro hEq
    subst delta
    exact hdeltaUnused
      (by simpa [a, J₀] using hgammaCarrier.1)
      (by simpa [a] using hgammaCarrier.2.1)
  have hdeltaCenter : ¬a.MissingAt center delta :=
    h.not_missingAt_center_of_unused root
      (by simpa [root, J₀] using state.rootOutside)
      (by simpa [a] using state.valid)
      (by simpa [a, root] using state.oneHole)
      (by simpa [a, J₀] using state.rainbow)
      hdeltaUnused
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      a hdeltaCenter with ⟨deltaEdge, hdeltaEdgeCenter, hdeltaEdgeColor⟩
  have hdeltaEdgeOutside : deltaEdge ∉ J₀ := by
    intro hedgeJ
    exact hdeltaUnused hedgeJ hdeltaEdgeColor
  rcases Sym2.mem_iff_exists.mp hdeltaEdgeCenter with
    ⟨deltaHead, hdeltaEdgeEnds⟩
  have hdeltaHeadNeRoot : deltaHead ≠ root.leaf :=
    PartialEdgeAssignment.centerTarget_ne_root_of_colored_of_oneHoleAt
      root.endpoints (by simpa [a, root] using state.oneHole)
      hdeltaEdgeEnds hdeltaEdgeColor
  have hdeltaHeadOutsideOld :
      ¬a.CenterReachable J₀ center root.leaf deltaHead :=
    PartialEdgeAssignment.not_centerReachable_of_center_edge_color_present_on_reachable
      hdeltaHeadNeRoot hdeltaEdgeEnds hdeltaEdgeColor hdeltaPresent

  let K₀ := a.TwoColorReachabilityClass alpha delta deltaEdge
  have hdeltaEdgeSupported : a.TwoColorSupported alpha delta deltaEdge :=
    Or.inr hdeltaEdgeColor
  have hK₀ : a.IsTwoColorKempeComponent alpha delta K₀ :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      a alpha delta deltaEdge hdeltaEdgeSupported
  have hdeltaEdgeK₀ : deltaEdge ∈ K₀ :=
    PartialEdgeAssignment.root_mem_twoColorReachabilityClass
      a alpha delta deltaEdge
  have hK₀Center : EdgeSetMeetsVertex K₀ center :=
    ⟨deltaEdge, hdeltaEdgeK₀, hdeltaEdgeCenter⟩
  have halphaCarrierK₀ : alphaCarrier ∈ K₀ :=
    h.uniqueCarrier_mem_component_of_missingAt_center_of_unused
      root (by simpa [root, J₀] using state.rootOutside)
      (by simpa [a] using state.valid)
      (by simpa [a, root] using state.oneHole)
      (by simpa [a, J₀] using state.rainbow)
      halphaCenter hdeltaUnused halphaCarrier hK₀ hK₀Center
  have hsafe₀ :=
    PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_of_one_unused
      a J₀ K₀ (by simpa [a] using state.valid)
      (by simpa [a, J₀] using state.rainbow) halphaDelta hK₀
      (Or.inr hdeltaUnused)
  let b := a.swapOn alpha delta K₀
  have hbHole : b.OneHoleAt root.edge :=
    (PartialEdgeAssignment.swapOn_oneHoleAt_iff
      a alpha delta K₀ root.edge).2 (by simpa [a, root] using state.oneHole)
  have hbAlphaUnused : b.ColorUnusedOn J₀ alpha :=
    PartialEdgeAssignment.colorUnusedOn_left_swapOn_of_unused_right_of_unique_left_mem
      a J₀ K₀ halphaCarrier hdeltaUnused halphaCarrierK₀
  have hbDeltaEdgeColor : b.color deltaEdge = some alpha := by
    rw [show b.color deltaEdge =
        (a.swapOn alpha delta K₀).color deltaEdge by rfl,
      PartialEdgeAssignment.swapOn_color_of_mem
        a alpha delta K₀ hdeltaEdgeK₀, hdeltaEdgeColor]
    simp
  have hbGammaCarrierColor : b.color gammaCarrier = some gamma := by
    by_cases hcarrierK₀ : gammaCarrier ∈ K₀
    · rw [show b.color gammaCarrier =
          (a.swapOn alpha delta K₀).color gammaCarrier by rfl,
        PartialEdgeAssignment.swapOn_color_of_mem
          a alpha delta K₀ hcarrierK₀,
        show a.color gammaCarrier = some gamma by
          simpa [a] using hgammaCarrier.2.1]
      simp [Equiv.swap_apply_of_ne_of_ne hgammaAlpha hgammaDelta]
    · rw [show b.color gammaCarrier =
          (a.swapOn alpha delta K₀).color gammaCarrier by rfl,
        PartialEdgeAssignment.swapOn_color_of_not_mem
          a alpha delta K₀ hcarrierK₀]
      simpa [a] using hgammaCarrier.2.1
  have halphaPresentOld : ∀ ⦃leaf : V⦄,
      a.CenterReachable J₀ center root.leaf leaf →
        ¬a.MissingAt leaf alpha := by
    intro leaf hreach hmissing
    exact h.center_reachable_elementary root
      (by simpa [root, J₀] using state.rootOutside)
      (by simpa [a] using state.valid)
      (by simpa [a, root] using state.oneHole)
      (by simpa [a, J₀] using state.rainbow)
      hreach alpha ⟨halphaCenter, hmissing⟩
  have hbAlphaPresentOld : ∀ ⦃leaf : V⦄,
      a.CenterReachable J₀ center root.leaf leaf →
        ¬b.MissingAt leaf alpha := by
    intro leaf hreach
    exact (PartialEdgeAssignment.swapOn_component_preserves_present_both
      a hK₀ halphaDelta (halphaPresentOld hreach)
        (hdeltaPresent hreach)).1

  let T : Set V := {leaf : V |
    a.CenterReachable J₀ center root.leaf leaf ∧
      a.MissingAt leaf gamma}
  have hTthree : 3 ≤ T.ncard := by
    simpa [T, a, center, root, J₀] using hthree
  have hbGammaMissing : ∀ ⦃leaf : V⦄, leaf ∈ T →
      b.MissingAt leaf gamma := by
    intro leaf hleaf
    exact (PartialEdgeAssignment.missingAt_other_swapOn_iff
      a K₀ hgammaAlpha hgammaDelta).2 hleaf.2
  have hbAlphaPresent : ∀ ⦃leaf : V⦄, leaf ∈ T →
      ¬b.MissingAt leaf alpha := by
    intro leaf hleaf
    exact hbAlphaPresentOld hleaf.1
  have hbAlphaCenter : ¬b.MissingAt center alpha := by
    intro hmissing
    exact hmissing deltaEdge hdeltaEdgeCenter hbDeltaEdgeColor
  rcases PartialEdgeAssignment.exists_component_avoiding_vertex_of_three_missing
      hsafe₀.1 hTthree hbGammaMissing hbAlphaPresent hbAlphaCenter with
    ⟨chosen, K₁, hchosenT, hK₁, hchosenEndpoint, hK₁AvoidCenter⟩
  have hK₁MeetsChosen : EdgeSetMeetsVertex K₁ chosen :=
    ⟨hchosenEndpoint.choose, hchosenEndpoint.choose_spec.1,
      hchosenEndpoint.choose_spec.2.1⟩
  have hbChosenGamma : b.MissingAt chosen gamma :=
    hbGammaMissing hchosenT
  have hbNoOutsideGamma : ∀ ⦃edge : H.edgeSet⦄,
      Incident center edge → edge ∉ J₀ → b.color edge ≠ some gamma :=
    PartialEdgeAssignment.no_outside_center_color_of_incident_carrier
      hsafe₀.1 (by simpa [center] using hgammaCenter)
      (by simpa [a, J₀] using hgammaCarrier.1)
      hbGammaCarrierColor
  have halphaGamma : alpha ≠ gamma := Ne.symm hgammaAlpha
  have hsafe₁ :=
    PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_of_one_unused
      b J₀ K₁ hsafe₀.1 hsafe₀.2 halphaGamma hK₁
      (Or.inl hbAlphaUnused)
  let c := b.swapOn alpha gamma K₁
  have hcHole : c.OneHoleAt root.edge :=
    (PartialEdgeAssignment.swapOn_oneHoleAt_iff
      b alpha gamma K₁ root.edge).2 hbHole
  have hcChosenAlpha : c.MissingAt chosen alpha :=
    PartialEdgeAssignment.missingAt_left_swapOn_of_missing_right_of_component_meets
      b hK₁ halphaGamma hbChosenGamma hK₁MeetsChosen
  have hdeltaEdgeNotK₁ : deltaEdge ∉ K₁ := by
    intro hedgeK₁
    exact hK₁AvoidCenter hedgeK₁ hdeltaEdgeCenter
  have hcDeltaEdgeColor : c.color deltaEdge = some alpha := by
    rw [show c.color deltaEdge =
        (b.swapOn alpha gamma K₁).color deltaEdge by rfl,
      PartialEdgeAssignment.swapOn_color_of_not_mem
        b alpha gamma K₁ hdeltaEdgeNotK₁]
    exact hbDeltaEdgeColor
  have hcombinedReach : ∀ ⦃leaf : V⦄,
      a.CenterReachable J₀ center root.leaf leaf →
        c.CenterReachable J₀ center root.leaf leaf := by
    intro leaf hreach
    apply PartialEdgeAssignment.centerReachable_of_dependency_transport
      (a := a) (b := c) (J := J₀) (center := center)
      (root := root.leaf) (target := leaf) ?_ hreach
    intro source next hsource hstep
    have hstepB : b.CenterDependency J₀ center source next :=
      PartialEdgeAssignment.centerDependency_swapOn_of_source_present
        a J₀ K₀ hstep (halphaPresentOld hsource)
          (hdeltaPresent hsource)
    exact
      PartialEdgeAssignment.centerDependency_swapOn_of_source_present_left_of_no_outside_right
        b J₀ K₁ hstepB (hbAlphaPresentOld hsource) hbNoOutsideGamma
  have hcChosenReach :
      c.CenterReachable J₀ center root.leaf chosen :=
    hcombinedReach hchosenT.1
  have hcNewStep : c.CenterDependency J₀ center chosen deltaHead :=
    ⟨deltaEdge, alpha, hdeltaEdgeEnds, hdeltaEdgeOutside,
      hcDeltaEdgeColor, hcChosenAlpha⟩
  have hcDeltaHeadReach :
      c.CenterReachable J₀ center root.leaf deltaHead :=
    PartialEdgeAssignment.centerReachable_tail hcChosenReach hcNewStep
  let other : OrientedOneHoleState D H J :=
    {
      assignment := c
      center := center
      root := root
      rootOutside := by simpa [root, J₀] using state.rootOutside
      valid := hsafe₁.1
      oneHole := hcHole
      rainbow := hsafe₁.2
    }
  have hsubset : state.canonicalReachableFinset ⊆
      other.canonicalReachableFinset := by
    intro leaf hleaf
    have hreach : a.CenterReachable J₀ center root.leaf leaf := by
      simpa [OrientedOneHoleState.canonicalReachableFinset,
        a, center, root, J₀] using hleaf
    have hreachOther := hcombinedReach hreach
    simpa [OrientedOneHoleState.canonicalReachableFinset,
      other, a, b, c, center, root, J₀] using hreachOther
  have hdeltaHeadOther : deltaHead ∈ other.canonicalReachableFinset := by
    simpa [OrientedOneHoleState.canonicalReachableFinset,
      other, a, b, c, center, root, J₀] using hcDeltaHeadReach
  have hdeltaHeadOld : deltaHead ∉ state.canonicalReachableFinset := by
    intro hmem
    have hreach : a.CenterReachable J₀ center root.leaf deltaHead := by
      simpa [OrientedOneHoleState.canonicalReachableFinset,
        a, center, root, J₀] using hmem
    exact hdeltaHeadOutsideOld hreach
  have hstrict : state.canonicalReachableFinset ⊂
      other.canonicalReachableFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsubset, ?_⟩
    intro hEq
    exact hdeltaHeadOld (hEq ▸ hdeltaHeadOther)
  exact hmaximal.not_ssubset_canonicalReachableFinset other hstrict

/-- In a globally maximal state of an auxiliary critical member, every color
missing at three reachable vertices has a non-distinguished center carrier.
Thus the exceptional matching-carrier branch of the state-local dichotomy is
impossible. -/
theorem exists_mobile_centerCarrier_of_three_missing_of_globalMaximal
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {x : V} {M : Finset (Sym2 V)}
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {gamma : ExtensionPalette D}
    (hthree : 3 ≤ ({leaf : V |
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf leaf ∧
        state.assignment.MissingAt leaf gamma} : Set V).ncard) :
    ∃ gammaEdge : H.edgeSet,
      Incident state.center gammaEdge ∧
        state.assignment.color gammaEdge = some gamma ∧
        gammaEdge ∉ distinguishedEdgeSet H J ∧
        4 ≤ state.canonicalReachableFinset.card := by
  classical
  rcases h.exists_centerCarrier_mobile_or_matching_of_three_missing_centerReachable
      hstructure state.root state.rootOutside state.valid state.oneHole
      state.rainbow hthree with
    ⟨gammaEdge, hgammaCenter, hgammaColor,
      hmobile | hfrozen⟩
  · exact ⟨gammaEdge, hgammaCenter, hgammaColor,
      hmobile.1, by simpa [OrientedOneHoleState.canonicalReachableFinset]
        using hmobile.2⟩
  · let U := state.assignment.colorUnusedOnFinset
      (distinguishedEdgeSet H J)
    have hUcard : U.card = 2 := by
      simpa [U] using h.card_colorUnusedOnFinset_eq_two state.rainbow
    have hUpositive : 0 < U.card := by omega
    rcases Finset.card_pos.mp hUpositive with ⟨delta, hdeltaU⟩
    change delta ∈ state.assignment.colorUnusedOnFinset
      (distinguishedEdgeSet H J) at hdeltaU
    have hdeltaUnused : state.assignment.ColorUnusedOn
        (distinguishedEdgeSet H J) delta :=
      (PartialEdgeAssignment.mem_colorUnusedOnFinset_iff
        state.assignment (distinguishedEdgeSet H J) delta).mp hdeltaU
    rcases h.exists_reachable_missing_of_unused_of_frozenTriple
        state hmaximal hthree hgammaCenter hfrozen.2.1 hdeltaUnused with
      ⟨leaf, hreach, hmissing⟩
    exact (h.not_missingAt_centerReachable_of_unused hstructure
      state.root state.rootOutside state.valid state.oneHole state.rainbow
      hdeltaUnused hreach) hmissing |>.elim

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
