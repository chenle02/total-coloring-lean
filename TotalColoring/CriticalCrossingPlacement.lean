import TotalColoring.CriticalRecenteredLocation
import TotalColoring.CriticalRobustExpansion

/-!
# Carrier and endpoint placement for an off-center crossing component

This module isolates the placement facts used before the physical detachment
step in the `k = 2` branch.  If an off-center `alpha`--`gamma` component meets
an old reachable `gamma`-hole, exact dependency transport has the following
first-failure form: either that hole is still reachable after the swap, or an
earlier reachable vertex on the chosen dependency path is itself a
`gamma`-hole met by the component.  Thus the swapped coloring always has a
reachable affected endpoint.

When `alpha` is unused on the distinguished set and `gamma` has a unique
distinguished carrier, omitting that carrier would leave `alpha` unused after
the swap.  The affected endpoint becomes `alpha`-missing, contradicting the
fresh reachable-hole location theorem.  Consequently the crossing component
contains the literal `gamma`-carrier.

The final lemmas record the exact finite-set seam separately.  If every
affected source is external and the external-source finset is the pair
`{first, second}`, then the affected finset is contained in that pair; it is
equal to the pair once the component is known to meet both vertices.  No
unproved claim that affected sources are automatically external is made here.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- If `alpha` is unused on `J`, `gamma` has a unique carrier there, and that
carrier is not swapped, then `alpha` remains unused after an
`alpha`--`gamma` swap. -/
theorem colorUnusedOn_left_swapOn_of_unused_left_of_unique_right_not_mem
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {alpha gamma : C} {carrier : G.edgeSet}
    (halphaUnused : a.ColorUnusedOn J alpha)
    (hGamma : a.IsUniqueColorOn J gamma carrier)
    (hcarrierK : carrier ∉ K) :
    (a.swapOn alpha gamma K).ColorUnusedOn J alpha := by
  intro edge hedgeJ hedgeColor
  by_cases hedgeK : edge ∈ K
  · rw [swapOn_color_of_mem a alpha gamma K hedgeK] at hedgeColor
    rw [Option.map_eq_some_iff] at hedgeColor
    rcases hedgeColor with ⟨color, hcolor, hswap⟩
    have hcolorGamma : color = gamma := by
      rw [Equiv.swap_apply_eq_iff] at hswap
      simpa using hswap
    have hedgeGamma : a.color edge = some gamma :=
      hcolor.trans (congrArg some hcolorGamma)
    exact hcarrierK ((hGamma.2.2 hedgeJ hedgeGamma) ▸ hedgeK)
  · rw [swapOn_color_of_not_mem a alpha gamma K hedgeK] at hedgeColor
    exact halphaUnused hedgeJ hedgeColor

/-- First-failure transport along one old dependency path.  If the full path
does not survive an off-center `alpha`--`gamma` swap, its first deleted step
has a source which is already reachable in the swapped relation, misses
`gamma` in the old coloring, and is met by the component. -/
theorem centerReachable_swapOn_or_exists_reachable_gammaEndpoint
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center root target gammaTarget : V}
    {alpha gamma : C}
    (hvalid : a.Valid)
    (hK : a.IsTwoColorKempeComponent alpha gamma K)
    (halphaGamma : alpha ≠ gamma)
    (hcenterAvoid : EdgeSetAvoidsVertex K center)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      a.CenterReachable J center root vertex →
        ¬a.MissingAt vertex alpha)
    (hgammaTarget : a.IsCenterColorTarget J center gammaTarget gamma)
    (hreach : a.CenterReachable J center root target) :
    (a.swapOn alpha gamma K).CenterReachable J center root target ∨
      ∃ source : V,
        (a.swapOn alpha gamma K).CenterReachable J center root source ∧
          a.MissingAt source gamma ∧ EdgeSetMeetsVertex K source := by
  induction hreach with
  | refl =>
      exact Or.inl (centerReachable_refl
        (a.swapOn alpha gamma K) J center root)
  | @tail dependencySource dependencyTarget hprefix hdependency ih =>
      rcases ih with hprefixSwap | ⟨source, hsourceReach, hsourceGamma,
          hsourceMeets⟩
      · by_cases hexception :
          a.MissingAt dependencySource gamma ∧
            EdgeSetMeetsVertex K dependencySource ∧
            dependencyTarget = gammaTarget
        · exact Or.inr ⟨dependencySource, hprefixSwap,
            hexception.1, hexception.2.1⟩
        · have hdependencySwap :
              (a.swapOn alpha gamma K).CenterDependency
                J center dependencySource dependencyTarget :=
            (centerDependency_swapOn_iff_not_gamma_exception
              a J K hvalid hK halphaGamma hcenterAvoid
              (halphaPresent hprefix) hgammaTarget hdependency).2 hexception
          exact Or.inl (centerReachable_tail hprefixSwap hdependencySwap)
      · exact Or.inr ⟨source, hsourceReach, hsourceGamma, hsourceMeets⟩

/-- A reachable old `gamma`-endpoint guarantees some reachable affected
endpoint after the component swap.  The witness can be the supplied endpoint
or the first source at which its old dependency path fails. -/
theorem exists_reachable_gammaEndpoint_swapOn
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center root gammaTarget source : V}
    {alpha gamma : C}
    (hvalid : a.Valid)
    (hK : a.IsTwoColorKempeComponent alpha gamma K)
    (halphaGamma : alpha ≠ gamma)
    (hcenterAvoid : EdgeSetAvoidsVertex K center)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      a.CenterReachable J center root vertex →
        ¬a.MissingAt vertex alpha)
    (hgammaTarget : a.IsCenterColorTarget J center gammaTarget gamma)
    (hsourceReach : a.CenterReachable J center root source)
    (hsourceGamma : a.MissingAt source gamma)
    (hsourceMeets : EdgeSetMeetsVertex K source) :
    ∃ endpoint : V,
      (a.swapOn alpha gamma K).CenterReachable J center root endpoint ∧
        a.MissingAt endpoint gamma ∧ EdgeSetMeetsVertex K endpoint := by
  rcases centerReachable_swapOn_or_exists_reachable_gammaEndpoint
      a J K hvalid hK halphaGamma hcenterAvoid halphaPresent
      hgammaTarget hsourceReach with
    hsourceSwap | ⟨endpoint, hendpointReach, hendpointGamma,
      hendpointMeets⟩
  · exact ⟨source, hsourceSwap, hsourceGamma, hsourceMeets⟩
  · exact ⟨endpoint, hendpointReach, hendpointGamma, hendpointMeets⟩

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Every off-center component meeting a reachable `gamma`-hole crosses the
literal unique distinguished `gamma`-carrier, provided `alpha` is absent from
the distinguished set and present throughout the old reachable set.

The proof uses only first-failure dependency transport and the fresh
reachable-hole location theorem; global reach-card maximality is not needed. -/
theorem uniqueGammaCarrier_mem_offCenterComponent_of_reachable_gammaEndpoint
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {gammaTarget source : V} {gammaCarrier : H.edgeSet}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center gammaTarget gamma)
    (halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha)
    (hGamma : state.assignment.IsUniqueColorOn
      (distinguishedEdgeSet H J) gamma gammaCarrier)
    {K : Set H.edgeSet} [DecidablePred (· ∈ K)]
    (hK : state.assignment.IsTwoColorKempeComponent alpha gamma K)
    (hcenterAvoid : EdgeSetAvoidsVertex K state.center)
    (hsourceReach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf source)
    (hsourceGamma : state.assignment.MissingAt source gamma)
    (hsourceMeets : EdgeSetMeetsVertex K source) :
    gammaCarrier ∈ K := by
  by_contra hcarrierK
  rcases PartialEdgeAssignment.exists_reachable_gammaEndpoint_swapOn
      state.assignment (distinguishedEdgeSet H J) K state.valid hK
      halphaGamma hcenterAvoid halphaPresent hgammaTarget hsourceReach
      hsourceGamma hsourceMeets with
    ⟨endpoint, hendpointReach, hendpointGamma, hendpointMeets⟩
  have hsafe :=
    PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_of_one_unused
      state.assignment (distinguishedEdgeSet H J) K state.valid
      state.rainbow halphaGamma hK (Or.inl halphaUnused)
  have hhole :
      (state.assignment.swapOn alpha gamma K).OneHoleAt state.root.edge :=
    (PartialEdgeAssignment.swapOn_oneHoleAt_iff
      state.assignment alpha gamma K state.root.edge).2 state.oneHole
  have halphaUnusedSwap :
      (state.assignment.swapOn alpha gamma K).ColorUnusedOn
        (distinguishedEdgeSet H J) alpha :=
    PartialEdgeAssignment.colorUnusedOn_left_swapOn_of_unused_left_of_unique_right_not_mem
      state.assignment (distinguishedEdgeSet H J) K halphaUnused hGamma
      hcarrierK
  have hendpointAlpha :
      (state.assignment.swapOn alpha gamma K).MissingAt endpoint alpha :=
    PartialEdgeAssignment.missingAt_alpha_swapOn_of_gamma_endpoint
      state.assignment K hK halphaGamma hendpointGamma hendpointMeets
  have hendpointPresent := h.not_missingAt_centerReachable_of_unused
    hstructure state.root state.rootOutside hsafe.1 hhole hsafe.2
      halphaUnusedSwap hendpointReach
  exact hendpointPresent hendpointAlpha

end IsOutsideEdgeMinimalNoncolorable

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

omit [DecidableRel H.Adj] in
/-- If every affected source is external and the full external-source finset
is a named pair, then no third affected source exists. -/
theorem affectedMissingSourceFinset_subset_pair_of_subset_external
    (state : OrientedOneHoleState D H J)
    {gamma : ExtensionPalette D} {gammaTarget first second : V}
    {K : Set H.edgeSet}
    (hexternalPair :
      state.externalMissingSourceFinset gammaTarget gamma = {first, second})
    (haffectedExternal :
      state.affectedMissingSourceFinset gamma K ⊆
        state.externalMissingSourceFinset gammaTarget gamma) :
    state.affectedMissingSourceFinset gamma K ⊆ {first, second} := by
  intro source hsource
  rw [← hexternalPair]
  exact haffectedExternal hsource

omit [DecidableRel H.Adj] in
/-- Under the same external-source placement, if the component meets both
named external sources, the affected-source finset is exactly that pair. -/
theorem affectedMissingSourceFinset_eq_pair_of_external_pair
    (state : OrientedOneHoleState D H J)
    {gamma : ExtensionPalette D} {gammaTarget first second : V}
    {K : Set H.edgeSet}
    (hexternalPair :
      state.externalMissingSourceFinset gammaTarget gamma = {first, second})
    (haffectedExternal :
      state.affectedMissingSourceFinset gamma K ⊆
        state.externalMissingSourceFinset gammaTarget gamma)
    (hfirstMeets : EdgeSetMeetsVertex K first)
    (hsecondMeets : EdgeSetMeetsVertex K second) :
    state.affectedMissingSourceFinset gamma K = {first, second} := by
  apply Finset.Subset.antisymm
  · exact state.affectedMissingSourceFinset_subset_pair_of_subset_external
      hexternalPair haffectedExternal
  · intro source hsourcePair
    have hsourceExternal :
        source ∈ state.externalMissingSourceFinset gammaTarget gamma := by
      rw [hexternalPair]
      exact hsourcePair
    have hsourceMissing : source ∈ state.missingSourceFinset gamma :=
      ((state.mem_externalMissingSourceFinset_iff
        gammaTarget gamma source).1 hsourceExternal).1
    have hsourceMeets : EdgeSetMeetsVertex K source := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hsourcePair
      rcases hsourcePair with hsourceFirst | hsourceSecond
      · simpa [hsourceFirst] using hfirstMeets
      · simpa [hsourceSecond] using hsecondMeets
    exact (state.mem_affectedMissingSourceFinset_iff
      gamma K source).2 ⟨hsourceMissing, hsourceMeets⟩

end OrientedOneHoleState

end TotalColoring
