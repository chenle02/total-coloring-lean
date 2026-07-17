import TotalColoring.CriticalCrossingPlacement
import TotalColoring.DependencyMobileSwap

/-!
# External placement of an off-center crossing component

This module closes the finite-set externality seam in the `k = 2` crossing
argument.  The key implication runs in the direction opposite to the desired
containment.  Once a nonempty off-center `alpha`--`gamma` component is known
to cross the unique distinguished `gamma`-carrier, swapping it makes `gamma`
unused on the distinguished set.  Every external `gamma`-source must then be
met by the component: otherwise its `gamma`-hole and a `gammaTarget`-avoiding
rooted path both survive, contradicting fresh reachable-hole location.

Thus the external-source finset is contained in the affected-source finset.
When there are exactly two external sources, endpoint capacity gives the
reverse containment as well, since one physical two-color component affects
at most two missing sources.  If the component affects no missing source, the
desired containment is immediate.  Consequently the affected finset is
either empty or exactly the external finset, and in particular is external.

No automatic externality is asserted without the critical fresh-location
hypothesis, the rotated-label interface, and the exact two-external-source
count.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- If `alpha` is unused on `J`, `gamma` has a unique carrier there, and that
carrier is swapped, then `gamma` is unused after the `alpha`--`gamma` swap. -/
theorem colorUnusedOn_right_swapOn_of_unused_left_of_unique_right_mem
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {alpha gamma : C} {carrier : G.edgeSet}
    (halphaUnused : a.ColorUnusedOn J alpha)
    (hGamma : a.IsUniqueColorOn J gamma carrier)
    (hcarrierK : carrier ∈ K) :
    (a.swapOn alpha gamma K).ColorUnusedOn J gamma := by
  intro edge hedgeJ hedgeColor
  by_cases hedgeK : edge ∈ K
  · rw [swapOn_color_of_mem a alpha gamma K hedgeK] at hedgeColor
    rw [Option.map_eq_some_iff] at hedgeColor
    rcases hedgeColor with ⟨color, hcolor, hswap⟩
    have hcolorAlpha : color = alpha := by
      rw [Equiv.swap_apply_eq_iff] at hswap
      simpa using hswap
    exact halphaUnused hedgeJ
      (hcolor.trans (congrArg some hcolorAlpha))
  · rw [swapOn_color_of_not_mem a alpha gamma K hedgeK] at hedgeColor
    exact hedgeK ((hGamma.2.2 hedgeJ hedgeColor) ▸ hcarrierK)

/-- A rooted dependency path avoiding the `gamma` target survives an
off-center `alpha`--`gamma` component swap.  Exact dependency transport shows
that the only possible deleted step targets `gammaTarget`, which an avoiding
path never does. -/
theorem centerReachable_swapOn_of_avoidReach_gammaTarget
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center root gammaTarget target : V}
    {alpha gamma : C}
    (hvalid : a.Valid)
    (hK : a.IsTwoColorKempeComponent alpha gamma K)
    (halphaGamma : alpha ≠ gamma)
    (hcenterAvoid : EdgeSetAvoidsVertex K center)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      a.CenterReachable J center root vertex →
        ¬a.MissingAt vertex alpha)
    (hgammaTarget : a.IsCenterColorTarget J center gammaTarget gamma)
    (havoid : DirectedDominator.AvoidReach
      (a.CenterDependency J center) root gammaTarget target) :
    (a.swapOn alpha gamma K).CenterReachable
      J center root target := by
  induction havoid with
  | refl =>
      exact centerReachable_refl (a.swapOn alpha gamma K) J center root
  | @tail source target hprefix hstep ih =>
      have hsourceReach : a.CenterReachable J center root source := by
        exact Relation.ReflTransGen.mono
          (fun _ _ step => step.1) root source hprefix
      have hdependencySwap :
          (a.swapOn alpha gamma K).CenterDependency
            J center source target := by
        apply (centerDependency_swapOn_iff_not_gamma_exception
          a J K hvalid hK halphaGamma hcenterAvoid
          (halphaPresent hsourceReach) hgammaTarget hstep.1).2
        rintro ⟨_hsourceGamma, _hsourceMeets, htarget⟩
        exact hstep.2.2 htarget
      exact centerReachable_tail ih hdependencySwap

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- For a nonempty crossing component, every external `gamma`-source is
affected.  This is the fresh-location content of the `k = 2` endpoint
placement argument; it does not use the number of external sources. -/
theorem externalMissingSourceFinset_subset_affected_of_nonempty_crossing
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {gammaTarget : V} {gammaCarrier : H.edgeSet}
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
    (haffectedNonempty :
      (state.affectedMissingSourceFinset gamma K).Nonempty) :
    state.externalMissingSourceFinset gammaTarget gamma ⊆
      state.affectedMissingSourceFinset gamma K := by
  rcases haffectedNonempty with ⟨witness, hwitnessAffected⟩
  have hwitnessParts :=
    (state.mem_affectedMissingSourceFinset_iff gamma K witness).1
      hwitnessAffected
  have hwitnessMissingParts :=
    (state.mem_missingSourceFinset_iff gamma witness).1
      hwitnessParts.1
  have hcarrierK : gammaCarrier ∈ K :=
    h.uniqueGammaCarrier_mem_offCenterComponent_of_reachable_gammaEndpoint
      hstructure state halphaGamma hgammaTarget halphaUnused halphaPresent
      hGamma hK hcenterAvoid hwitnessMissingParts.1
      hwitnessMissingParts.2 hwitnessParts.2
  have hsafe :=
    PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_of_one_unused
      state.assignment (distinguishedEdgeSet H J) K state.valid
      state.rainbow halphaGamma hK (Or.inl halphaUnused)
  have hhole :
      (state.assignment.swapOn alpha gamma K).OneHoleAt state.root.edge :=
    (PartialEdgeAssignment.swapOn_oneHoleAt_iff
      state.assignment alpha gamma K state.root.edge).2 state.oneHole
  have hgammaUnusedSwap :
      (state.assignment.swapOn alpha gamma K).ColorUnusedOn
        (distinguishedEdgeSet H J) gamma :=
    PartialEdgeAssignment.colorUnusedOn_right_swapOn_of_unused_left_of_unique_right_mem
      state.assignment (distinguishedEdgeSet H J) K halphaUnused hGamma
      hcarrierK
  intro source hsourceExternal
  by_contra hsourceAffected
  have hsourceExternalParts :=
    (state.mem_externalMissingSourceFinset_iff
      gammaTarget gamma source).1 hsourceExternal
  have hsourceMissingParts :=
    (state.mem_missingSourceFinset_iff gamma source).1
      hsourceExternalParts.1
  have hsourceNotMeets : ¬EdgeSetMeetsVertex K source := by
    intro hsourceMeets
    exact hsourceAffected
      ((state.mem_affectedMissingSourceFinset_iff gamma K source).2
        ⟨hsourceExternalParts.1, hsourceMeets⟩)
  have hsourceGammaSwap :
      (state.assignment.swapOn alpha gamma K).MissingAt source gamma :=
    (PartialEdgeAssignment.missingAt_swapOn_iff_of_avoidsVertex
      state.assignment alpha gamma K
      (edgeSetAvoidsVertex_iff_not_meets.mpr hsourceNotMeets) gamma).2
      hsourceMissingParts.2
  have hsourceReachSwap :
      (state.assignment.swapOn alpha gamma K).CenterReachable
        (distinguishedEdgeSet H J) state.center state.root.leaf source := by
    by_cases hsourceRoot : source = state.root.leaf
    · subst source
      exact PartialEdgeAssignment.centerReachable_refl
        (state.assignment.swapOn alpha gamma K)
        (distinguishedEdgeSet H J) state.center state.root.leaf
    · have hsourceAvoid :=
        DirectedDominator.avoidReach_of_not_mem_dominatorRegion
          hsourceRoot hsourceExternalParts.2
      exact
        PartialEdgeAssignment.centerReachable_swapOn_of_avoidReach_gammaTarget
          state.assignment (distinguishedEdgeSet H J) K state.valid hK
          halphaGamma hcenterAvoid halphaPresent hgammaTarget hsourceAvoid
  have hsourcePresent := h.not_missingAt_centerReachable_of_unused
    hstructure state.root state.rootOutside hsafe.1 hhole hsafe.2
      hgammaUnusedSwap hsourceReachSwap
  exact hsourcePresent hsourceGammaSwap

/-- In the exact `k = 2` setup, a nonempty affected-source finset equals the
two-source external finset.  The reverse inclusion is the fresh-location
argument above; endpoint capacity supplies the cardinal inequality. -/
theorem affectedMissingSourceFinset_eq_external_of_two_external_crossing
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {gammaTarget : V} {gammaCarrier : H.edgeSet}
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
    (htwoExternal :
      (state.externalMissingSourceFinset gammaTarget gamma).card = 2)
    (haffectedNonempty :
      (state.affectedMissingSourceFinset gamma K).Nonempty) :
    state.affectedMissingSourceFinset gamma K =
      state.externalMissingSourceFinset gammaTarget gamma := by
  have hexternalSubset :
      state.externalMissingSourceFinset gammaTarget gamma ⊆
        state.affectedMissingSourceFinset gamma K :=
    h.externalMissingSourceFinset_subset_affected_of_nonempty_crossing
      hstructure state halphaGamma hgammaTarget halphaUnused halphaPresent
      hGamma hK hcenterAvoid haffectedNonempty
  have haffectedCard :
      (state.affectedMissingSourceFinset gamma K).card ≤ 2 :=
    state.card_affectedMissingSourceFinset_le_two hK
  have heq : state.externalMissingSourceFinset gammaTarget gamma =
      state.affectedMissingSourceFinset gamma K :=
    Finset.eq_of_subset_of_card_le hexternalSubset (by
      simpa only [htwoExternal] using haffectedCard)
  exact heq.symm

/-- Exact placement dichotomy for an arbitrary off-center component in the
`k = 2` crossing setup: it either meets no old `gamma`-hole, or its affected
endpoint set is precisely the two external sources. -/
theorem affectedMissingSourceFinset_eq_empty_or_eq_external_of_two_external_crossing
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {gammaTarget : V} {gammaCarrier : H.edgeSet}
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
    (htwoExternal :
      (state.externalMissingSourceFinset gammaTarget gamma).card = 2) :
    state.affectedMissingSourceFinset gamma K = ∅ ∨
      state.affectedMissingSourceFinset gamma K =
        state.externalMissingSourceFinset gammaTarget gamma := by
  classical
  by_cases hempty : state.affectedMissingSourceFinset gamma K = ∅
  · exact Or.inl hempty
  · exact Or.inr
      (h.affectedMissingSourceFinset_eq_external_of_two_external_crossing
        hstructure state halphaGamma hgammaTarget halphaUnused
        halphaPresent hGamma hK hcenterAvoid htwoExternal
        (Finset.nonempty_iff_ne_empty.mpr hempty))

/-- The requested externality conclusion.  The empty branch is immediate;
the nonempty branch is equality with the external-source finset. -/
theorem affectedMissingSourceFinset_subset_external_of_two_external_crossing
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {gammaTarget : V} {gammaCarrier : H.edgeSet}
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
    (htwoExternal :
      (state.externalMissingSourceFinset gammaTarget gamma).card = 2) :
    state.affectedMissingSourceFinset gamma K ⊆
      state.externalMissingSourceFinset gammaTarget gamma := by
  rcases
      h.affectedMissingSourceFinset_eq_empty_or_eq_external_of_two_external_crossing
        hstructure state halphaGamma hgammaTarget halphaUnused
        halphaPresent hGamma hK hcenterAvoid htwoExternal with
    hempty | heq
  · rw [hempty]
    exact Finset.empty_subset
      (state.externalMissingSourceFinset gammaTarget gamma)
  · rw [heq]

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
