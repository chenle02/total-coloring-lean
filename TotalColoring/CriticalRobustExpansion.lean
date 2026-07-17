import TotalColoring.CriticalDominatorPivot
import TotalColoring.DependencyMobileSwap
import TotalColoring.PartialKempe

/-!
# Robust-column expansion at a global reachable maximum

This module closes the state-level `k = 3` expansion step.  Let `gamma` have
a direct non-distinguished center target whose incoming column is robust
against deletion of two sources.  After a centered spare rotation, let
`alpha` be unused on the distinguished set, present at every old reachable
vertex, and carried by another non-distinguished center edge.  An off-center
`alpha`--`gamma` component meeting an old reachable `gamma`-hole affects at
most two old sources, because all such sources are physical endpoints of one
two-color component.

Delete those affected entries into the `gamma` target.  Column robustness
keeps every old vertex reachable.  Exact off-center dependency transport
embeds each surviving path into the swapped dependency relation.  Meanwhile
the selected endpoint becomes `alpha`-missing and therefore reaches the
unchanged external `alpha` target.  That target was not previously reachable,
so the swap strictly enlarges the canonical reachable finset, contradicting
global maximality.

The theorem starts after the centered rotation and records precisely the
interface that rotation must supply.  It makes no criticality, auxiliary-class,
degree, or palette-size assumption beyond the data already stored in the
oriented one-hole state.
-/

namespace TotalColoring

universe u

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- The old reachable `gamma`-holes met by one physical component.  These are
exactly the old sources at which an off-center `alpha`--`gamma` swap can delete
an incoming dependency from the `gamma` column. -/
noncomputable def affectedMissingSourceFinset
    (state : OrientedOneHoleState D H J) (gamma : ExtensionPalette D)
    (K : Set H.edgeSet) : Finset V := by
  classical
  exact (state.missingSourceFinset gamma).filter fun source =>
    EdgeSetMeetsVertex K source

omit [DecidableEq V] [DecidableRel H.Adj] in
@[simp]
theorem mem_affectedMissingSourceFinset_iff
    (state : OrientedOneHoleState D H J) (gamma : ExtensionPalette D)
    (K : Set H.edgeSet) (source : V) :
    source ∈ state.affectedMissingSourceFinset gamma K ↔
      source ∈ state.missingSourceFinset gamma ∧
        EdgeSetMeetsVertex K source := by
  classical
  simp [affectedMissingSourceFinset]

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- A genuine two-color component affects at most two reachable holes of its
right-hand color. -/
theorem card_affectedMissingSourceFinset_le_two
    (state : OrientedOneHoleState D H J)
    {alpha gamma : ExtensionPalette D} {K : Set H.edgeSet}
    (hK : state.assignment.IsTwoColorKempeComponent alpha gamma K) :
    (state.affectedMissingSourceFinset gamma K).card ≤ 2 := by
  classical
  have hsubset :
      (↑(state.affectedMissingSourceFinset gamma K) : Set V) ⊆
        {source : V | EdgeSetIsEndpoint K source} := by
    intro source hsource
    change source ∈ state.affectedMissingSourceFinset gamma K at hsource
    have hparts :=
      (state.mem_affectedMissingSourceFinset_iff gamma K source).1 hsource
    have hmissing : state.assignment.MissingAt source gamma :=
      ((state.mem_missingSourceFinset_iff gamma source).1 hparts.1).2
    exact
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
        state.valid hK hmissing hparts.2
  calc
    (state.affectedMissingSourceFinset gamma K).card =
        (↑(state.affectedMissingSourceFinset gamma K) : Set V).ncard :=
      (Set.ncard_coe_finset
        (state.affectedMissingSourceFinset gamma K)).symm
    _ ≤ ({source : V | EdgeSetIsEndpoint K source} : Set V).ncard :=
      Set.ncard_le_ncard hsubset
    _ ≤ 2 :=
      PartialEdgeAssignment.edgeSetIsEndpoint_ncard_le_two_of_component
        state.valid hK

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- A colored center target whose color is present at every old reachable
source is external to the old canonical reachable set.  The one-hole root
excludes the target from being the root itself. -/
theorem centerColorTarget_not_mem_canonicalReachableFinset_of_present
    (state : OrientedOneHoleState D H J)
    {target : V} {color : ExtensionPalette D}
    (htarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center target color)
    (hpresent : ∀ ⦃source : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf source →
        ¬state.assignment.MissingAt source color) :
    target ∉ state.canonicalReachableFinset := by
  rcases htarget with ⟨edge, hedgeEnds, _hedgeJ, hedgeColor⟩
  have htargetNeRoot : target ≠ state.root.leaf :=
    PartialEdgeAssignment.centerTarget_ne_root_of_colored_of_oneHoleAt
      state.root.endpoints state.oneHole hedgeEnds hedgeColor
  have htargetNotReachable :
      ¬state.assignment.CenterReachable (distinguishedEdgeSet H J)
        state.center state.root.leaf target :=
    PartialEdgeAssignment.not_centerReachable_of_center_edge_color_present_on_reachable
      htargetNeRoot hedgeEnds hedgeColor hpresent
  intro htargetMem
  apply htargetNotReachable
  simpa [canonicalReachableFinset] using htargetMem

omit [DecidableRel H.Adj] in
/-- Robust-token expansion contradiction.  Under the post-rotation interface,
no off-center `alpha`--`gamma` component can meet a reachable `gamma`-hole
when the direct `gamma` column is robust against two entry deletions. -/
theorem not_colorColumnEntryRobust_two_of_externalTokenComponent
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {alpha gamma : ExtensionPalette D}
    (halphaGamma : alpha ≠ gamma)
    {gammaTarget alphaTarget source : V}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center gammaTarget gamma)
    (halphaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center alphaTarget alpha)
    (halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha)
    (halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha)
    {K : Set H.edgeSet} [DecidablePred (· ∈ K)]
    (hK : state.assignment.IsTwoColorKempeComponent alpha gamma K)
    (hcenterAvoid : EdgeSetAvoidsVertex K state.center)
    (hsourceReach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf source)
    (hsourceGamma : state.assignment.MissingAt source gamma)
    (hsourceMeets : EdgeSetMeetsVertex K source) :
    ¬state.ColorColumnEntryRobust gammaTarget gamma 2 := by
  classical
  intro hrobust
  let affected := state.affectedMissingSourceFinset gamma K
  let R := state.assignment.CenterDependency
    (distinguishedEdgeSet H J) state.center
  have haffectedSubset : affected ⊆ state.missingSourceFinset gamma := by
    intro vertex hvertex
    have hvertex' :
        vertex ∈ state.affectedMissingSourceFinset gamma K := by
      simpa [affected] using hvertex
    exact
      ((state.mem_affectedMissingSourceFinset_iff gamma K vertex).1
        hvertex').1
  have haffectedCard : affected.card ≤ 2 := by
    simpa [affected] using
      state.card_affectedMissingSourceFinset_le_two hK
  have hrobust' : DirectedDominator.EntryRobust R state.root.leaf
      gammaTarget (state.missingSourceFinset gamma) 2 := by
    simpa [ColorColumnEntryRobust, R] using hrobust
  have hdeletedToSwap : ∀ {target : V},
      Relation.ReflTransGen
          (DirectedDominator.DeleteEntries R gammaTarget
            (affected : Set V))
          state.root.leaf target →
        (state.assignment.swapOn alpha gamma K).CenterReachable
          (distinguishedEdgeSet H J) state.center state.root.leaf target := by
    intro target hreach
    induction hreach with
    | refl => exact Relation.ReflTransGen.refl
    | @tail dependencySource dependencyTarget hprefix hstep ih =>
        have hsourceOldR : Relation.ReflTransGen R state.root.leaf
            dependencySource :=
          Relation.ReflTransGen.mono
            (DirectedDominator.deleteEntries_le R gammaTarget
              (affected : Set V))
            state.root.leaf dependencySource hprefix
        have hsourceOld : state.assignment.CenterReachable
            (distinguishedEdgeSet H J) state.center state.root.leaf
            dependencySource := by
          simpa [R, PartialEdgeAssignment.CenterReachable] using hsourceOldR
        have hdependency : state.assignment.CenterDependency
            (distinguishedEdgeSet H J) state.center dependencySource
            dependencyTarget := by
          simpa [R] using hstep.1
        have hnewDependency :
            (state.assignment.swapOn alpha gamma K).CenterDependency
              (distinguishedEdgeSet H J) state.center dependencySource
              dependencyTarget := by
          apply
            (PartialEdgeAssignment.centerDependency_swapOn_iff_not_gamma_exception
              state.assignment (distinguishedEdgeSet H J) K state.valid hK
              halphaGamma hcenterAvoid (halphaPresent hsourceOld)
              hgammaTarget hdependency).2
          rintro ⟨hmissingGamma, hmeets, htargetEq⟩
          apply hstep.2
          refine ⟨?_, htargetEq⟩
          change dependencySource ∈ affected
          have hmissingSource : dependencySource ∈
              state.missingSourceFinset gamma :=
            (state.mem_missingSourceFinset_iff gamma dependencySource).2
              ⟨hsourceOld, hmissingGamma⟩
          have haffected : dependencySource ∈
              state.affectedMissingSourceFinset gamma K :=
            (state.mem_affectedMissingSourceFinset_iff gamma K
              dependencySource).2 ⟨hmissingSource, hmeets⟩
          simpa [affected] using haffected
        exact PartialEdgeAssignment.centerReachable_tail ih hnewDependency
  have holdSurvives : ∀ {target : V},
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf target →
        (state.assignment.swapOn alpha gamma K).CenterReachable
          (distinguishedEdgeSet H J) state.center state.root.leaf target := by
    intro target htarget
    exact hdeletedToSwap
      (hrobust' affected haffectedSubset haffectedCard target htarget)
  have hsafe :=
    PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_of_one_unused
      state.assignment (distinguishedEdgeSet H J) K state.valid
      state.rainbow halphaGamma hK (Or.inl halphaUnused)
  have hhole :
      (state.assignment.swapOn alpha gamma K).OneHoleAt state.root.edge :=
    (PartialEdgeAssignment.swapOn_oneHoleAt_iff
      state.assignment alpha gamma K state.root.edge).2 state.oneHole
  have hsourceSwapReach :
      (state.assignment.swapOn alpha gamma K).CenterReachable
        (distinguishedEdgeSet H J) state.center state.root.leaf source :=
    holdSurvives hsourceReach
  have hsourceToAlphaTarget :
      (state.assignment.swapOn alpha gamma K).CenterDependency
        (distinguishedEdgeSet H J) state.center source alphaTarget :=
    PartialEdgeAssignment.centerDependency_to_alphaTarget_swapOn_of_gamma_endpoint
      state.assignment (distinguishedEdgeSet H J) K hK halphaGamma
      hcenterAvoid hsourceGamma hsourceMeets halphaTarget
  have halphaTargetSwapReach :
      (state.assignment.swapOn alpha gamma K).CenterReachable
        (distinguishedEdgeSet H J) state.center state.root.leaf alphaTarget :=
    PartialEdgeAssignment.centerReachable_tail hsourceSwapReach
      hsourceToAlphaTarget
  have halphaTargetOld : alphaTarget ∉ state.canonicalReachableFinset :=
    state.centerColorTarget_not_mem_canonicalReachableFinset_of_present
      halphaTarget halphaPresent
  let other : OrientedOneHoleState D H J :=
    {
      assignment := state.assignment.swapOn alpha gamma K
      center := state.center
      root := state.root
      rootOutside := state.rootOutside
      valid := hsafe.1
      oneHole := hhole
      rainbow := hsafe.2
    }
  have hsubset : state.canonicalReachableFinset ⊆
      other.canonicalReachableFinset := by
    intro vertex hvertex
    have hvertexOld : state.assignment.CenterReachable
        (distinguishedEdgeSet H J) state.center state.root.leaf vertex := by
      simpa [canonicalReachableFinset] using hvertex
    have hvertexNew := holdSurvives hvertexOld
    simpa [other, canonicalReachableFinset] using hvertexNew
  have halphaTargetOther : alphaTarget ∈
      other.canonicalReachableFinset := by
    simpa [other, canonicalReachableFinset] using halphaTargetSwapReach
  have hstrict : state.canonicalReachableFinset ⊂
      other.canonicalReachableFinset := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsubset, ?_⟩
    intro hEq
    exact halphaTargetOld (hEq ▸ halphaTargetOther)
  exact hmaximal.not_ssubset_canonicalReachableFinset other hstrict

end OrientedOneHoleState

end TotalColoring
