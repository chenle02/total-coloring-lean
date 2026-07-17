import TotalColoring.CriticalDominator

/-!
# Dominator transport through a root pivot

After pivoting from an old root `r` to a direct target `q`, every old path
which started at `q` has a new `q`-rooted realization avoiding `r`.  If an old
path re-enters `q`, its earlier loop is discarded.  No old dependency can
enter `r` because the old `center-r` edge was the unique hole, and every other
dependency survives by the exact root-pivot column formula.

The path-transport seam supports the final `k = 1` theorem below: a direct
triple column with only the old root external becomes robust against any two
selected entry deletions after the pivot.  This remains a dependency-digraph
statement; it does not yet identify physical recolorings with those deletions.
-/

namespace TotalColoring

universe u

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

omit [Fintype V] [DecidableRel H.Adj] in
/-- Old reachability from the new root becomes new reachability avoiding the
old root after a literal pivot. -/
theorem avoidReach_rootPivot_from_newRoot
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {target : V}
    (hreach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center next.leaf target) :
    DirectedDominator.AvoidReach
      ((state.rootPivot next hstep).assignment.CenterDependency
        (distinguishedEdgeSet H J) state.center)
      next.leaf state.root.leaf target := by
  classical
  rcases hstep with ⟨pivotColor, hnextJ, hnextColor, hrootMissing⟩
  let hfan : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next :=
    ⟨pivotColor, hnextJ, hnextColor, hrootMissing⟩
  have hnewRootOldRoot : next.leaf ≠ state.root.leaf :=
    (CenterSpoke.ne_iff_leaf_ne.mp hfan.ne).symm
  induction hreach with
  | refl =>
      exact Relation.ReflTransGen.refl
  | @tail source target hprefix hdependency ih =>
      by_cases htargetNewRoot : target = next.leaf
      · subst target
        exact Relation.ReflTransGen.refl
      · have htargetOldRoot : target ≠ state.root.leaf := by
          intro htarget
          subst target
          exact (PartialEdgeAssignment.centerDependency_target_ne_root_of_oneHoleAt
            state.root.endpoints state.oneHole hdependency).elim
        have hsourceOldRoot : source ≠ state.root.leaf :=
          DirectedDominator.ne_target_of_avoidReach hnewRootOldRoot ih
        have hnewDependency :
            (state.rootPivot next hfan).assignment.CenterDependency
              (distinguishedEdgeSet H J) state.center source target := by
          apply (state.centerDependency_rootPivot_iff
            next hfan hnextColor source target).2
          exact Or.inr ⟨htargetOldRoot, htargetNewRoot, hdependency⟩
        exact Relation.ReflTransGen.tail ih
          ⟨hnewDependency, hsourceOldRoot, htargetOldRoot⟩

omit [DecidableRel H.Adj] in
/-- At a global maximum, the missing-source finset for the pivot color loses
the old root and gains the new root, with every other physical source fixed. -/
theorem missingSourceFinset_rootPivot_eq_of_globalMaximal
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {pivotColor : ExtensionPalette D}
    (hnextColor : state.assignment.color next.edge = some pivotColor) :
    (state.rootPivot next hstep).missingSourceFinset pivotColor =
      insert next.leaf
        ((state.missingSourceFinset pivotColor).erase state.root.leaf) := by
  classical
  have hreachEq :=
    state.canonicalReachableFinset_rootPivot_eq_of_globalMaximal
      hmaximal next hstep
  have hnextReach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf next.leaf :=
    Relation.ReflTransGen.single hstep.centerDependency
  ext vertex
  simp only [missingSourceFinset, Finset.mem_filter, Finset.mem_insert,
    Finset.mem_erase]
  rw [hreachEq, state.missingAt_pivotColor_rootPivot_iff
    next hstep hnextColor vertex]
  constructor
  · rintro ⟨hreach, hnew | ⟨hold, hneRoot⟩⟩
    · exact Or.inl hnew
    · exact Or.inr ⟨hneRoot, hreach, hold⟩
  · rintro (hnew | ⟨hneRoot, hreach, hold⟩)
    · refine ⟨?_, Or.inl hnew⟩
      simpa [canonicalReachableFinset, hnew] using hnextReach
    · exact ⟨hreach, Or.inr ⟨hold, hneRoot⟩⟩

omit [DecidableRel H.Adj] in
/-- The pivot-color missing-source cardinality is unchanged at a global
maximum. -/
theorem card_missingSourceFinset_rootPivot_eq_of_globalMaximal
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {pivotColor : ExtensionPalette D}
    (hnextColor : state.assignment.color next.edge = some pivotColor) :
    ((state.rootPivot next hstep).missingSourceFinset pivotColor).card =
      (state.missingSourceFinset pivotColor).card := by
  classical
  rw [state.missingSourceFinset_rootPivot_eq_of_globalMaximal
    hmaximal next hstep hnextColor]
  have hrootMem : state.root.leaf ∈
      state.missingSourceFinset pivotColor := by
    apply (state.mem_missingSourceFinset_iff pivotColor state.root.leaf).2
    rcases hstep with ⟨color, _hnextJ, hcolor, hmissing⟩
    have hcolorEq : color = pivotColor :=
      Option.some.inj (hcolor.symm.trans hnextColor)
    exact ⟨Relation.ReflTransGen.refl, by simpa [hcolorEq] using hmissing⟩
  have hnextNotMem : next.leaf ∉ state.missingSourceFinset pivotColor := by
    intro hnextMem
    have hmissing :=
      ((state.mem_missingSourceFinset_iff pivotColor next.leaf).1
        hnextMem).2
    exact hmissing next.edge next.leaf_incident hnextColor
  rw [Finset.card_insert_of_notMem (by
    intro hmem
    exact hnextNotMem (Finset.mem_of_mem_erase hmem))]
  exact Finset.card_erase_add_one hrootMem

omit [DecidableRel H.Adj] in
/-- The `k = 1` pivot-to-robust step.  If a direct triple column has only the
old root outside its target dominator region, pivoting that column makes all
three updated sources external to the new target.  Hence the pivoted column
is robust against deletion of any two entries. -/
theorem colorColumnEntryRobust_two_rootPivot_of_external_card_eq_one
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {gamma : ExtensionPalette D}
    (hnextColor : state.assignment.color next.edge = some gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3)
    (hone : (state.externalMissingSourceFinset next.leaf gamma).card = 1) :
    (state.rootPivot next hstep).ColorColumnEntryRobust
      state.root.leaf gamma 2 := by
  classical
  let pivot := state.rootPivot next hstep
  let R := state.assignment.CenterDependency
    (distinguishedEdgeSet H J) state.center
  have htarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center next.leaf gamma :=
    ⟨next.edge, next.endpoints, hstep.target_not_mem, hnextColor⟩
  have hrootMissing : state.assignment.MissingAt state.root.leaf gamma :=
    (htarget.centerDependency_iff_missingAt state.root.leaf).1
      hstep.centerDependency
  have hrootNeNext : state.root.leaf ≠ next.leaf :=
    CenterSpoke.ne_iff_leaf_ne.mp hstep.ne
  have hrootSource : state.root.leaf ∈
      state.missingSourceFinset gamma := by
    exact (state.mem_missingSourceFinset_iff gamma state.root.leaf).2
      ⟨Relation.ReflTransGen.refl, hrootMissing⟩
  have hrootOutside : state.root.leaf ∉ state.dominatorRegion next.leaf := by
    exact DirectedDominator.root_not_mem_dominatorRegion
      R state.root.leaf next.leaf
  have hrootExternal : state.root.leaf ∈
      state.externalMissingSourceFinset next.leaf gamma :=
    (state.mem_externalMissingSourceFinset_iff
      next.leaf gamma state.root.leaf).2 ⟨hrootSource, hrootOutside⟩
  have hsourceUpdate :=
    state.missingSourceFinset_rootPivot_eq_of_globalMaximal
      hmaximal next hstep hnextColor
  have hallNewExternal : ∀ vertex ∈ pivot.missingSourceFinset gamma,
      vertex ∈ pivot.externalMissingSourceFinset state.root.leaf gamma := by
    intro vertex hvertexNew
    apply (pivot.mem_externalMissingSourceFinset_iff
      state.root.leaf gamma vertex).2
    refine ⟨hvertexNew, ?_⟩
    by_cases hvertexNext : vertex = next.leaf
    · subst vertex
      exact DirectedDominator.root_not_mem_dominatorRegion
        (pivot.assignment.CenterDependency
          (distinguishedEdgeSet H J) pivot.center)
        pivot.root.leaf state.root.leaf
    · have hupdated : vertex ∈ insert next.leaf
          ((state.missingSourceFinset gamma).erase state.root.leaf) := by
        rw [← hsourceUpdate]
        exact hvertexNew
      have herased : vertex ∈
          (state.missingSourceFinset gamma).erase state.root.leaf := by
        simpa [hvertexNext] using hupdated
      have hvertexOld : vertex ∈ state.missingSourceFinset gamma :=
        Finset.mem_of_mem_erase herased
      have hvertexNeRoot : vertex ≠ state.root.leaf :=
        (Finset.mem_erase.mp herased).1
      have hvertexDom : vertex ∈ state.dominatorRegion next.leaf := by
        by_contra hnotDom
        have hvertexExternal : vertex ∈
            state.externalMissingSourceFinset next.leaf gamma :=
          (state.mem_externalMissingSourceFinset_iff
            next.leaf gamma vertex).2 ⟨hvertexOld, hnotDom⟩
        have heq : vertex = state.root.leaf :=
          (Finset.card_le_one_iff.mp (by omega))
            hvertexExternal hrootExternal
        exact hvertexNeRoot heq
      have hvertexReach : Relation.ReflTransGen R state.root.leaf vertex :=
        ((state.mem_missingSourceFinset_iff gamma vertex).1 hvertexOld).1
      have hfromNext : Relation.ReflTransGen R next.leaf vertex :=
        DirectedDominator.reachable_from_of_mem_dominatorRegion
          hrootNeNext hvertexReach (by
            simpa [dominatorRegion, R] using hvertexDom)
      have havoid := state.avoidReach_rootPivot_from_newRoot
        next hstep hfromNext
      have havoidPivot : DirectedDominator.AvoidReach
          (pivot.assignment.CenterDependency
            (distinguishedEdgeSet H J) pivot.center)
          pivot.root.leaf state.root.leaf vertex := by
        simpa [pivot] using havoid
      intro hdomPivot
      exact hdomPivot.2 (by
        simpa [dominatorRegion] using havoidPivot)
  have hexternalEq :
      pivot.externalMissingSourceFinset state.root.leaf gamma =
        pivot.missingSourceFinset gamma := by
    ext vertex
    constructor
    · intro hvertex
      exact ((pivot.mem_externalMissingSourceFinset_iff
        state.root.leaf gamma vertex).1 hvertex).1
    · exact hallNewExternal vertex
  have hnewTriple : (pivot.missingSourceFinset gamma).card = 3 := by
    calc
      (pivot.missingSourceFinset gamma).card =
          (state.missingSourceFinset gamma).card := by
        simpa [pivot] using
          state.card_missingSourceFinset_rootPivot_eq_of_globalMaximal
            hmaximal next hstep hnextColor
      _ = 3 := htriple
  have hnewExternal :
      (pivot.externalMissingSourceFinset state.root.leaf gamma).card = 3 := by
    rw [hexternalEq, hnewTriple]
  have hpivotRootColor : pivot.assignment.color state.root.edge =
      some gamma := by
    change (state.assignment.moveHole state.root.edge next.edge).color
      state.root.edge = some gamma
    exact (PartialEdgeAssignment.moveHole_color_hole
      state.assignment state.root.edge next.edge).trans hnextColor
  have hpivotTarget : pivot.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) pivot.center state.root.leaf gamma :=
    ⟨state.root.edge, by simpa [pivot] using state.root.endpoints,
      state.rootOutside, hpivotRootColor⟩
  have hpivotRootMissing :
      pivot.assignment.MissingAt pivot.root.leaf gamma := by
    have hmissing := (state.missingAt_pivotColor_rootPivot_iff
      next hstep hnextColor next.leaf).2 (Or.inl rfl)
    simpa [pivot] using hmissing
  exact (pivot.colorColumnEntryRobust_two_iff_three_le
    hpivotTarget hpivotRootMissing).2 (by omega)

end OrientedOneHoleState

end TotalColoring
