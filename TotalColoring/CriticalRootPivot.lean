import TotalColoring.CriticalGlobalMaximal

/-!
# Literal root pivots

A fan step from the current root spoke to a colored non-distinguished spoke
supports the primitive `moveHole`: move the donor color to the old hole and
make the donor the new hole.  This module packages that operation as another
oriented one-hole state.

Every vertex reachable from the old root remains reachable from the new root.
The new root first reaches the old root through the moved color.  Along an old
dependency path, a step into the new root can be discarded; every other step
survives.  Indeed, the only old dependency using the donor color entered the
new root itself, while every other dependency color is unaffected by the
two-edge move.

Consequently a globally reach-card-maximal state has exactly the same
canonical reachable finset after every literal root pivot.  This is equality
of physical reachable vertices, not equality of assignments or states.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Moving a donor of color `pivotColor` changes no missing predicate for a
different color. -/
theorem missingAt_moveHole_iff_of_ne_donor_color
    [DecidableEq G.edgeSet]
    {a : PartialEdgeAssignment G C} {hole donor : G.edgeSet}
    (hhole : a.OneHoleAt hole) {pivotColor other : C}
    (hdonorColor : a.color donor = some pivotColor)
    (hother : other ≠ pivotColor) (vertex : V) :
    (a.moveHole hole donor).MissingAt vertex other ↔
      a.MissingAt vertex other := by
  have hholeNone : a.color hole = none := (hhole hole).2 rfl
  constructor
  · intro hnew edge hedge hedgeColor
    by_cases hedgeHole : edge = hole
    · subst edge
      rw [hholeNone] at hedgeColor
      simp at hedgeColor
    · by_cases hedgeDonor : edge = donor
      · subst edge
        have hEq : pivotColor = other :=
          Option.some.inj (hdonorColor.symm.trans hedgeColor)
        exact hother hEq.symm
      · apply hnew edge hedge
        simpa [moveHole_color_of_ne a hedgeHole hedgeDonor] using hedgeColor
  · intro hold edge hedge hedgeColor
    by_cases hedgeHole : edge = hole
    · subst edge
      rw [moveHole_color_hole] at hedgeColor
      have hEq : pivotColor = other :=
        Option.some.inj (hdonorColor.symm.trans hedgeColor)
      exact hother hEq.symm
    · by_cases hedgeDonor : edge = donor
      · subst edge
        have hne : donor ≠ hole := by
          intro hEq
          subst donor
          rw [hholeNone] at hdonorColor
          simp at hdonorColor
        rw [moveHole_color_donor a hne] at hedgeColor
        simp at hedgeColor
      · apply hold edge hedge
        simpa [moveHole_color_of_ne a hedgeHole hedgeDonor] using hedgeColor

/-- After a legal one-step move, the donor leaf misses the moved color. -/
theorem missingAt_donorLeaf_moveHole_of_fanStep
    [DecidableEq G.edgeSet]
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet} {center : V}
    {root next : CenterSpoke G center}
    (hvalid : a.Valid) (hstep : a.FanStep J root next)
    {pivotColor : C} (hnextColor : a.color next.edge = some pivotColor) :
    (a.moveHole root.edge next.edge).MissingAt next.leaf pivotColor := by
  have hspokes : root ≠ next := hstep.ne
  intro edge hedgeIncident hedgeColor
  by_cases hedgeRoot : edge = root.edge
  · subst edge
    exact root.not_incident_leaf_of_ne hspokes hedgeIncident
  · by_cases hedgeNext : edge = next.edge
    · subst edge
      rw [moveHole_color_donor a
        (CenterSpoke.ne_iff_edge_ne.mp hspokes).symm] at hedgeColor
      simp at hedgeColor
    · have holdColor : a.color edge = some pivotColor := by
        simpa [moveHole_color_of_ne a hedgeRoot hedgeNext] using hedgeColor
      have hadj : G.lineGraph.Adj next.edge edge := by
        apply SimpleGraph.lineGraph_adj_iff_exists.mpr
        exact ⟨Ne.symm hedgeNext, next.leaf, next.leaf_incident,
          hedgeIncident⟩
      exact (hvalid next.edge edge pivotColor hadj hnextColor) holdColor

/-- Exact missing-set update for the moved donor color between two distinct
spokes at one center.  The new donor leaf is added as a hole and the old root
leaf is removed; all other old holes of that color are unchanged. -/
theorem missingAt_moveHole_donorColor_iff
    [DecidableEq G.edgeSet]
    {a : PartialEdgeAssignment G C} {center : V}
    {root next : CenterSpoke G center}
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hspokes : root ≠ next) {pivotColor : C}
    (hnextColor : a.color next.edge = some pivotColor) (vertex : V) :
    (a.moveHole root.edge next.edge).MissingAt vertex pivotColor ↔
      vertex = next.leaf ∨
        (a.MissingAt vertex pivotColor ∧ vertex ≠ root.leaf) := by
  have hrootNone : a.color root.edge = none := (hhole root.edge).2 rfl
  constructor
  · intro hnew
    by_cases hvertexNext : vertex = next.leaf
    · exact Or.inl hvertexNext
    · right
      refine ⟨?_, ?_⟩
      · intro edge hedgeIncident hedgeColor
        by_cases hedgeNext : edge = next.edge
        · subst edge
          rcases next.incident_iff.mp hedgeIncident with
            hcenter | hleaf
          · apply hnew root.edge
              (by simpa [hcenter] using root.center_incident)
            simpa using
              (moveHole_color_hole a root.edge next.edge).trans hnextColor
          · exact hvertexNext hleaf
        · by_cases hedgeRoot : edge = root.edge
          · subst edge
            rw [hrootNone] at hedgeColor
            simp at hedgeColor
          · apply hnew edge hedgeIncident
            simpa [moveHole_color_of_ne a hedgeRoot hedgeNext] using hedgeColor
      · intro hvertexRoot
        subst vertex
        apply hnew root.edge root.leaf_incident
        simpa using
          (moveHole_color_hole a root.edge next.edge).trans hnextColor
  · rintro (hvertexNext | ⟨hold, hvertexRoot⟩)
    · subst vertex
      intro edge hedgeIncident hedgeColor
      by_cases hedgeRoot : edge = root.edge
      · subst edge
        exact root.not_incident_leaf_of_ne hspokes hedgeIncident
      · by_cases hedgeNext : edge = next.edge
        · subst edge
          rw [moveHole_color_donor a
            (CenterSpoke.ne_iff_edge_ne.mp hspokes).symm] at hedgeColor
          simp at hedgeColor
        · have holdColor : a.color edge = some pivotColor := by
            simpa [moveHole_color_of_ne a hedgeRoot hedgeNext] using hedgeColor
          have hadj : G.lineGraph.Adj next.edge edge := by
            apply SimpleGraph.lineGraph_adj_iff_exists.mpr
            exact ⟨Ne.symm hedgeNext, next.leaf, next.leaf_incident,
              hedgeIncident⟩
          exact (hvalid next.edge edge pivotColor hadj hnextColor) holdColor
    · intro edge hedgeIncident hedgeColor
      by_cases hedgeRoot : edge = root.edge
      · subst edge
        rcases root.incident_iff.mp hedgeIncident with hcenter | hleaf
        · apply hold next.edge
            (by simpa [hcenter] using next.center_incident)
          exact hnextColor
        · exact hvertexRoot hleaf
      · by_cases hedgeNext : edge = next.edge
        · subst edge
          rw [moveHole_color_donor a
            (CenterSpoke.ne_iff_edge_ne.mp hspokes).symm] at hedgeColor
          simp at hedgeColor
        · apply hold edge hedgeIncident
          simpa [moveHole_color_of_ne a hedgeRoot hedgeNext] using hedgeColor

end PartialEdgeAssignment

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- The literal one-step root pivot along a supplied fan dependency. -/
noncomputable def rootPivot
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next) :
    OrientedOneHoleState D H J := by
  classical
  have hsafe :=
    PartialEdgeAssignment.valid_oneHoleAt_rainbowOn_moveHole_of_fanStep
      state.valid state.oneHole state.rainbow state.rootOutside hstep
  exact {
    assignment := state.assignment.moveHole state.root.edge next.edge
    center := state.center
    root := next
    rootOutside := hstep.target_not_mem
    valid := hsafe.1
    oneHole := hsafe.2.1
    rainbow := hsafe.2.2
  }

omit [Fintype V] [DecidableRel H.Adj] in
@[simp]
theorem rootPivot_assignment
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next) :
    (state.rootPivot next hstep).assignment =
      state.assignment.moveHole state.root.edge next.edge := by
  classical
  rfl

omit [Fintype V] [DecidableRel H.Adj] in
@[simp]
theorem rootPivot_center
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next) :
    (state.rootPivot next hstep).center = state.center := by
  classical
  rfl

omit [Fintype V] [DecidableRel H.Adj] in
@[simp]
theorem rootPivot_root
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next) :
    (state.rootPivot next hstep).root = next := by
  classical
  rfl

omit [Fintype V] [DecidableRel H.Adj] in
/-- Exact missing-set update for the literal pivot color. -/
theorem missingAt_pivotColor_rootPivot_iff
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {pivotColor : ExtensionPalette D}
    (hnextColor : state.assignment.color next.edge = some pivotColor)
    (vertex : V) :
    (state.rootPivot next hstep).assignment.MissingAt vertex pivotColor ↔
      vertex = next.leaf ∨
        (state.assignment.MissingAt vertex pivotColor ∧
          vertex ≠ state.root.leaf) := by
  classical
  simpa [rootPivot] using
    (PartialEdgeAssignment.missingAt_moveHole_donorColor_iff
      state.valid state.oneHole hstep.ne hnextColor vertex)

omit [Fintype V] [DecidableRel H.Adj] in
/-- Every nonpivot missing-color predicate is literally unchanged. -/
theorem missingAt_otherColor_rootPivot_iff
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {pivotColor other : ExtensionPalette D}
    (hnextColor : state.assignment.color next.edge = some pivotColor)
    (hother : other ≠ pivotColor) (vertex : V) :
    (state.rootPivot next hstep).assignment.MissingAt vertex other ↔
      state.assignment.MissingAt vertex other := by
  classical
  simpa [rootPivot] using
    (PartialEdgeAssignment.missingAt_moveHole_iff_of_ne_donor_color
      state.oneHole hnextColor hother vertex)

omit [Fintype V] [DecidableRel H.Adj] in
/-- Exact dependency-column update under a literal root pivot.  The pivot
color target moves from `next.leaf` to the old root leaf, its source set loses
the old root and gains the new root, and every other dependency is unchanged.
-/
theorem centerDependency_rootPivot_iff
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {pivotColor : ExtensionPalette D}
    (hnextColor : state.assignment.color next.edge = some pivotColor)
    (source target : V) :
    (state.rootPivot next hstep).assignment.CenterDependency
        (distinguishedEdgeSet H J) state.center source target ↔
      (target = state.root.leaf ∧
        (source = next.leaf ∨
          (state.assignment.MissingAt source pivotColor ∧
            source ≠ state.root.leaf))) ∨
      (target ≠ state.root.leaf ∧ target ≠ next.leaf ∧
        state.assignment.CenterDependency
          (distinguishedEdgeSet H J) state.center source target) := by
  classical
  let moved := state.assignment.moveHole state.root.edge next.edge
  have hspokes : state.root ≠ next := hstep.ne
  have hedgeNe : next.edge ≠ state.root.edge :=
    (CenterSpoke.ne_iff_edge_ne.mp hspokes).symm
  have hmovedRootColor : moved.color state.root.edge = some pivotColor := by
    simpa [moved] using
      (PartialEdgeAssignment.moveHole_color_hole
        state.assignment state.root.edge next.edge).trans hnextColor
  constructor
  · intro hdependency
    change moved.CenterDependency
      (distinguishedEdgeSet H J) state.center source target at hdependency
    rcases hdependency with
      ⟨edge, color, hedgeEnds, hedgeJ, hedgeColor, hsourceMissing⟩
    by_cases htargetOld : target = state.root.leaf
    · left
      refine ⟨htargetOld, ?_⟩
      subst target
      have hedgeEq : edge = state.root.edge :=
        PartialEdgeAssignment.centerEdge_eq_of_endpoints
          hedgeEnds state.root.endpoints
      subst edge
      have hcolorEq : color = pivotColor :=
        Option.some.inj (hedgeColor.symm.trans hmovedRootColor)
      subst color
      exact (state.missingAt_pivotColor_rootPivot_iff
        next hstep hnextColor source).1 (by
          simpa [rootPivot, moved] using hsourceMissing)
    · right
      have htargetNext : target ≠ next.leaf := by
        intro hEq
        subst target
        have hedgeEq : edge = next.edge :=
          PartialEdgeAssignment.centerEdge_eq_of_endpoints
            hedgeEnds next.endpoints
        subst edge
        rw [show moved.color next.edge = none by
          simpa [moved] using
            PartialEdgeAssignment.moveHole_color_donor
              state.assignment hedgeNe] at hedgeColor
        simp at hedgeColor
      refine ⟨htargetOld, htargetNext, ?_⟩
      have hedgeNeRoot : edge ≠ state.root.edge := by
        intro hEq
        apply htargetOld
        apply Sym2.congr_right.mp
        calc
          s(state.center, target) = (edge : Sym2 V) := hedgeEnds.symm
          _ = (state.root.edge : Sym2 V) := by rw [hEq]
          _ = s(state.center, state.root.leaf) := state.root.endpoints
      have hedgeNeNext : edge ≠ next.edge := by
        intro hEq
        apply htargetNext
        apply Sym2.congr_right.mp
        calc
          s(state.center, target) = (edge : Sym2 V) := hedgeEnds.symm
          _ = (next.edge : Sym2 V) := by rw [hEq]
          _ = s(state.center, next.leaf) := next.endpoints
      have holdColor : state.assignment.color edge = some color := by
        simpa [moved, PartialEdgeAssignment.moveHole_color_of_ne
          state.assignment hedgeNeRoot hedgeNeNext] using hedgeColor
      have hedgeCenter : Incident state.center edge := by
        change state.center ∈ (edge : Sym2 V)
        rw [hedgeEnds]
        exact Sym2.mem_mk_left state.center target
      have hcolorNe : color ≠ pivotColor := by
        intro hEq
        subst color
        have hedgeEq : edge = next.edge :=
          PartialEdgeAssignment.edge_eq_of_incident_of_color_eq
            state.valid hedgeCenter next.center_incident
            holdColor hnextColor
        exact hedgeNeNext hedgeEq
      have holdMissing : state.assignment.MissingAt source color :=
        (state.missingAt_otherColor_rootPivot_iff
          next hstep hnextColor hcolorNe source).1 (by
            simpa [rootPivot, moved] using hsourceMissing)
      exact ⟨edge, color, hedgeEnds, hedgeJ, holdColor, holdMissing⟩
  · rintro (⟨rfl, hsource⟩ | ⟨htargetOld, htargetNext, hdependency⟩)
    · change moved.CenterDependency (distinguishedEdgeSet H J)
        state.center source state.root.leaf
      have hmovedMissing : moved.MissingAt source pivotColor := by
        have hpivotMissing := (state.missingAt_pivotColor_rootPivot_iff
          next hstep hnextColor source).2 hsource
        simpa [rootPivot, moved] using hpivotMissing
      exact ⟨state.root.edge, pivotColor, state.root.endpoints,
        state.rootOutside, hmovedRootColor, hmovedMissing⟩
    · change moved.CenterDependency
        (distinguishedEdgeSet H J) state.center source target
      rcases hdependency with
        ⟨edge, color, hedgeEnds, hedgeJ, hedgeColor, hsourceMissing⟩
      have hedgeNeRoot : edge ≠ state.root.edge := by
        intro hEq
        apply htargetOld
        apply Sym2.congr_right.mp
        calc
          s(state.center, target) = (edge : Sym2 V) := hedgeEnds.symm
          _ = (state.root.edge : Sym2 V) := by rw [hEq]
          _ = s(state.center, state.root.leaf) := state.root.endpoints
      have hedgeNeNext : edge ≠ next.edge := by
        intro hEq
        apply htargetNext
        apply Sym2.congr_right.mp
        calc
          s(state.center, target) = (edge : Sym2 V) := hedgeEnds.symm
          _ = (next.edge : Sym2 V) := by rw [hEq]
          _ = s(state.center, next.leaf) := next.endpoints
      have hedgeCenter : Incident state.center edge := by
        change state.center ∈ (edge : Sym2 V)
        rw [hedgeEnds]
        exact Sym2.mem_mk_left state.center target
      have hcolorNe : color ≠ pivotColor := by
        intro hEq
        subst color
        have hedgeEq : edge = next.edge :=
          PartialEdgeAssignment.edge_eq_of_incident_of_color_eq
            state.valid hedgeCenter next.center_incident
            hedgeColor hnextColor
        exact hedgeNeNext hedgeEq
      have hmovedColor : moved.color edge = some color := by
        simpa [moved, PartialEdgeAssignment.moveHole_color_of_ne
          state.assignment hedgeNeRoot hedgeNeNext] using hedgeColor
      have hmovedMissing : moved.MissingAt source color := by
        have hpivotMissing := (state.missingAt_otherColor_rootPivot_iff
          next hstep hnextColor hcolorNe source).2 hsourceMissing
        simpa [rootPivot, moved] using hpivotMissing
      exact ⟨edge, color, hedgeEnds, hedgeJ,
        hmovedColor, hmovedMissing⟩

omit [Fintype V] [DecidableRel H.Adj] in
/-- Every old reachable vertex remains reachable after a literal root pivot.
The proof retains the old physical path and treats the unique changed color
column explicitly. -/
theorem centerReachable_rootPivot
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next)
    {target : V}
    (hreach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf target) :
    (state.rootPivot next hstep).assignment.CenterReachable
      (distinguishedEdgeSet H J) (state.rootPivot next hstep).center
      (state.rootPivot next hstep).root.leaf target := by
  classical
  rcases hstep with ⟨pivotColor, hnextJ, hnextColor, hrootMissing⟩
  let moved := state.assignment.moveHole state.root.edge next.edge
  have hspokes : state.root ≠ next := by
    apply PartialEdgeAssignment.FanStep.ne
    exact ⟨pivotColor, hnextJ, hnextColor, hrootMissing⟩
  have hnewRootMissing : moved.MissingAt next.leaf pivotColor :=
    PartialEdgeAssignment.missingAt_donorLeaf_moveHole_of_fanStep
      state.valid
      (⟨pivotColor, hnextJ, hnextColor, hrootMissing⟩ :
        state.assignment.FanStep
          (distinguishedEdgeSet H J) state.root next)
      hnextColor
  have hnewToOld : moved.CenterReachable
      (distinguishedEdgeSet H J) state.center next.leaf state.root.leaf := by
    apply Relation.ReflTransGen.single
    exact ⟨state.root.edge, pivotColor, state.root.endpoints,
      state.rootOutside, by
        simpa [moved] using
          (PartialEdgeAssignment.moveHole_color_hole
            state.assignment state.root.edge next.edge).trans hnextColor,
      hnewRootMissing⟩
  have hmovedReach : moved.CenterReachable
      (distinguishedEdgeSet H J) state.center next.leaf target := by
    induction hreach with
    | refl => exact hnewToOld
    | @tail source current hprefix hlast ih =>
        by_cases htargetNew : current = next.leaf
        · subst current
          exact Relation.ReflTransGen.refl
        · rcases hlast with
            ⟨edge, color, hedgeEnds, hedgeJ, hedgeColor, hsourceMissing⟩
          have htargetOld : current ≠ state.root.leaf := by
            intro hEq
            subst current
            exact (PartialEdgeAssignment.centerDependency_target_ne_root_of_oneHoleAt
              state.root.endpoints state.oneHole
              ⟨edge, color, hedgeEnds, hedgeJ, hedgeColor,
                hsourceMissing⟩).elim
          have hedgeCenter : Incident state.center edge := by
            change state.center ∈ (edge : Sym2 V)
            rw [hedgeEnds]
            exact Sym2.mem_mk_left state.center current
          have hcolorNe : color ≠ pivotColor := by
            intro hEq
            subst color
            have hedgeEq : edge = next.edge :=
              PartialEdgeAssignment.edge_eq_of_incident_of_color_eq
                state.valid hedgeCenter next.center_incident
                hedgeColor hnextColor
            apply htargetNew
            apply Sym2.congr_right.mp
            calc
              s(state.center, current) = (edge : Sym2 V) := hedgeEnds.symm
              _ = (next.edge : Sym2 V) := by rw [hedgeEq]
              _ = s(state.center, next.leaf) := next.endpoints
          have hedgeNeRoot : edge ≠ state.root.edge := by
            intro hedgeEq
            apply htargetOld
            apply Sym2.congr_right.mp
            calc
              s(state.center, current) = (edge : Sym2 V) := hedgeEnds.symm
              _ = (state.root.edge : Sym2 V) := by rw [hedgeEq]
              _ = s(state.center, state.root.leaf) := state.root.endpoints
          have hedgeNeNext : edge ≠ next.edge := by
            intro hedgeEq
            apply htargetNew
            apply Sym2.congr_right.mp
            calc
              s(state.center, current) = (edge : Sym2 V) := hedgeEnds.symm
              _ = (next.edge : Sym2 V) := by rw [hedgeEq]
              _ = s(state.center, next.leaf) := next.endpoints
          have hmovedColor : moved.color edge = some color := by
            simpa [moved, PartialEdgeAssignment.moveHole_color_of_ne
              state.assignment hedgeNeRoot hedgeNeNext] using hedgeColor
          have hmovedMissing : moved.MissingAt _ color :=
            (PartialEdgeAssignment.missingAt_moveHole_iff_of_ne_donor_color
              state.oneHole hnextColor hcolorNe _).2 hsourceMissing
          exact Relation.ReflTransGen.tail ih
            ⟨edge, color, hedgeEnds, hedgeJ, hmovedColor, hmovedMissing⟩
  simpa [rootPivot, moved] using hmovedReach

omit [DecidableRel H.Adj] in
/-- The old canonical reachable finset is contained in the pivoted one. -/
theorem canonicalReachableFinset_subset_rootPivot
    (state : OrientedOneHoleState D H J)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next) :
    state.canonicalReachableFinset ⊆
      (state.rootPivot next hstep).canonicalReachableFinset := by
  classical
  intro target htarget
  have hreach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf target := by
    simpa [canonicalReachableFinset] using htarget
  have hpivotReach := state.centerReachable_rootPivot next hstep hreach
  simpa [canonicalReachableFinset] using hpivotReach

omit [DecidableRel H.Adj] in
/-- At a globally reach-card-maximal state, every literal root pivot retains
exactly the same physical canonical reachable finset. -/
theorem canonicalReachableFinset_rootPivot_eq_of_globalMaximal
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    (next : CenterSpoke H state.center)
    (hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next) :
    (state.rootPivot next hstep).canonicalReachableFinset =
      state.canonicalReachableFinset := by
  classical
  have hsubset := state.canonicalReachableFinset_subset_rootPivot next hstep
  have hcard := hmaximal (state.rootPivot next hstep)
  exact (Finset.eq_of_subset_of_card_le hsubset (by
    simpa [canonicalReachCard] using hcard)).symm

end OrientedOneHoleState

end TotalColoring
