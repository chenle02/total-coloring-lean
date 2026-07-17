import TotalColoring.CriticalDirectEntry
import TotalColoring.Dominator

/-!
# Dominator regions for a critical color column

This module connects the generic directed-dominator API to the canonical
center-dependency relation of an oriented one-hole state.  For a specified
colored center target `q : gamma`, the incoming dependencies from reachable
vertices are exactly the reachable vertices missing `gamma`.  Thus the
finite missing-source column is predecessor-complete for every rooted path,
even though unreachable vertices elsewhere in the graph may also miss the
same color.

The main theorem is the exact robust-entry characterization for that column:
robustness against deletion of at most `budget` incoming sources is equivalent
to having more than `budget` sources outside the target's dominator region.
It is a dependency-digraph theorem only; no Kempe swap is asserted here.
-/

namespace TotalColoring

universe u

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Reachable vertices missing one specified color. -/
noncomputable def missingSourceFinset
    (state : OrientedOneHoleState D H J) (color : ExtensionPalette D) :
    Finset V := by
  classical
  exact state.canonicalReachableFinset.filter fun source =>
    state.assignment.MissingAt source color

omit [DecidableEq V] [DecidableRel H.Adj] in
@[simp]
theorem mem_missingSourceFinset_iff
    (state : OrientedOneHoleState D H J) (color : ExtensionPalette D)
    (source : V) :
    source ∈ state.missingSourceFinset color ↔
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf source ∧
        state.assignment.MissingAt source color := by
  classical
  simp [missingSourceFinset, canonicalReachableFinset,
    PartialEdgeAssignment.centerReachableFinset]

/-- The dominator region of a target in the state's canonical dependency
relation. -/
def dominatorRegion
    (state : OrientedOneHoleState D H J) (target : V) : Set V :=
  DirectedDominator.DominatorRegion
    (state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center)
    state.root.leaf target

/-- The reachable missing sources lying outside the target's dominator
region.  Its cardinality is the `k` parameter of the direct-entry proof. -/
noncomputable def externalMissingSourceFinset
    (state : OrientedOneHoleState D H J) (target : V)
    (color : ExtensionPalette D) : Finset V :=
  DirectedDominator.externalSources
    (state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center)
    state.root.leaf target (state.missingSourceFinset color)

omit [DecidableEq V] [DecidableRel H.Adj] in
@[simp]
theorem mem_externalMissingSourceFinset_iff
    (state : OrientedOneHoleState D H J) (target : V)
    (color : ExtensionPalette D) (source : V) :
    source ∈ state.externalMissingSourceFinset target color ↔
      source ∈ state.missingSourceFinset color ∧
        source ∉ state.dominatorRegion target := by
  classical
  simp [externalMissingSourceFinset, dominatorRegion]

/-- Robustness of one physical color column against deletion of selected
incoming sources. -/
def ColorColumnEntryRobust
    (state : OrientedOneHoleState D H J) (target : V)
    (color : ExtensionPalette D) (budget : ℕ) : Prop :=
  DirectedDominator.EntryRobust
    (state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center)
    state.root.leaf target (state.missingSourceFinset color) budget

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- Every member of the missing-source finset supplies an incoming dependency
to a center target carrying that color. -/
theorem dependency_of_mem_missingSourceFinset
    (state : OrientedOneHoleState D H J)
    {target : V} {color : ExtensionPalette D}
    (htarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center target color)
    {source : V} (hsource : source ∈ state.missingSourceFinset color) :
    state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center source target := by
  exact (htarget.centerDependency_iff_missingAt source).2
    ((state.mem_missingSourceFinset_iff color source).1 hsource).2

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- Conversely, every reachable predecessor of the specified color target
belongs to the reachable missing-source finset. -/
theorem mem_missingSourceFinset_of_reachable_of_dependency
    (state : OrientedOneHoleState D H J)
    {target : V} {color : ExtensionPalette D}
    (htarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center target color)
    {source : V}
    (hreach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf source)
    (hdependency : state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center source target) :
    source ∈ state.missingSourceFinset color := by
  exact (state.mem_missingSourceFinset_iff color source).2
    ⟨hreach, (htarget.centerDependency_iff_missingAt source).1 hdependency⟩

omit [DecidableRel H.Adj] in
/-- Exact robust-entry characterization for a direct color target. -/
theorem colorColumnEntryRobust_iff
    (state : OrientedOneHoleState D H J)
    {target : V} {color : ExtensionPalette D} {budget : ℕ}
    (htarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center target color)
    (hrootMissing : state.assignment.MissingAt state.root.leaf color) :
    state.ColorColumnEntryRobust target color budget ↔
      budget < (state.externalMissingSourceFinset target color).card := by
  let R := state.assignment.CenterDependency
    (distinguishedEdgeSet H J) state.center
  have hrootTarget : R state.root.leaf target :=
    (htarget.centerDependency_iff_missingAt state.root.leaf).2 hrootMissing
  have hrootNe : state.root.leaf ≠ target := by
    intro hEq
    subst target
    exact (state.assignment.centerDependency_irrefl
      (distinguishedEdgeSet H J) state.center state.root.leaf) hrootTarget
  have htargetReach : Relation.ReflTransGen R state.root.leaf target :=
    Relation.ReflTransGen.single hrootTarget
  apply DirectedDominator.entryRobust_iff_lt_card_externalSources
      (R := R) (root := state.root.leaf) (q := target)
      (sources := state.missingSourceFinset color) (budget := budget)
      hrootNe htargetReach
  · intro source hsource
    exact state.dependency_of_mem_missingSourceFinset htarget hsource
  · intro source hreach hdependency
    exact state.mem_missingSourceFinset_of_reachable_of_dependency
      htarget hreach hdependency

omit [DecidableRel H.Adj] in
/-- Three external sources are exactly sufficient for robustness against any
two selected entry deletions. -/
theorem colorColumnEntryRobust_two_iff_three_le
    (state : OrientedOneHoleState D H J)
    {target : V} {color : ExtensionPalette D}
    (htarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center target color)
    (hrootMissing : state.assignment.MissingAt state.root.leaf color) :
    state.ColorColumnEntryRobust target color 2 ↔
      3 ≤ (state.externalMissingSourceFinset target color).card := by
  rw [state.colorColumnEntryRobust_iff htarget hrootMissing]
  omega

end OrientedOneHoleState

end TotalColoring
