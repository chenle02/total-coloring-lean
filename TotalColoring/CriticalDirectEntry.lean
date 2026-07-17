import TotalColoring.CriticalRootPivot
import TotalColoring.FanReachability

/-!
# Iterated root-pivot positioning

A dependency-reachable leaf can be made the literal root leaf by following a
simple linear fan path and pivoting the unique hole one spoke at a time.  This
module records that finite iteration as a reflexive-transitive closure of the
already checked primitive `OrientedOneHoleState.rootPivot`.

The only local seam needed for iteration is that, after moving the hole across
the first step of a simple fan path, every step in the remaining suffix is
still a fan step.  The changed old-root edge cannot meet a later source leaf,
the new hole contributes no color, and simplicity keeps every later target
edge unchanged.

Consequently every old canonical reachable vertex remains reachable after an
iterated pivot.  At a globally reach-card-maximal state the physical canonical
reachable finset is therefore exactly unchanged.  This is a positioning
interface only: it does not assert a dominator, robust-token, crossing, or
detachment lemma.
-/

namespace TotalColoring

universe u

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type*}

namespace LinearFanPath

variable {a : PartialEdgeAssignment G C} {J : Set G.edgeSet} {center : V}

/-- A non-root terminal of a linear fan path belongs to its tail. -/
theorem terminal_mem_tail_of_tail_ne_nil
    (F : LinearFanPath a J center) (htail : F.tail ≠ []) :
    F.terminal ∈ F.tail := by
  cases htailEq : F.tail with
  | nil => exact (htail htailEq).elim
  | cons next rest =>
      simp [LinearFanPath.terminal, LinearFanPath.spokes, htailEq]

/-- A linear fan path with a nonempty tail has distinct root and terminal
spokes. -/
theorem terminal_ne_root_of_tail_ne_nil
    (F : LinearFanPath a J center) (htail : F.tail ≠ []) :
    F.terminal ≠ F.root := by
  intro hterminal
  have hrootNotTail : F.root ∉ F.tail :=
    (List.nodup_cons.mp F.nodup_spokes).1
  apply hrootNotTail
  simpa [hterminal] using F.terminal_mem_tail_of_tail_ne_nil htail

end LinearFanPath

/-- A fan step survives a primitive hole move when the moved old-hole spoke
does not meet the source leaf and neither changed edge is the target edge.
The donor may itself be the source spoke: becoming uncolored cannot destroy a
missing-color assertion at its leaf. -/
theorem FanStep.moveHole_of_spoke_avoidance
    [DecidableEq G.edgeSet]
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet} {center : V}
    {hole donor p q : CenterSpoke G center}
    (hstep : a.FanStep J p q) (hdonorHole : donor ≠ hole)
    (hholeSource : hole ≠ p) (hholeTarget : hole ≠ q)
    (hdonorTarget : donor ≠ q) :
    (a.moveHole hole.edge donor.edge).FanStep J p q := by
  rcases hstep with ⟨color, hqJ, hqColor, hpMissing⟩
  have hdonorEdgeHole : donor.edge ≠ hole.edge :=
    CenterSpoke.ne_iff_edge_ne.mp hdonorHole
  have hqEdgeHole : q.edge ≠ hole.edge :=
    (CenterSpoke.ne_iff_edge_ne.mp hholeTarget).symm
  have hqEdgeDonor : q.edge ≠ donor.edge :=
    (CenterSpoke.ne_iff_edge_ne.mp hdonorTarget).symm
  refine ⟨color, hqJ, ?_, ?_⟩
  · simpa [PartialEdgeAssignment.moveHole_color_of_ne a
      hqEdgeHole hqEdgeDonor] using hqColor
  · intro edge hedgeIncident hedgeColor
    by_cases hedgeHole : edge = hole.edge
    · subst edge
      exact hole.not_incident_leaf_of_ne hholeSource hedgeIncident
    · by_cases hedgeDonor : edge = donor.edge
      · subst edge
        rw [PartialEdgeAssignment.moveHole_color_donor a hdonorEdgeHole]
          at hedgeColor
        simp at hedgeColor
      · apply hpMissing edge hedgeIncident
        simpa [PartialEdgeAssignment.moveHole_color_of_ne a
          hedgeHole hedgeDonor] using hedgeColor

/-- Removing the first spoke of a simple fan path after pivoting across its
first step leaves a fan path chain for the moved assignment. -/
private theorem fanTail_chain_moveHole
    [DecidableEq G.edgeSet]
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet} {center : V}
    {root next : CenterSpoke G center}
    {rest : List (CenterSpoke G center)}
    (hchain : (root :: next :: rest).IsChain (a.FanStep J))
    (hnodup : (root :: next :: rest).Nodup) :
    (next :: rest).IsChain
      ((a.moveHole root.edge next.edge).FanStep J) := by
  have hparts : a.FanStep J root next ∧
      (next :: rest).IsChain (a.FanStep J) := by
    simpa [List.isChain_cons] using hchain
  have hrootNotTail : root ∉ next :: rest :=
    (List.nodup_cons.mp hnodup).1
  have htailNodup : (next :: rest).Nodup :=
    (List.nodup_cons.mp hnodup).2
  have hnextNotRest : next ∉ rest :=
    (List.nodup_cons.mp htailNodup).1
  apply hparts.2.imp_of_mem_tail_imp
  intro p q hp hq hstep
  simp only [List.tail_cons] at hq
  apply hstep.moveHole_of_spoke_avoidance hparts.1.ne.symm
  · intro hrootP
    apply hrootNotTail
    simpa [hrootP] using hp
  · intro hrootQ
    apply hrootNotTail
    simpa [hrootQ] using (List.mem_cons.mpr (Or.inr hq))
  · intro hnextQ
    apply hnextNotRest
    simpa [hnextQ] using hq

end PartialEdgeAssignment

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- One literal root-pivot step between oriented one-hole states. -/
def IsRootPivotStep (state other : OrientedOneHoleState D H J) : Prop :=
  ∃ (next : CenterSpoke H state.center)
      (hstep : state.assignment.FanStep
        (distinguishedEdgeSet H J) state.root next),
    other = state.rootPivot next hstep

/-- Zero or more literal root-pivot steps. -/
def IsRootPivotReachable (state other : OrientedOneHoleState D H J) : Prop :=
  Relation.ReflTransGen IsRootPivotStep state other

omit [Fintype V] [DecidableRel H.Adj] in
/-- One root-pivot step preserves the fan center literally. -/
theorem IsRootPivotStep.center_eq
    {state other : OrientedOneHoleState D H J}
    (hstep : IsRootPivotStep state other) :
    other.center = state.center := by
  rcases hstep with ⟨next, hfan, rfl⟩
  exact rootPivot_center state next hfan

omit [Fintype V] [DecidableRel H.Adj] in
/-- Every finite root-pivot iteration preserves the fan center. -/
theorem IsRootPivotReachable.center_eq
    {state other : OrientedOneHoleState D H J}
    (hreach : IsRootPivotReachable state other) :
    other.center = state.center := by
  induction hreach with
  | refl => rfl
  | tail hprefix hstep ih =>
      exact hstep.center_eq.trans ih

omit [DecidableRel H.Adj] in
/-- One root-pivot step contains the old canonical reachable finset in the
new one. -/
theorem IsRootPivotStep.canonicalReachableFinset_subset
    {state other : OrientedOneHoleState D H J}
    (hstep : IsRootPivotStep state other) :
    state.canonicalReachableFinset ⊆ other.canonicalReachableFinset := by
  rcases hstep with ⟨next, hfan, rfl⟩
  exact state.canonicalReachableFinset_subset_rootPivot next hfan

omit [DecidableRel H.Adj] in
/-- Canonical reachability is monotone along every finite root-pivot
iteration. -/
theorem IsRootPivotReachable.canonicalReachableFinset_subset
    {state other : OrientedOneHoleState D H J}
    (hreach : IsRootPivotReachable state other) :
    state.canonicalReachableFinset ⊆ other.canonicalReachableFinset := by
  induction hreach with
  | refl => exact Set.Subset.rfl
  | tail hprefix hstep ih =>
      exact ih.trans hstep.canonicalReachableFinset_subset

omit [DecidableRel H.Adj] in
/-- At a global maximum, every finite root-pivot iteration preserves the
physical canonical reachable finset exactly. -/
theorem IsRootPivotReachable.canonicalReachableFinset_eq_of_globalMaximal
    {state other : OrientedOneHoleState D H J}
    (hreach : IsRootPivotReachable state other)
    (hmaximal : state.IsGloballyReachCardMaximal) :
    other.canonicalReachableFinset = state.canonicalReachableFinset := by
  classical
  have hsubset := hreach.canonicalReachableFinset_subset
  have hcard := hmaximal other
  exact (Finset.eq_of_subset_of_card_le hsubset (by
    simpa [canonicalReachCard] using hcard)).symm

omit [DecidableRel H.Adj] in
/-- Global reach-card maximality is inherited by every state obtained through
finite literal root pivots from a globally maximal state. -/
theorem IsRootPivotReachable.isGloballyReachCardMaximal
    {state other : OrientedOneHoleState D H J}
    (hreach : IsRootPivotReachable state other)
    (hmaximal : state.IsGloballyReachCardMaximal) :
    other.IsGloballyReachCardMaximal := by
  classical
  have heq := hreach.canonicalReachableFinset_eq_of_globalMaximal hmaximal
  intro candidate
  have hle := hmaximal candidate
  simpa [canonicalReachCard, heq] using hle

omit [Fintype V] [DecidableRel H.Adj] in
/-- Follow a supplied simple linear fan path by finitely many literal root
pivots.  The final root is the original path terminal. -/
theorem exists_rootPivotReachable_root_eq_terminal
    (state : OrientedOneHoleState D H J)
    (F : PartialEdgeAssignment.LinearFanPath state.assignment
      (distinguishedEdgeSet H J) state.center)
    (hroot : F.root = state.root) :
    ∃ other : OrientedOneHoleState D H J,
      IsRootPivotReachable state other ∧
        other.root.leaf = F.terminal.leaf := by
  classical
  cases htail : F.tail with
  | nil =>
      refine ⟨state, Relation.ReflTransGen.refl, ?_⟩
      simpa [PartialEdgeAssignment.LinearFanPath.terminal,
        PartialEdgeAssignment.LinearFanPath.spokes, htail] using
        congrArg CenterSpoke.leaf hroot.symm
  | cons next rest =>
      have hchain : (F.root :: next :: rest).IsChain
          (state.assignment.FanStep (distinguishedEdgeSet H J)) := by
        simpa [htail] using F.chain
      have hnodup : (F.root :: next :: rest).Nodup := by
        simpa [htail] using F.nodup_spokes
      have hfirst : state.assignment.FanStep
          (distinguishedEdgeSet H J) F.root next := by
        exact (List.isChain_cons_cons.mp hchain).1
      have hfan : state.assignment.FanStep
          (distinguishedEdgeSet H J) state.root next := by
        simpa [hroot] using hfirst
      let stateOne := state.rootPivot next hfan
      have hmovedChain : (next :: rest).IsChain
          ((state.assignment.moveHole state.root.edge next.edge).FanStep
            (distinguishedEdgeSet H J)) := by
        apply PartialEdgeAssignment.fanTail_chain_moveHole
            (root := state.root)
        · simpa [hroot] using hchain
        · simpa [hroot] using hnodup
      have hnextNotJ : next.edge ∉ distinguishedEdgeSet H J :=
        hfan.target_not_mem
      have htailNodup : (next :: rest).Nodup :=
        (List.nodup_cons.mp (by simpa [hroot] using hnodup)).2
      let FOneRaw : PartialEdgeAssignment.LinearFanPath
          (state.assignment.moveHole state.root.edge next.edge)
          (distinguishedEdgeSet H J) state.center :=
        { root := next
          tail := rest
          root_not_mem := hnextNotJ
          chain := hmovedChain
          nodup_spokes := htailNodup }
      let FOne : PartialEdgeAssignment.LinearFanPath stateOne.assignment
          (distinguishedEdgeSet H J) stateOne.center := by
        change PartialEdgeAssignment.LinearFanPath
          (state.assignment.moveHole state.root.edge next.edge)
          (distinguishedEdgeSet H J) state.center
        exact FOneRaw
      rcases exists_rootPivotReachable_root_eq_terminal stateOne FOne rfl with
        ⟨other, hotherReach, hotherRoot⟩
      have honeStep : IsRootPivotStep state stateOne := by
        exact ⟨next, hfan, rfl⟩
      refine ⟨other,
        (Relation.ReflTransGen.single honeStep).trans hotherReach, ?_⟩
      have hFOneRoot : FOne.root = next := rfl
      have hFOneTail : FOne.tail = rest := rfl
      have hterm : FOne.terminal.leaf = F.terminal.leaf := by
        let last : CenterSpoke H state.center :=
          (next :: rest).getLast (by simp)
        have hFOneTerminal : FOne.terminal = last := by
          unfold PartialEdgeAssignment.LinearFanPath.terminal
          apply List.getLast_congr FOne.spokes_ne_nil (by simp)
          change next :: rest = next :: rest
          rfl
        have hFTerminal : F.terminal = last := by
          calc
            F.terminal = (F.root :: next :: rest).getLast (by simp) := by
              unfold PartialEdgeAssignment.LinearFanPath.terminal
              apply List.getLast_congr F.spokes_ne_nil (by simp)
              simp [PartialEdgeAssignment.LinearFanPath.spokes, htail]
            _ = last := by simp [last]
        exact congrArg CenterSpoke.leaf
          (hFOneTerminal.trans hFTerminal.symm)
      exact hotherRoot.trans hterm
termination_by F.tail.length
decreasing_by
  change rest.length < F.tail.length
  simp [htail]

omit [Fintype V] [DecidableRel H.Adj] in
/-- Pivot only along the nonfinal arcs of a nontrivial linear fan path.  The
old terminal spoke is never used as a donor: its literal color is retained,
the final fan step survives, and hence the new root leaf has a direct center
dependency into the old terminal leaf.

The explicit missing-color conclusion is the source-side content of that
direct dependency for the supplied terminal color. -/
theorem exists_rootPivotReachable_directEntry_to_terminal
    (state : OrientedOneHoleState D H J)
    (F : PartialEdgeAssignment.LinearFanPath state.assignment
      (distinguishedEdgeSet H J) state.center)
    (hroot : F.root = state.root) (htail : F.tail ≠ [])
    {gamma : ExtensionPalette D}
    (hgamma : state.assignment.color F.terminal.edge = some gamma) :
    ∃ other : OrientedOneHoleState D H J,
      IsRootPivotReachable state other ∧ other.center = state.center ∧
        other.assignment.color F.terminal.edge = some gamma ∧
        other.assignment.MissingAt other.root.leaf gamma ∧
        (∀ vertex, other.assignment.MissingAt vertex gamma ↔
          state.assignment.MissingAt vertex gamma) ∧
        other.assignment.CenterDependency (distinguishedEdgeSet H J)
          other.center other.root.leaf F.terminal.leaf := by
  classical
  cases htailEq : F.tail with
  | nil => exact (htail htailEq).elim
  | cons next rest =>
      cases rest with
      | nil =>
          have hfanRoot : state.assignment.FanStep
              (distinguishedEdgeSet H J) F.root next := by
            simpa [htailEq] using F.chain
          have hfan : state.assignment.FanStep
              (distinguishedEdgeSet H J) state.root next := by
            simpa [hroot] using hfanRoot
          have hterminal : F.terminal = next := by
            simp [PartialEdgeAssignment.LinearFanPath.terminal,
              PartialEdgeAssignment.LinearFanPath.spokes, htailEq]
          rcases hfan with
            ⟨color, hnextJ, hnextColor, hrootMissing⟩
          have hgammaNext : state.assignment.color next.edge =
              some gamma := by
            simpa [hterminal] using hgamma
          have hcolorEq : color = gamma :=
            Option.some.inj (hnextColor.symm.trans hgammaNext)
          subst color
          refine ⟨state, Relation.ReflTransGen.refl, rfl, hgamma,
            hrootMissing, fun _ => Iff.rfl, ?_⟩
          exact ⟨F.terminal.edge, gamma, F.terminal.endpoints,
            F.terminal_edge_not_mem, hgamma, hrootMissing⟩
      | cons after more =>
          have hchain : (F.root :: next :: after :: more).IsChain
              (state.assignment.FanStep (distinguishedEdgeSet H J)) := by
            simpa [htailEq] using F.chain
          have hnodup : (F.root :: next :: after :: more).Nodup := by
            simpa [htailEq] using F.nodup_spokes
          have hfirst : state.assignment.FanStep
              (distinguishedEdgeSet H J) F.root next := by
            exact (List.isChain_cons_cons.mp hchain).1
          have hfan : state.assignment.FanStep
              (distinguishedEdgeSet H J) state.root next := by
            simpa [hroot] using hfirst
          let stateOne := state.rootPivot next hfan
          have hmovedChain : (next :: after :: more).IsChain
              ((state.assignment.moveHole state.root.edge next.edge).FanStep
                (distinguishedEdgeSet H J)) := by
            apply PartialEdgeAssignment.fanTail_chain_moveHole
                (root := state.root)
            · simpa [hroot] using hchain
            · simpa [hroot] using hnodup
          have hnextNotJ : next.edge ∉ distinguishedEdgeSet H J :=
            hfan.target_not_mem
          have htailNodup : (next :: after :: more).Nodup :=
            (List.nodup_cons.mp (by simpa [hroot] using hnodup)).2
          let FOneRaw : PartialEdgeAssignment.LinearFanPath
              (state.assignment.moveHole state.root.edge next.edge)
              (distinguishedEdgeSet H J) state.center :=
            { root := next
              tail := after :: more
              root_not_mem := hnextNotJ
              chain := hmovedChain
              nodup_spokes := htailNodup }
          let FOne : PartialEdgeAssignment.LinearFanPath stateOne.assignment
              (distinguishedEdgeSet H J) stateOne.center := by
            change PartialEdgeAssignment.LinearFanPath
              (state.assignment.moveHole state.root.edge next.edge)
              (distinguishedEdgeSet H J) state.center
            exact FOneRaw
          have hFOneRoot : FOne.root = next := rfl
          have hFOneTail : FOne.tail = after :: more := rfl
          have hterminal : FOne.terminal = F.terminal := by
            let last : CenterSpoke H state.center :=
              (next :: after :: more).getLast (by simp)
            have hFOneTerminal : FOne.terminal = last := by
              unfold PartialEdgeAssignment.LinearFanPath.terminal
              apply List.getLast_congr FOne.spokes_ne_nil (by simp)
              change next :: after :: more = next :: after :: more
              rfl
            have hFTerminal : F.terminal = last := by
              calc
                F.terminal =
                    (F.root :: next :: after :: more).getLast
                      (by simp) := by
                  unfold PartialEdgeAssignment.LinearFanPath.terminal
                  apply List.getLast_congr F.spokes_ne_nil (by simp)
                  simp [PartialEdgeAssignment.LinearFanPath.spokes,
                    htailEq]
                _ = last := by simp [last]
            exact hFOneTerminal.trans hFTerminal.symm
          have hterminalNeRoot : F.terminal ≠ state.root := by
            have hne := F.terminal_ne_root_of_tail_ne_nil htail
            simpa [hroot] using hne
          have hterminalNeNext : F.terminal ≠ next := by
            intro hEq
            apply FOne.terminal_ne_root_of_tail_ne_nil (by
              simp [hFOneTail])
            exact hterminal.trans (hEq.trans hFOneRoot.symm)
          have hterminalEdgeNeRoot :
              F.terminal.edge ≠ state.root.edge :=
            CenterSpoke.ne_iff_edge_ne.mp hterminalNeRoot
          have hterminalEdgeNeNext : F.terminal.edge ≠ next.edge :=
            CenterSpoke.ne_iff_edge_ne.mp hterminalNeNext
          have hgammaMoved :
              (state.assignment.moveHole state.root.edge next.edge).color
                F.terminal.edge = some gamma := by
            simpa [PartialEdgeAssignment.moveHole_color_of_ne
              state.assignment hterminalEdgeNeRoot hterminalEdgeNeNext]
              using hgamma
          have hgammaOne : stateOne.assignment.color
              FOne.terminal.edge = some gamma := by
            change (state.assignment.moveHole state.root.edge next.edge).color
              FOne.terminal.edge = some gamma
            rw [hterminal]
            exact hgammaMoved
          have hmissingOne : ∀ vertex,
              stateOne.assignment.MissingAt vertex gamma ↔
                state.assignment.MissingAt vertex gamma := by
            rcases hfan with
              ⟨pivotColor, hnextJ, hnextColor, hrootMissing⟩
            let hfanData : state.assignment.FanStep
                (distinguishedEdgeSet H J) state.root next :=
              ⟨pivotColor, hnextJ, hnextColor, hrootMissing⟩
            have hgammaPivot : gamma ≠ pivotColor := by
              intro hEq
              subst pivotColor
              have hadj : H.lineGraph.Adj next.edge F.terminal.edge :=
                CenterSpoke.lineGraph_adj hterminalNeNext.symm
              exact (state.valid next.edge F.terminal.edge gamma hadj
                hnextColor) hgamma
            intro vertex
            exact state.missingAt_otherColor_rootPivot_iff
              next hfanData hnextColor hgammaPivot vertex
          rcases exists_rootPivotReachable_directEntry_to_terminal
              stateOne FOne rfl (by simp [hFOneTail]) hgammaOne with
            ⟨other, hotherReach, hotherCenter, hotherColor,
              hotherMissing, hotherMissingIff, hotherDependency⟩
          have honeStep : IsRootPivotStep state stateOne := by
            exact ⟨next, hfan, rfl⟩
          have hreach : IsRootPivotReachable state other :=
            (Relation.ReflTransGen.single honeStep).trans hotherReach
          have hcenter : other.center = state.center := by
            simpa [stateOne] using hotherCenter
          have hcolor : other.assignment.color F.terminal.edge =
              some gamma := by
            simpa [hterminal] using hotherColor
          have hdependency : other.assignment.CenterDependency
              (distinguishedEdgeSet H J) other.center other.root.leaf
                F.terminal.leaf := by
            simpa [hterminal] using hotherDependency
          have hmissingIff : ∀ vertex,
              other.assignment.MissingAt vertex gamma ↔
                state.assignment.MissingAt vertex gamma := by
            intro vertex
            exact (hotherMissingIff vertex).trans (hmissingOne vertex)
          exact ⟨other, hreach, hcenter, hcolor, hotherMissing, hmissingIff,
            hdependency⟩
termination_by F.tail.length
decreasing_by
  change (after :: more).length < F.tail.length
  simp [htailEq]

omit [DecidableRel H.Adj] in
/-- The nonfinal direct-entry positioning from a global maximum remains a
global maximum and retains the same physical canonical reachable finset. -/
theorem exists_globallyMaximal_rootPivotReachable_directEntry_to_terminal
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    (F : PartialEdgeAssignment.LinearFanPath state.assignment
      (distinguishedEdgeSet H J) state.center)
    (hroot : F.root = state.root) (htail : F.tail ≠ [])
    {gamma : ExtensionPalette D}
    (hgamma : state.assignment.color F.terminal.edge = some gamma) :
    ∃ other : OrientedOneHoleState D H J,
      IsRootPivotReachable state other ∧
        other.IsGloballyReachCardMaximal ∧ other.center = state.center ∧
        other.assignment.color F.terminal.edge = some gamma ∧
        other.assignment.MissingAt other.root.leaf gamma ∧
        (∀ vertex, other.assignment.MissingAt vertex gamma ↔
          state.assignment.MissingAt vertex gamma) ∧
        other.assignment.CenterDependency (distinguishedEdgeSet H J)
          other.center other.root.leaf F.terminal.leaf ∧
        other.canonicalReachableFinset = state.canonicalReachableFinset := by
  classical
  rcases state.exists_rootPivotReachable_directEntry_to_terminal
      F hroot htail hgamma with
    ⟨other, hreach, hcenter, hcolor, hmissing, hmissingIff,
      hdependency⟩
  have hotherMaximal := hreach.isGloballyReachCardMaximal hmaximal
  have hreacheq :=
    hreach.canonicalReachableFinset_eq_of_globalMaximal hmaximal
  exact ⟨other, hreach, hotherMaximal, hcenter, hcolor, hmissing,
    hmissingIff,
    hdependency, hreacheq⟩

omit [Fintype V] [DecidableRel H.Adj] in
/-- Every dependency-reachable target leaf admits a finite literal root-pivot
positioning whose new root leaf is exactly that target. -/
theorem exists_rootPivotReachable_root_leaf_eq_of_centerReachable
    (state : OrientedOneHoleState D H J) {target : V}
    (hreach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf target) :
    ∃ other : OrientedOneHoleState D H J,
      IsRootPivotReachable state other ∧ other.center = state.center ∧
        other.root.leaf = target := by
  classical
  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      state.root state.rootOutside hreach with ⟨F, hFroot, hFterminal⟩
  rcases state.exists_rootPivotReachable_root_eq_terminal F hFroot with
    ⟨other, hotherReach, hotherRoot⟩
  exact ⟨other, hotherReach, hotherReach.center_eq,
    hotherRoot.trans hFterminal⟩

omit [DecidableRel H.Adj] in
/-- At global reach-card maximality, dependency-reachable root positioning
keeps the physical canonical reachable finset exactly unchanged. -/
theorem exists_rootPivotReachable_root_leaf_eq_and_reachable_eq_of_globalMaximal
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal) {target : V}
    (hreach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf target) :
    ∃ other : OrientedOneHoleState D H J,
      IsRootPivotReachable state other ∧ other.center = state.center ∧
        other.root.leaf = target ∧
        other.canonicalReachableFinset = state.canonicalReachableFinset := by
  classical
  rcases state.exists_rootPivotReachable_root_leaf_eq_of_centerReachable hreach
      with ⟨other, hotherReach, hcenter, hroot⟩
  have heq :=
    hotherReach.canonicalReachableFinset_eq_of_globalMaximal hmaximal
  exact ⟨other, hotherReach, hcenter, hroot, heq⟩

end OrientedOneHoleState

end TotalColoring
