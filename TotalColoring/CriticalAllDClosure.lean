import TotalColoring.CriticalDominatorClosure
import TotalColoring.CriticalFrozenMobility
import TotalColoring.MinimalExtraction

/-!
# All-parameter closure of the auxiliary rainbow-coloring theorem

This module assembles the checked critical-state interfaces into the final
contradiction for the auxiliary graph problem.  A hypothetical minimal
noncolorable member supplies a globally reach-card-maximal one-hole state.
The exact reachable-set count supplies a color missing at exactly three
reachable vertices, and global frozen-triple elimination makes its center
carrier non-distinguished.

That carrier is a reachable direct target.  A simple fan path to it is
pivoted only along its nonfinal arcs, so the resulting state is still globally
maximal, the target edge retains its color, the new root misses that color,
and the exact triple is unchanged.  The direct dominator closure then gives
the contradiction by exhausting its one-, two-, and three-external-source
cases.

Finally, finite minimization turns this critical contradiction into a valid
rainbow coloring for every supplied auxiliary-class member.  No bound on `D`
is used.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- No outside-edge-minimal noncolorable auxiliary member exists.  This is
the full critical-state wrapper: global maximum, mobile exact triple,
nonfinal direct-entry pivot, and exhaustive direct-column contradiction. -/
theorem false_of_critical_allD
    (h : IsOutsideEdgeMinimalNoncolorable D H J) : False := by
  classical
  rcases h.member with ⟨x, M, hstructure⟩
  rcases h.exists_globallyReachCardMaximal_orientedOneHoleState with
    ⟨state, hmaximal⟩
  rcases h.exists_eq_three_missing_centerReachable state.root
      state.rootOutside state.valid state.oneHole state.rainbow with
    ⟨gamma, htripleSet⟩
  have hthree : 3 ≤ ({leaf : V |
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf leaf ∧
        state.assignment.MissingAt leaf gamma} : Set V).ncard := by
    omega
  rcases h.exists_mobile_centerCarrier_of_three_missing_of_globalMaximal
      hstructure state hmaximal hthree with
    ⟨gammaEdge, hgammaCenter, hgammaColor, hgammaOutside, _hfour⟩
  rcases Sym2.mem_iff_exists.mp hgammaCenter with ⟨q, hgammaEnds⟩
  let gammaSpoke : CenterSpoke H state.center :=
    {
      leaf := q
      edge := gammaEdge
      endpoints := hgammaEnds
    }
  have hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma :=
    ⟨gammaEdge, hgammaEnds, hgammaOutside, hgammaColor⟩

  let T : Set V := {leaf : V |
    state.assignment.CenterReachable (distinguishedEdgeSet H J)
        state.center state.root.leaf leaf ∧
      state.assignment.MissingAt leaf gamma}
  have hTcard : T.ncard = 3 := by
    simpa [T] using htripleSet
  have hTpositive : 0 < T.ncard := by omega
  rcases (Set.ncard_pos (s := T)).mp hTpositive with
    ⟨source, hsourceT⟩
  have hsourceReach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf source := by
    simpa [T] using hsourceT.1
  have hsourceMissing : state.assignment.MissingAt source gamma := by
    simpa [T] using hsourceT.2
  have hsourceTarget : state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center source q :=
    (hgammaTarget.centerDependency_iff_missingAt source).2 hsourceMissing
  have hqReach : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf q :=
    PartialEdgeAssignment.centerReachable_tail hsourceReach hsourceTarget
  have hqNeRoot : q ≠ state.root.leaf := by
    intro hqRoot
    subst q
    exact PartialEdgeAssignment.centerDependency_target_ne_root_of_oneHoleAt
      state.root.endpoints state.oneHole hsourceTarget

  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      state.root state.rootOutside hqReach with
    ⟨F, hFroot, hFterminal⟩
  have hFtail : F.tail ≠ [] := by
    intro htail
    apply hqNeRoot
    calc
      q = F.terminal.leaf := hFterminal.symm
      _ = F.root.leaf := by
        simp [PartialEdgeAssignment.LinearFanPath.terminal,
          PartialEdgeAssignment.LinearFanPath.spokes, htail]
      _ = state.root.leaf := congrArg CenterSpoke.leaf hFroot
  have hFterminalSpoke : F.terminal = gammaSpoke := by
    apply CenterSpoke.ext
    simpa [gammaSpoke] using hFterminal
  have hFterminalColor :
      state.assignment.color F.terminal.edge = some gamma := by
    rw [hFterminalSpoke]
    exact hgammaColor

  have hstateSourceSet :
      (↑(state.missingSourceFinset gamma) : Set V) = T := by
    ext leaf
    simp [T, OrientedOneHoleState.mem_missingSourceFinset_iff]
  have hstateTriple : (state.missingSourceFinset gamma).card = 3 := by
    calc
      (state.missingSourceFinset gamma).card =
          (↑(state.missingSourceFinset gamma) : Set V).ncard := by simp
      _ = T.ncard := congrArg Set.ncard hstateSourceSet
      _ = 3 := hTcard

  rcases
      state.exists_globallyMaximal_rootPivotReachable_directEntry_to_terminal
        hmaximal F hFroot hFtail hFterminalColor with
    ⟨direct, _hdirectReach, hdirectMaximal, hdirectCenter,
      hdirectColor, hdirectRootMissing, hdirectMissingIff,
      _hdirectDependency, hdirectReachableEq⟩
  have hdirectTarget : direct.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) direct.center F.terminal.leaf gamma := by
    refine ⟨F.terminal.edge, ?_, F.terminal_edge_not_mem, hdirectColor⟩
    simpa [hdirectCenter] using F.terminal.endpoints
  have hdirectReachIff (leaf : V) :
      direct.assignment.CenterReachable (distinguishedEdgeSet H J)
          direct.center direct.root.leaf leaf ↔
        state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf leaf := by
    have hmem : leaf ∈ direct.canonicalReachableFinset ↔
        leaf ∈ state.canonicalReachableFinset := by
      rw [hdirectReachableEq]
    simpa [OrientedOneHoleState.canonicalReachableFinset] using hmem
  have hdirectSources : direct.missingSourceFinset gamma =
      state.missingSourceFinset gamma := by
    ext leaf
    rw [direct.mem_missingSourceFinset_iff gamma leaf,
      state.mem_missingSourceFinset_iff gamma leaf]
    exact and_congr (hdirectReachIff leaf) (hdirectMissingIff leaf)
  have hdirectTriple : (direct.missingSourceFinset gamma).card = 3 := by
    rw [hdirectSources]
    exact hstateTriple

  exact h.false_of_direct_exactTriple hstructure direct hdirectMaximal
    hdirectTarget hdirectRootMissing hdirectTriple

end IsOutsideEdgeMinimalNoncolorable

namespace MinimalExtraction

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Every finite auxiliary-class member has a valid edge coloring from the
`D + 2` extension palette which is rainbow on its distinguished set. -/
theorem hasValidRainbowColoring_of_inAuxiliaryClass
    (D : ℕ) (H : SimpleGraph V) [hAdjH : DecidableRel H.Adj]
    (J : Finset (Sym2 V)) (hmember : InAuxiliaryClass D H J) :
    HasValidRainbowColoring D H J := by
  classical
  by_contra hnoncolorable
  rcases exists_outsideEdgeMinimalNoncolorable D H J hmember
      hnoncolorable with ⟨Hmin, hminimal⟩
  letI : DecidableRel Hmin.Adj := Classical.decRel Hmin.Adj
  exact hminimal.false_of_critical_allD

end MinimalExtraction

end TotalColoring
