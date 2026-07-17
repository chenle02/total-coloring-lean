import TotalColoring.CriticalDominatorPivot
import TotalColoring.CriticalRobustColumn

/-!
# The one- and three-external-source dominator cases

Fix a globally reach-card-maximal critical state and a direct center target
`q` carrying a color `gamma` which is missing at exactly three reachable
vertices.  The exact dominator characterization turns three external sources
into robustness against deletion of two entries, contradicting the robust
exact-triple-column theorem.

If instead there is exactly one external source, the direct target is a legal
root pivot for `gamma`.  The pivot theorem makes the updated column robust.
Literal root-pivot reachability preserves global maximality, and the exact
source-update theorem preserves the triple, so the same robust-column theorem
again gives a contradiction in the pivoted state.

The explicit root-missing hypothesis is needed in both arguments: it is the
root-to-`q` dependency used by the dominator equivalence and the legality
witness for the pivot.  This module does not eliminate the remaining
two-external-source case.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V}
variable {J M : Finset (Sym2 V)} [DecidableRel H.Adj]

/-- A direct exact-triple color column cannot have all three of its reachable
missing sources outside the target's dominator region. -/
theorem externalMissingSourceFinset_card_ne_three_of_exactTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {q : V} {gamma : ExtensionPalette D}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma)
    (hrootMissing : state.assignment.MissingAt state.root.leaf gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3) :
    (state.externalMissingSourceFinset q gamma).card ≠ 3 := by
  intro hthree
  have hrobust : state.ColorColumnEntryRobust q gamma 2 :=
    (state.colorColumnEntryRobust_two_iff_three_le
      hgammaTarget hrootMissing).2 (by omega)
  exact (h.not_colorColumnEntryRobust_two_of_exactTriple hstructure state
    hmaximal hgammaTarget htriple) hrobust

/-- A direct exact-triple color column cannot have exactly one reachable
missing source outside the target's dominator region.  The contradiction is
taken only after constructing and checking the literal pivoted state. -/
theorem externalMissingSourceFinset_card_ne_one_of_exactTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {q : V} {gamma : ExtensionPalette D}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma)
    (hrootMissing : state.assignment.MissingAt state.root.leaf gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3) :
    (state.externalMissingSourceFinset q gamma).card ≠ 1 := by
  classical
  intro hone
  rcases hgammaTarget with
    ⟨gammaEdge, hgammaEnds, hgammaOutside, hgammaColor⟩
  let next : CenterSpoke H state.center :=
    {
      leaf := q
      edge := gammaEdge
      endpoints := hgammaEnds
    }
  have hstep : state.assignment.FanStep
      (distinguishedEdgeSet H J) state.root next :=
    ⟨gamma, hgammaOutside, hgammaColor, hrootMissing⟩
  let pivot := state.rootPivot next hstep

  have hpivotRobust : pivot.ColorColumnEntryRobust
      state.root.leaf gamma 2 := by
    simpa [pivot, next] using
      state.colorColumnEntryRobust_two_rootPivot_of_external_card_eq_one
        hmaximal next hstep hgammaColor htriple hone

  have hpivotStep : state.IsRootPivotStep pivot := by
    exact ⟨next, hstep, rfl⟩
  have hpivotReach : state.IsRootPivotReachable pivot :=
    Relation.ReflTransGen.single hpivotStep
  have hpivotMaximal : pivot.IsGloballyReachCardMaximal :=
    hpivotReach.isGloballyReachCardMaximal hmaximal

  have hpivotTriple : (pivot.missingSourceFinset gamma).card = 3 := by
    calc
      (pivot.missingSourceFinset gamma).card =
          (state.missingSourceFinset gamma).card := by
        simpa [pivot] using
          state.card_missingSourceFinset_rootPivot_eq_of_globalMaximal
            hmaximal next hstep hgammaColor
      _ = 3 := htriple

  have hpivotRootColor :
      pivot.assignment.color state.root.edge = some gamma := by
    change (state.assignment.moveHole state.root.edge next.edge).color
      state.root.edge = some gamma
    exact (PartialEdgeAssignment.moveHole_color_hole
      state.assignment state.root.edge next.edge).trans hgammaColor
  have hpivotTarget : pivot.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) pivot.center state.root.leaf gamma :=
    ⟨state.root.edge, by simpa [pivot] using state.root.endpoints,
      state.rootOutside, hpivotRootColor⟩

  exact (h.not_colorColumnEntryRobust_two_of_exactTriple hstructure pivot
    hpivotMaximal hpivotTarget hpivotTriple) hpivotRobust

/-- The assembled dominator conclusion: under one common direct exact-triple
setup, the external-source cardinality is neither one nor three. -/
theorem externalMissingSourceFinset_card_ne_one_and_ne_three_of_exactTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {q : V} {gamma : ExtensionPalette D}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma)
    (hrootMissing : state.assignment.MissingAt state.root.leaf gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3) :
    (state.externalMissingSourceFinset q gamma).card ≠ 1 ∧
      (state.externalMissingSourceFinset q gamma).card ≠ 3 := by
  exact ⟨h.externalMissingSourceFinset_card_ne_one_of_exactTriple
      hstructure state hmaximal hgammaTarget hrootMissing htriple,
    h.externalMissingSourceFinset_card_ne_three_of_exactTriple
      hstructure state hmaximal hgammaTarget hrootMissing htriple⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
