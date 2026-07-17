import TotalColoring.CriticalDominatorCases
import TotalColoring.CriticalTwoExternalCase

/-!
# Closure of the direct exact-triple dominator cases

For a direct color target `q`, the old root is always an external missing
source: it is reachable, is missing the target color by hypothesis, and is
excluded literally from every dominator region.  Conversely, external
missing sources form a subfinset of all reachable missing sources.  Thus an
exact-triple column has between one and three external sources.

The established `k = 1`, `k = 2`, and `k = 3` exclusions exhaust that finite
range.  The final theorem packages only this direct-column contradiction; it
does not assert existence of a direct exact-triple column.
-/

namespace TotalColoring

universe u

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- The root is an external source for every color which it is missing. -/
theorem root_mem_externalMissingSourceFinset_of_missingAt
    (state : OrientedOneHoleState D H J)
    (target : V) {color : ExtensionPalette D}
    (hrootMissing : state.assignment.MissingAt state.root.leaf color) :
    state.root.leaf ∈ state.externalMissingSourceFinset target color := by
  have hrootSource :
      state.root.leaf ∈ state.missingSourceFinset color :=
    (state.mem_missingSourceFinset_iff color state.root.leaf).2
      ⟨PartialEdgeAssignment.centerReachable_refl state.assignment
        (distinguishedEdgeSet H J) state.center state.root.leaf,
        hrootMissing⟩
  exact (state.mem_externalMissingSourceFinset_iff
    target color state.root.leaf).2
      ⟨hrootSource,
        DirectedDominator.root_not_mem_dominatorRegion
          (state.assignment.CenterDependency
            (distinguishedEdgeSet H J) state.center)
          state.root.leaf target⟩

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- External missing sources are a subfinset of all reachable missing
sources. -/
theorem card_externalMissingSourceFinset_le_card_missingSourceFinset
    (state : OrientedOneHoleState D H J)
    (target : V) (color : ExtensionPalette D) :
    (state.externalMissingSourceFinset target color).card ≤
      (state.missingSourceFinset color).card := by
  apply Finset.card_le_card
  intro source hsource
  exact ((state.mem_externalMissingSourceFinset_iff
    target color source).1 hsource).1

omit [DecidableEq V] [DecidableRel H.Adj] in
/-- In an exact-triple column, root externality and the defining subfinset
bound leave exactly the three positive cardinality cases. -/
theorem externalMissingSourceFinset_card_eq_one_or_two_or_three_of_exactTriple
    (state : OrientedOneHoleState D H J)
    (target : V) {color : ExtensionPalette D}
    (hrootMissing : state.assignment.MissingAt state.root.leaf color)
    (htriple : (state.missingSourceFinset color).card = 3) :
    (state.externalMissingSourceFinset target color).card = 1 ∨
      (state.externalMissingSourceFinset target color).card = 2 ∨
      (state.externalMissingSourceFinset target color).card = 3 := by
  have hrootExternal :=
    state.root_mem_externalMissingSourceFinset_of_missingAt
      target hrootMissing
  have hpositive :
      0 < (state.externalMissingSourceFinset target color).card :=
    Finset.card_pos.mpr ⟨state.root.leaf, hrootExternal⟩
  have hupper :=
    state.card_externalMissingSourceFinset_le_card_missingSourceFinset
      target color
  rw [htriple] at hupper
  omega

end OrientedOneHoleState

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V}
variable {J M : Finset (Sym2 V)} [DecidableRel H.Adj]

/-- A globally reach-card-maximal critical state cannot contain a direct
color target whose color is missing at exactly three reachable vertices.
The contradiction is the exhaustive `k = 1`, `k = 2`, `k = 3` dominator
case split. -/
theorem false_of_direct_exactTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {q : V} {gamma : ExtensionPalette D}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma)
    (hrootMissing : state.assignment.MissingAt state.root.leaf gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3) : False := by
  rcases
      state.externalMissingSourceFinset_card_eq_one_or_two_or_three_of_exactTriple
        q hrootMissing htriple with hone | htwo | hthree
  · exact (h.externalMissingSourceFinset_card_ne_one_of_exactTriple
      hstructure state hmaximal hgammaTarget hrootMissing htriple) hone
  · exact (h.externalMissingSourceFinset_card_ne_two_of_exactTriple
      hstructure state hmaximal hgammaTarget hrootMissing htriple) htwo
  · exact (h.externalMissingSourceFinset_card_ne_three_of_exactTriple
      hstructure state hmaximal hgammaTarget hrootMissing htriple) hthree

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
