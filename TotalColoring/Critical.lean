import Mathlib.Data.Finset.Card

/-!
# Critical-edge counting lemmas

This module isolates the finite-set and natural-number arithmetic used after a
critical-edge argument has proved that the colors missing at the two endpoints
are disjoint.  It does not assert that such disjointness holds for an arbitrary
partial coloring; that remains a separate graph-theoretic obligation.
-/

namespace TotalColoring.Critical

/-- Two disjoint finite subsets of one palette use at most all palette colors. -/
theorem card_add_card_le_palette {C : Type*} [DecidableEq C]
    (palette missingU missingV : Finset C)
    (hU : missingU ⊆ palette) (hV : missingV ⊆ palette)
    (hDisjoint : Disjoint missingU missingV) :
    missingU.card + missingV.card ≤ palette.card := by
  calc
    missingU.card + missingV.card = (missingU ∪ missingV).card :=
      (Finset.card_union_of_disjoint hDisjoint).symm
    _ ≤ palette.card := Finset.card_le_card (Finset.union_subset hU hV)

/-- Arithmetic core of the critical-edge degree-sum argument.

For a palette of size at most `D + 2`, suppose the two endpoint missing-color
counts are bounded below by `D + 3 - degreeU` and
`D + 3 - degreeV`, while their sum is bounded by the palette size.  Then the
endpoint degrees have sum at least `D + 4`.
-/
theorem degree_sum_of_missing_count
    {D degreeU degreeV missingU missingV paletteSize : ℕ}
    (hMissingU : D + 3 - degreeU ≤ missingU)
    (hMissingV : D + 3 - degreeV ≤ missingV)
    (hMissingSum : missingU + missingV ≤ paletteSize)
    (hPalette : paletteSize ≤ D + 2) :
    D + 4 ≤ degreeU + degreeV := by
  omega

/-- Finite-set form of `degree_sum_of_missing_count`.

The graph-theoretic part of a later proof need only supply the two missing
color finsets, their containment in the palette, their disjointness, and the
two endpoint lower bounds.  This theorem then closes the cardinality and
arithmetic part of the argument.
-/
theorem degree_sum_of_disjoint_missing_finsets {C : Type*} [DecidableEq C]
    {D degreeU degreeV : ℕ} (palette missingU missingV : Finset C)
    (hU : missingU ⊆ palette) (hV : missingV ⊆ palette)
    (hDisjoint : Disjoint missingU missingV)
    (hPalette : palette.card ≤ D + 2)
    (hMissingU : D + 3 - degreeU ≤ missingU.card)
    (hMissingV : D + 3 - degreeV ≤ missingV.card) :
    D + 4 ≤ degreeU + degreeV := by
  exact degree_sum_of_missing_count hMissingU hMissingV
    (card_add_card_le_palette palette missingU missingV hU hV hDisjoint) hPalette

end TotalColoring.Critical
