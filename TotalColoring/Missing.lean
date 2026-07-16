import TotalColoring.Critical
import TotalColoring.Partial

/-!
# Finite-palette missing colors

This module packages the colors missing at a vertex as a finset relative to an
explicit finite palette.  Its main theorem isolates the graph-theoretic seam
in the critical-edge argument: if a valid one-hole partial coloring cannot be
completed by any palette color while preserving the distinguished-edge
rainbow condition, then the missing-color finsets at the two endpoints of the
hole are disjoint.

The result is deliberately conditional.  It neither supplies a blocked
one-hole coloring nor proves the missing-color cardinality lower bounds needed
by the degree-sum argument.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Palette colors missing at a vertex in a partial edge coloring. -/
noncomputable def missingColorsAt (a : PartialEdgeAssignment G C)
    (palette : Finset C) (v : V) : Finset C := by
  classical
  exact palette.filter (a.MissingAt v)

section MissingColors

@[simp]
theorem mem_missingColorsAt {a : PartialEdgeAssignment G C} {palette : Finset C}
    {v : V} {c : C} :
    c ∈ a.missingColorsAt palette v ↔ c ∈ palette ∧ a.MissingAt v c := by
  classical
  simp [missingColorsAt]

/-- Every missing-color finset is contained in its declared palette. -/
theorem missingColorsAt_subset (a : PartialEdgeAssignment G C) (palette : Finset C)
    (v : V) :
    a.missingColorsAt palette v ⊆ palette := by
  intro c hc
  exact (mem_missingColorsAt.mp hc).1

/-- A vertex has at most as many palette-missing colors as the palette has
colors. -/
theorem card_missingColorsAt_le_palette (a : PartialEdgeAssignment G C)
    (palette : Finset C) (v : V) :
    (a.missingColorsAt palette v).card ≤ palette.card :=
  Finset.card_le_card (missingColorsAt_subset a palette v)

/-- Membership in both endpoint missing-color finsets gives a color missing at
every endpoint of the represented edge.  The equality records which vertices
are the two endpoints and avoids hiding an endpoint-selection convention. -/
theorem missingAtEndpoints_of_mem_missingColorsAt
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {u v : V} {c : C}
    (hends : (e : Sym2 V) = s(u, v))
    (hcu : c ∈ a.missingColorsAt palette u)
    (hcv : c ∈ a.missingColorsAt palette v) :
    a.MissingAtEndpoints e c := by
  have hmu : a.MissingAt u c := (mem_missingColorsAt.mp hcu).2
  have hmv : a.MissingAt v c := (mem_missingColorsAt.mp hcv).2
  intro w hw
  have hw' : w = u ∨ w = v := by
    change w ∈ (e : Sym2 V) at hw
    rw [hends] at hw
    exact Sym2.mem_iff.mp hw
  rcases hw' with rfl | rfl
  · exact hmu
  · exact hmv

section Fill

variable [DecidableEq G.edgeSet]

/-- No color in the declared palette fills the designated edge in a way that
is simultaneously proper, complete, and rainbow on `J`. -/
def NoValidCompleteRainbowFill (a : PartialEdgeAssignment G C)
    (palette : Finset C) (e : G.edgeSet) (J : Set G.edgeSet) : Prop :=
  ∀ c ∈ palette,
    ¬((a.fill e c).Valid ∧ (a.fill e c).Complete ∧
      (a.fill e c).RainbowOn J)

/-- A blocked valid one-hole rainbow partial coloring has disjoint endpoint
missing-color finsets.

This is the graph-theoretic bridge required by the finite-set counting theorem
in `TotalColoring.Critical`.  The proof uses only the already-verified fill
theorem: a color missing at both endpoints would produce the forbidden valid,
complete, rainbow fill. -/
theorem disjoint_missingColorsAt_endpoints_of_no_fill
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {u v : V} {J : Set G.edgeSet}
    (hends : (e : Sym2 V) = s(u, v))
    (hvalid : a.Valid) (hhole : a.OneHoleAt e)
    (hrainbow : a.RainbowOn J) (heJ : e ∉ J)
    (hblocked : a.NoValidCompleteRainbowFill palette e J) :
    Disjoint (a.missingColorsAt palette u) (a.missingColorsAt palette v) := by
  refine Finset.disjoint_left.mpr ?_
  intro c hcu hcv
  have hcpalette : c ∈ palette := (mem_missingColorsAt.mp hcu).1
  have hcend : a.MissingAtEndpoints e c :=
    missingAtEndpoints_of_mem_missingColorsAt hends hcu hcv
  have hfill :=
    fill_valid_complete_rainbowOn_of_oneHoleAt_missingAtEndpoints
      hvalid hhole hcend hrainbow heJ
  exact hblocked c hcpalette hfill

/-- Conditional degree-sum conclusion obtained by feeding the endpoint
disjointness theorem into `Critical.degree_sum_of_disjoint_missing_finsets`.

The palette-size bound and both missing-color lower bounds remain explicit
hypotheses; this theorem does not derive them from degrees. -/
theorem degree_sum_of_no_valid_complete_rainbow_fill
    [DecidableEq C]
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {u v : V} {J : Set G.edgeSet}
    {D degreeU degreeV : ℕ}
    (hends : (e : Sym2 V) = s(u, v))
    (hvalid : a.Valid) (hhole : a.OneHoleAt e)
    (hrainbow : a.RainbowOn J) (heJ : e ∉ J)
    (hblocked : a.NoValidCompleteRainbowFill palette e J)
    (hPalette : palette.card ≤ D + 2)
    (hMissingU : D + 3 - degreeU ≤ (a.missingColorsAt palette u).card)
    (hMissingV : D + 3 - degreeV ≤ (a.missingColorsAt palette v).card) :
    D + 4 ≤ degreeU + degreeV := by
  exact Critical.degree_sum_of_disjoint_missing_finsets
    palette (a.missingColorsAt palette u) (a.missingColorsAt palette v)
    (missingColorsAt_subset a palette u)
    (missingColorsAt_subset a palette v)
    (disjoint_missingColorsAt_endpoints_of_no_fill hends hvalid hhole
      hrainbow heJ hblocked)
    hPalette hMissingU hMissingV

end Fill

end MissingColors

end PartialEdgeAssignment

end TotalColoring
