import TotalColoring.Missing

/-!
# Missing-color counts at a one-hole endpoint

This module derives the missing-color lower bound that was left explicit in
`TotalColoring.Missing`.  If the unique uncolored edge is incident with a
vertex, every palette color which is not missing there is realized on another
incident edge.  Choosing one realizing edge for each such color, and sending
one additional point to the hole, injects these objects into the incident
edges.  Consequently

`palette.card + 1 ≤ (a.missingColorsAt palette v).card + G.degree v`.

The final theorem combines the two endpoint bounds with the blocked-fill
theorem from `TotalColoring.Missing`; it no longer assumes missing-color lower
bounds as separate hypotheses.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Edges of `G` incident with `v`, expressed using the edge subtype expected
by a partial edge assignment, are equivalent to mathlib's incidence set. -/
private def incidentEdgeEquivIncidenceSet (v : V) :
    {e : G.edgeSet // Incident v e} ≃ G.incidenceSet v where
  toFun e := ⟨e.1.1, e.1.2, e.2⟩
  invFun e := ⟨⟨e.1, e.2.1⟩, e.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

section Finite

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [DecidableEq C]

/-- The cardinality of the incident-edge subtype is the graph-theoretic
degree. -/
private theorem card_incidentEdges_eq_degree (v : V) :
    Fintype.card {e : G.edgeSet // Incident v e} = G.degree v := by
  calc
    Fintype.card {e : G.edgeSet // Incident v e} =
        Fintype.card (G.incidenceSet v) :=
      Fintype.card_congr (incidentEdgeEquivIncidenceSet (G := G) v)
    _ = G.degree v := G.card_incidenceSet_eq_degree v

/-- Colors in `palette` which are not missing at `v`, together with one extra
point representing the hole, inject into the edges incident with `v`.

The argument only needs the one-hole property; properness is not needed for
this stronger intermediate statement because one edge cannot realize two
different actual colors. -/
theorem card_not_missing_add_one_le_degree_of_oneHoleAt
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {v : V}
    (hhole : a.OneHoleAt e) (hinc : Incident v e) :
    (palette \ a.missingColorsAt palette v).card + 1 ≤ G.degree v := by
  classical
  let present := palette \ a.missingColorsAt palette v
  have hRealized (c : C) (hc : c ∈ present) :
      ∃ f : G.edgeSet, Incident v f ∧ a.color f = some c := by
    have hparts := Finset.mem_sdiff.mp hc
    have hnotmissing : ¬a.MissingAt v c := by
      intro hmissing
      exact hparts.2 (mem_missingColorsAt.mpr ⟨hparts.1, hmissing⟩)
    rw [MissingAt] at hnotmissing
    push Not at hnotmissing
    exact hnotmissing
  let witness : {c : C // c ∈ present} → G.edgeSet := fun c ↦
    Classical.choose (hRealized c.1 c.2)
  have hwitness (c : {c : C // c ∈ present}) :
      Incident v (witness c) ∧ a.color (witness c) = some c.1 :=
    Classical.choose_spec (hRealized c.1 c.2)
  let embed : Sum {c : C // c ∈ present} Unit →
      {f : G.edgeSet // Incident v f}
    | Sum.inl c => ⟨witness c, (hwitness c).1⟩
    | Sum.inr _ => ⟨e, hinc⟩
  have hinjective : Function.Injective embed := by
    rintro (c | x) (d | y) hxy
    · apply congrArg Sum.inl
      apply Subtype.ext
      apply Option.some.inj
      have hedge : witness c = witness d := congrArg Subtype.val hxy
      calc
        some c.1 = a.color (witness c) := (hwitness c).2.symm
        _ = a.color (witness d) := congrArg a.color hedge
        _ = some d.1 := (hwitness d).2
    · have hedge : witness c = e := congrArg Subtype.val hxy
      have hsome : a.color e = some c.1 := by simpa [hedge] using (hwitness c).2
      have hnone : a.color e = none := (hhole e).2 rfl
      simp [hnone] at hsome
    · have hedge : e = witness d := congrArg Subtype.val hxy
      have hsome : a.color e = some d.1 := by simpa [← hedge] using (hwitness d).2
      have hnone : a.color e = none := (hhole e).2 rfl
      simp [hnone] at hsome
    · cases x
      cases y
      rfl
  change present.card + 1 ≤ G.degree v
  calc
    present.card + 1 = Fintype.card (Sum {c : C // c ∈ present} Unit) := by simp
    _ ≤ Fintype.card {f : G.edgeSet // Incident v f} :=
      Fintype.card_le_of_injective embed hinjective
    _ = G.degree v := card_incidentEdges_eq_degree (G := G) v

/-- At an endpoint of the unique hole, the palette size plus one is bounded
by the number of missing palette colors plus the degree. -/
theorem palette_card_add_one_le_missingColorsAt_card_add_degree
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {v : V}
    (hhole : a.OneHoleAt e) (hinc : Incident v e) :
    palette.card + 1 ≤ (a.missingColorsAt palette v).card + G.degree v := by
  classical
  have hpresent := card_not_missing_add_one_le_degree_of_oneHoleAt
    (a := a) (palette := palette) hhole hinc
  have hpartition :
      (palette \ a.missingColorsAt palette v).card +
          (a.missingColorsAt palette v).card = palette.card :=
    Finset.card_sdiff_add_card_eq_card (missingColorsAt_subset a palette v)
  omega

/-- Subtractive form of
`palette_card_add_one_le_missingColorsAt_card_add_degree`. -/
theorem palette_card_add_one_sub_degree_le_missingColorsAt_card
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {v : V}
    (hhole : a.OneHoleAt e) (hinc : Incident v e) :
    palette.card + 1 - G.degree v ≤
      (a.missingColorsAt palette v).card := by
  have hcount := palette_card_add_one_le_missingColorsAt_card_add_degree
    (a := a) (palette := palette) hhole hinc
  omega

/-- For a palette of exactly `D + 2` colors, an endpoint of the unique hole
misses at least `D + 3 - degree` palette colors. -/
theorem D_add_three_sub_degree_le_missingColorsAt_card
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {v : V} {D : ℕ}
    (hhole : a.OneHoleAt e) (hinc : Incident v e)
    (hPalette : palette.card = D + 2) :
    D + 3 - G.degree v ≤ (a.missingColorsAt palette v).card := by
  have hcount := palette_card_add_one_sub_degree_le_missingColorsAt_card
    (a := a) (palette := palette) hhole hinc
  omega

section Fill

variable [DecidableEq G.edgeSet]

/-- A blocked valid one-hole coloring with an exact `D + 2` palette satisfies
the critical endpoint degree-sum bound.  In contrast with the corresponding
theorem in `TotalColoring.Missing`, the endpoint missing-color lower bounds
are derived here rather than supplied as hypotheses. -/
theorem degree_sum_of_no_valid_complete_rainbow_fill_of_palette_card_eq
    {a : PartialEdgeAssignment G C} {palette : Finset C}
    {e : G.edgeSet} {u v : V} {J : Set G.edgeSet} {D : ℕ}
    (hends : (e : Sym2 V) = s(u, v))
    (hvalid : a.Valid) (hhole : a.OneHoleAt e)
    (hrainbow : a.RainbowOn J) (heJ : e ∉ J)
    (hblocked : a.NoValidCompleteRainbowFill palette e J)
    (hPalette : palette.card = D + 2) :
    D + 4 ≤ G.degree u + G.degree v := by
  have hincU : Incident u e := by
    change u ∈ (e : Sym2 V)
    rw [hends]
    exact Sym2.mem_mk_left u v
  have hincV : Incident v e := by
    change v ∈ (e : Sym2 V)
    rw [hends]
    exact Sym2.mem_mk_right u v
  exact degree_sum_of_no_valid_complete_rainbow_fill
    hends hvalid hhole hrainbow heJ hblocked hPalette.le
    (D_add_three_sub_degree_le_missingColorsAt_card
      hhole hincU hPalette)
    (D_add_three_sub_degree_le_missingColorsAt_card
      hhole hincV hPalette)

end Fill

end Finite

end PartialEdgeAssignment

end TotalColoring
