import TotalColoring.MissingCount

/-!
# Missing-color counts at an arbitrary vertex

This module proves the vertexwise missing-color bound without assuming that
the partial assignment is valid or has a hole.  Every palette color which is
not missing at a vertex is realized by an incident edge, and distinct realized
colors require distinct edges.  Thus

`palette.card ≤ (a.missingColorsAt palette v).card + G.degree v`.

In particular, an exact `D + 2` palette leaves at least two colors missing at
every vertex of degree at most `D`.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Edges incident with `v`, expressed as edge-subtype elements, are
equivalent to mathlib's incidence set at `v`. -/
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

/-- The palette colors present at a vertex inject into its incident edges.

No validity or hole hypothesis is needed: a single edge has only one
`Option C` value, so it cannot witness two distinct present colors. -/
theorem card_not_missing_le_degree
    (a : PartialEdgeAssignment G C) (palette : Finset C) (v : V) :
    (palette \ a.missingColorsAt palette v).card ≤ G.degree v := by
  classical
  let present := palette \ a.missingColorsAt palette v
  have hRealized (c : C) (hc : c ∈ present) :
      ∃ e : G.edgeSet, Incident v e ∧ a.color e = some c := by
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
  let embed : {c : C // c ∈ present} →
      {e : G.edgeSet // Incident v e} := fun c ↦
    ⟨witness c, (hwitness c).1⟩
  have hinjective : Function.Injective embed := by
    intro c d hcd
    apply Subtype.ext
    apply Option.some.inj
    have hedge : witness c = witness d := congrArg Subtype.val hcd
    calc
      some c.1 = a.color (witness c) := (hwitness c).2.symm
      _ = a.color (witness d) := congrArg a.color hedge
      _ = some d.1 := (hwitness d).2
  change present.card ≤ G.degree v
  calc
    present.card = Fintype.card {c : C // c ∈ present} := by simp
    _ ≤ Fintype.card {e : G.edgeSet // Incident v e} :=
      Fintype.card_le_of_injective embed hinjective
    _ = G.degree v := card_incidentEdges_eq_degree (G := G) v

/-- At every vertex, the palette size is at most the number of missing
palette colors plus the degree.  This requires neither validity nor a hole. -/
theorem palette_card_le_missingColorsAt_card_add_degree
    (a : PartialEdgeAssignment G C) (palette : Finset C) (v : V) :
    palette.card ≤ (a.missingColorsAt palette v).card + G.degree v := by
  classical
  have hpresent := card_not_missing_le_degree a palette v
  have hpartition :
      (palette \ a.missingColorsAt palette v).card +
          (a.missingColorsAt palette v).card = palette.card :=
    Finset.card_sdiff_add_card_eq_card (missingColorsAt_subset a palette v)
  omega

/-- Subtractive form of
`palette_card_le_missingColorsAt_card_add_degree`. -/
theorem palette_card_sub_degree_le_missingColorsAt_card
    (a : PartialEdgeAssignment G C) (palette : Finset C) (v : V) :
    palette.card - G.degree v ≤
      (a.missingColorsAt palette v).card := by
  have hcount := palette_card_le_missingColorsAt_card_add_degree a palette v
  omega

/-- An exact `D + 2` palette leaves at least two colors missing at every
vertex whose degree is at most `D`. -/
theorem two_le_missingColorsAt_card_of_palette_card_eq_of_degree_le
    (a : PartialEdgeAssignment G C) (palette : Finset C) (v : V) (D : ℕ)
    (hPalette : palette.card = D + 2) (hDegree : G.degree v ≤ D) :
    2 ≤ (a.missingColorsAt palette v).card := by
  have hcount := palette_card_le_missingColorsAt_card_add_degree a palette v
  omega

end Finite

end PartialEdgeAssignment

end TotalColoring
