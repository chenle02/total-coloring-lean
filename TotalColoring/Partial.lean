import TotalColoring.RainbowSwap

/-!
# Partial edge colorings

This module treats `none` as an uncolored edge and `some c` as a colored edge.
Validity forbids equal actual colors on adjacent edges; two uncolored edges do
not conflict.  The main results show that a color missing at both endpoints of
an uncolored edge can fill a unique hole, and that the resulting complete
partial assignment induces an ordinary proper edge coloring.
-/

namespace TotalColoring

universe u v

/-- A partial edge coloring assigns either no color or one palette color to
each edge. -/
structure PartialEdgeAssignment {V : Type u} (G : SimpleGraph V) (C : Type v) where
  color : G.edgeSet → Option C

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- No two adjacent colored edges receive the same actual color. -/
protected def Valid (a : PartialEdgeAssignment G C) : Prop :=
  ∀ e f c, G.lineGraph.Adj e f → a.color e = some c → a.color f ≠ some c

/-- A color is missing at a vertex when no incident edge currently has it. -/
def MissingAt (a : PartialEdgeAssignment G C) (v : V) (c : C) : Prop :=
  ∀ e, Incident v e → a.color e ≠ some c

/-- A color is available for an edge when no adjacent edge currently has it. -/
def AvailableAtEdge (a : PartialEdgeAssignment G C) (e : G.edgeSet) (c : C) : Prop :=
  ∀ f, G.lineGraph.Adj e f → a.color f ≠ some c

/-- A color is missing at every endpoint of an edge. -/
def MissingAtEndpoints (a : PartialEdgeAssignment G C) (e : G.edgeSet) (c : C) : Prop :=
  ∀ v, Incident v e → a.MissingAt v c

/-- Every edge has an actual color. -/
def Complete (a : PartialEdgeAssignment G C) : Prop :=
  ∀ e, ∃ c, a.color e = some c

/-- The designated edge is the unique uncolored edge. -/
def OneHoleAt (a : PartialEdgeAssignment G C) (e : G.edgeSet) : Prop :=
  ∀ f, a.color f = none ↔ f = e

/-- Every distinguished edge currently has an actual color. -/
def ColoredOn (a : PartialEdgeAssignment G C) (J : Set G.edgeSet) : Prop :=
  ∀ e, e ∈ J → ∃ c, a.color e = some c

/-- The distinguished edges are colored and have pairwise distinct colors. -/
def RainbowOn (a : PartialEdgeAssignment G C) (J : Set G.edgeSet) : Prop :=
  a.ColoredOn J ∧
    ∀ {e}, e ∈ J → ∀ {f}, f ∈ J → e ≠ f → a.color e ≠ a.color f

/-- If the unique hole lies outside `J`, then every edge of `J` is colored. -/
theorem coloredOn_of_oneHoleAt_not_mem {a : PartialEdgeAssignment G C}
    {e : G.edgeSet} {J : Set G.edgeSet} (hhole : a.OneHoleAt e) (heJ : e ∉ J) :
    a.ColoredOn J := by
  intro f hf
  have hnotnone : a.color f ≠ none := by
    intro hnone
    exact heJ ((hhole f).mp hnone ▸ hf)
  cases hfc : a.color f with
  | none => exact (hnotnone hfc).elim
  | some c => exact ⟨c, rfl⟩

theorem availableAtEdge_of_missingAtEndpoints {a : PartialEdgeAssignment G C}
    {e : G.edgeSet} {c : C} (h : a.MissingAtEndpoints e c) :
    a.AvailableAtEdge e c := by
  intro f hef
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hef with ⟨_, v, hve, hvf⟩
  exact h v hve f hvf

section Fill

variable [DecidableEq G.edgeSet]

/-- Replace the color of one edge by an actual color. -/
def fill (a : PartialEdgeAssignment G C) (e : G.edgeSet) (c : C) :
    PartialEdgeAssignment G C where
  color f := if f = e then some c else a.color f

@[simp]
theorem fill_color_self (a : PartialEdgeAssignment G C) (e : G.edgeSet) (c : C) :
    (a.fill e c).color e = some c := by
  simp [fill]

@[simp]
theorem fill_color_of_ne (a : PartialEdgeAssignment G C) {e f : G.edgeSet} (c : C)
    (h : f ≠ e) : (a.fill e c).color f = a.color f := by
  simp [fill, h]

/-- Filling an edge with an available color preserves partial properness. -/
theorem fill_valid {a : PartialEdgeAssignment G C} {e : G.edgeSet} {c : C}
    (ha : a.Valid) (hc : a.AvailableAtEdge e c) : (a.fill e c).Valid := by
  intro f g d hfg hfd
  by_cases hfe : f = e
  · subst f
    have hcd : c = d := by
      exact Option.some.inj (by simpa using hfd)
    subst d
    have hge : g ≠ e := hfg.ne'
    simpa [fill, hge] using hc g hfg
  · have hfd' : a.color f = some d := by
      simpa [fill, hfe] using hfd
    by_cases hge : g = e
    · subst g
      rw [fill_color_self]
      intro hcd
      have hdc : d = c := (Option.some.inj hcd).symm
      apply hc f hfg.symm
      simpa [hdc] using hfd'
    · simpa [fill, hge] using ha f g d hfg hfd'

/-- Filling the unique hole makes the partial assignment complete. -/
theorem fill_complete_of_oneHoleAt {a : PartialEdgeAssignment G C} {e : G.edgeSet} {c : C}
    (hhole : a.OneHoleAt e) : (a.fill e c).Complete := by
  intro f
  by_cases hfe : f = e
  · subst f
    exact ⟨c, fill_color_self a e c⟩
  · have hnotnone : a.color f ≠ none := by
      intro hf
      exact hfe ((hhole f).mp hf)
    cases hfc : a.color f with
    | none => exact (hnotnone hfc).elim
    | some d =>
        exact ⟨d, by simpa [fill, hfe] using hfc⟩

/-- Filling an edge outside `J` preserves the partial rainbow invariant. -/
theorem fill_rainbowOn_of_not_mem {a : PartialEdgeAssignment G C}
    {e : G.edgeSet} {c : C} {J : Set G.edgeSet} (hrainbow : a.RainbowOn J)
    (heJ : e ∉ J) : (a.fill e c).RainbowOn J := by
  constructor
  · intro f hf
    rcases hrainbow.1 f hf with ⟨d, hfd⟩
    exact ⟨d, by simpa [fill, ne_of_mem_of_not_mem hf heJ] using hfd⟩
  · intro f hf g hg hfg
    have hfe : f ≠ e := ne_of_mem_of_not_mem hf heJ
    have hge : g ≠ e := ne_of_mem_of_not_mem hg heJ
    simpa [fill, hfe, hge] using hrainbow.2 hf hg hfg

/-- A common missing endpoint color fills a unique hole properly and
completely. -/
theorem fill_valid_complete_of_oneHoleAt_missingAtEndpoints
    {a : PartialEdgeAssignment G C} {e : G.edgeSet} {c : C}
    (ha : a.Valid) (hhole : a.OneHoleAt e) (hc : a.MissingAtEndpoints e c) :
    (a.fill e c).Valid ∧ (a.fill e c).Complete := by
  exact ⟨fill_valid ha (availableAtEdge_of_missingAtEndpoints hc),
    fill_complete_of_oneHoleAt hhole⟩

/-- Filling a unique hole outside `J` with a common endpoint-missing color
preserves properness and the `J`-rainbow constraint and makes the coloring
complete. -/
theorem fill_valid_complete_rainbowOn_of_oneHoleAt_missingAtEndpoints
    {a : PartialEdgeAssignment G C} {e : G.edgeSet} {c : C}
    {J : Set G.edgeSet} (ha : a.Valid) (hhole : a.OneHoleAt e)
    (hc : a.MissingAtEndpoints e c) (hrainbow : a.RainbowOn J) (heJ : e ∉ J) :
    (a.fill e c).Valid ∧ (a.fill e c).Complete ∧ (a.fill e c).RainbowOn J := by
  exact ⟨fill_valid ha (availableAtEdge_of_missingAtEndpoints hc),
    fill_complete_of_oneHoleAt hhole, fill_rainbowOn_of_not_mem hrainbow heJ⟩

end Fill

section Complete

/-- Forget the `Option` wrapper on a complete partial edge assignment. -/
noncomputable def toEdgeAssignment (a : PartialEdgeAssignment G C) (h : a.Complete) :
    EdgeAssignment G C where
  color e := Classical.choose (h e)

@[simp]
theorem color_toEdgeAssignment (a : PartialEdgeAssignment G C) (h : a.Complete)
    (e : G.edgeSet) : a.color e = some ((a.toEdgeAssignment h).color e) := by
  exact Classical.choose_spec (h e)

/-- Forgetting the `Option` wrapper preserves properness. -/
theorem toEdgeAssignment_valid {a : PartialEdgeAssignment G C} (hcomplete : a.Complete)
    (hvalid : a.Valid) : (a.toEdgeAssignment hcomplete).Valid := by
  intro e f hef heq
  have hcolor := hvalid e f ((a.toEdgeAssignment hcomplete).color e) hef
    (color_toEdgeAssignment a hcomplete e)
  apply hcolor
  rw [color_toEdgeAssignment a hcomplete f, heq]

/-- Forgetting the `Option` wrapper also preserves the distinguished-set
rainbow property. -/
theorem toEdgeAssignment_rainbowOn {a : PartialEdgeAssignment G C}
    (hcomplete : a.Complete) {J : Set G.edgeSet} (hrainbow : a.RainbowOn J) :
    (a.toEdgeAssignment hcomplete).RainbowOn J := by
  intro e he f hf hef heq
  apply hrainbow.2 he hf hef
  rw [color_toEdgeAssignment a hcomplete e, color_toEdgeAssignment a hcomplete f, heq]

section Fill

variable [DecidableEq G.edgeSet]

/-- The one-hole endpoint criterion yields an ordinary proper edge coloring. -/
theorem exists_valid_edgeAssignment_of_oneHoleAt_missingAtEndpoints
    {a : PartialEdgeAssignment G C} {e : G.edgeSet} {c : C}
    (ha : a.Valid) (hhole : a.OneHoleAt e) (hc : a.MissingAtEndpoints e c) :
    ∃ b : EdgeAssignment G C, b.Valid ∧
      ∀ f, (a.fill e c).color f = some (b.color f) := by
  have h := fill_valid_complete_of_oneHoleAt_missingAtEndpoints ha hhole hc
  let b := (a.fill e c).toEdgeAssignment h.2
  exact ⟨b, toEdgeAssignment_valid h.2 h.1, fun f ↦ color_toEdgeAssignment _ h.2 f⟩

end Fill

end Complete

end PartialEdgeAssignment

end TotalColoring
