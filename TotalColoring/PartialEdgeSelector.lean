import TotalColoring.TotalIndependentSelector

/-!
# Partial-edge selector decoder and exact normalization

The old edge colors on a selected matching need not form part of the input
certificate: those values are discarded when the matching is sent to the
fresh color.  It is enough for the old edge assignment to be proper away from
the selected matching.  Likewise, an old vertex color only has to avoid the
incident edges outside that matching.

The second half of this file records the exact converse bookkeeping for a
*supplied* valid total coloring.  After choosing one palette color as fresh,
its vertex and edge color classes give the selector sets, and the remaining
colors are pulled back through `Fin.succAbove`.  Decoding the resulting data
is literally the supplied assignment.  This normalization does not construct
a total coloring and makes no existence claim for an arbitrary graph.
-/

namespace TotalColoring

universe u v

namespace EdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- An edge assignment is proper outside `F` when adjacent edges which both
lie outside `F` have different colors.  Values on `F` are unrestricted. -/
def ValidOutside (a : EdgeAssignment G C) (F : Finset G.edgeSet) : Prop :=
  ∀ e f : G.edgeSet, e ∉ F → f ∉ F →
    G.lineGraph.Adj e f → a.color e ≠ a.color f

/-- A globally proper edge assignment is proper outside every `F`. -/
theorem validOutside_of_valid (a : EdgeAssignment G C)
    (F : Finset G.edgeSet) (ha : a.Valid) : a.ValidOutside F := by
  intro e f _ _ hef
  exact ha e f hef

end EdgeAssignment

private theorem assignment_eq_of_colors_eq
    {V : Type u} {G : SimpleGraph V} {C : Type v}
    {a b : Assignment G C}
    (hvertex : a.vertexColor = b.vertexColor)
    (hedge : a.edgeColor = b.edgeColor) : a = b := by
  cases a with
  | mk av ae =>
      cases b with
      | mk bv be =>
          dsimp only at hvertex hedge
          cases hvertex
          cases hedge
          rfl

section Decoder

variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V} {q : ℕ}

/-- Send the selected edges to `fresh` and embed every unselected old color
through the canonical embedding whose range omits `fresh`. -/
def partialEdgeSelectorEdgeAssignment
    (fresh : Fin (q + 1)) (phi : EdgeAssignment G (Fin q))
    (F : Finset G.edgeSet) : EdgeAssignment G (Fin (q + 1)) where
  color e := if e ∈ F then fresh else fresh.succAbove (phi.color e)

/-- Properness outside a selected matching is exactly what is needed after
the matching is sent to the fresh color. -/
theorem partialEdgeSelectorEdgeAssignment_valid
    (fresh : Fin (q + 1)) (phi : EdgeAssignment G (Fin q))
    (F : Finset G.edgeSet) (hphi : phi.ValidOutside F)
    (hF : EdgeFinsetIsMatching (G := G) F) :
    (partialEdgeSelectorEdgeAssignment fresh phi F).Valid := by
  intro e f hef
  by_cases he : e ∈ F
  · by_cases hf : f ∈ F
    · exact (hF he hf hef).elim
    · simp [partialEdgeSelectorEdgeAssignment, he, hf]
  · by_cases hf : f ∈ F
    · simp [partialEdgeSelectorEdgeAssignment, he, hf]
    · intro heq
      apply hphi e f he hf hef
      exact Fin.succAbove_right_injective (p := fresh) (by
        simpa [partialEdgeSelectorEdgeAssignment, he, hf] using heq)

/-- Decode a chosen fresh vertex class, a chosen fresh edge matching, and old
colors on the complement into a total assignment. -/
def partialEdgeSelectorAssignment
    (fresh : Fin (q + 1)) (phi : EdgeAssignment G (Fin q))
    (S : Finset V) (F : Finset G.edgeSet) (g : V → Fin q) :
    Assignment G (Fin (q + 1)) where
  vertexColor v := if v ∈ S then fresh else fresh.succAbove (g v)
  edgeColor := (partialEdgeSelectorEdgeAssignment fresh phi F).color

/-- Soundness of the partial-edge selector decoder.  The old values on `F`
are ignored, so only `phi.ValidOutside F` is required. -/
theorem partialEdgeSelectorAssignment_valid
    (fresh : Fin (q + 1)) (phi : EdgeAssignment G (Fin q))
    (S : Finset V) (F : Finset G.edgeSet) (g : V → Fin q)
    (hphi : phi.ValidOutside F)
    (hS : G.IsIndepSet (S : Set V))
    (hF : EdgeFinsetIsMatching (G := G) F)
    (havoid : EdgeFinsetAvoids (G := G) F S)
    (hallowed : ∀ v, v ∉ S → SelectorOldColorAllowed phi F v (g v))
    (hproper : ∀ v, v ∉ S → ∀ w, w ∉ S → G.Adj v w → g v ≠ g w) :
    (partialEdgeSelectorAssignment fresh phi S F g).Valid := by
  refine ⟨?_, partialEdgeSelectorEdgeAssignment_valid fresh phi F hphi hF, ?_⟩
  · intro v w hvw
    by_cases hv : v ∈ S
    · by_cases hw : w ∈ S
      · exact (hS hv hw hvw.ne hvw).elim
      · simp [partialEdgeSelectorAssignment, hv, hw]
    · by_cases hw : w ∈ S
      · simp [partialEdgeSelectorAssignment, hv, hw]
      · intro heq
        apply hproper v hv w hw hvw
        exact Fin.succAbove_right_injective (p := fresh) (by
          simpa [partialEdgeSelectorAssignment, hv, hw] using heq)
  · intro v e hve
    by_cases hv : v ∈ S
    · have he : e ∉ F := by
        intro heF
        exact havoid hv heF hve
      simp [partialEdgeSelectorAssignment,
        partialEdgeSelectorEdgeAssignment, hv, he]
    · by_cases he : e ∈ F
      · simp [partialEdgeSelectorAssignment,
          partialEdgeSelectorEdgeAssignment, hv, he]
      · intro heq
        apply hallowed v hv e hve he
        exact (Fin.succAbove_right_injective (p := fresh) (by
          simpa [partialEdgeSelectorAssignment,
            partialEdgeSelectorEdgeAssignment, hv, he] using heq)).symm

/-- The existing last-color edge decoder only needs properness outside its
selected matching; the values of `phi` on the matching are irrelevant. -/
theorem selectorEdgeAssignment_valid_of_validOutside
    (phi : EdgeAssignment G (Fin q)) (F : Finset G.edgeSet)
    (hphi : phi.ValidOutside F)
    (hF : EdgeFinsetIsMatching (G := G) F) :
    (selectorEdgeAssignment phi F).Valid := by
  simpa [selectorEdgeAssignment, partialEdgeSelectorEdgeAssignment] using
    partialEdgeSelectorEdgeAssignment_valid (Fin.last q) phi F hphi hF

/-- Stronger soundness theorem for the existing last-color selector decoder:
old edge colors are required to be proper only outside `F`. -/
theorem totalIndependentSelectorAssignment_valid_of_validOutside
    (phi : EdgeAssignment G (Fin q)) (S : Finset V)
    (F : Finset G.edgeSet) (g : V → Fin q)
    (hphi : phi.ValidOutside F)
    (hS : G.IsIndepSet (S : Set V))
    (hF : EdgeFinsetIsMatching (G := G) F)
    (havoid : EdgeFinsetAvoids (G := G) F S)
    (hallowed : ∀ v, v ∉ S → SelectorOldColorAllowed phi F v (g v))
    (hproper : ∀ v, v ∉ S → ∀ w, w ∉ S → G.Adj v w → g v ≠ g w) :
    (totalIndependentSelectorAssignment phi S F g).Valid := by
  simpa [totalIndependentSelectorAssignment,
    partialEdgeSelectorAssignment, selectorEdgeAssignment,
    partialEdgeSelectorEdgeAssignment] using
      partialEdgeSelectorAssignment_valid (Fin.last q) phi S F g
        hphi hS hF havoid hallowed hproper

end Decoder

section Normalization

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [Fintype G.edgeSet] {q : ℕ}

/-- The vertices receiving the chosen fresh color in a supplied assignment. -/
def freshVertexClass (a : Assignment G (Fin (q + 1)))
    (fresh : Fin (q + 1)) : Finset V :=
  Finset.univ.filter fun v ↦ a.vertexColor v = fresh

/-- The edges receiving the chosen fresh color in a supplied assignment. -/
def freshEdgeClass (a : Assignment G (Fin (q + 1)))
    (fresh : Fin (q + 1)) : Finset G.edgeSet :=
  Finset.univ.filter fun e ↦ a.edgeColor e = fresh

/-- Pull a color back through `fresh.succAbove`.  The supplied fallback is
used only at `fresh`, where the old value will be discarded by the decoder. -/
noncomputable def oldColorOutsideFresh (fresh : Fin (q + 1))
    (fallback : Fin q) (c : Fin (q + 1)) : Fin q :=
  if h : c = fresh then fallback
  else Classical.choose (Fin.exists_succAbove_eq h)

/-- Away from `fresh`, `oldColorOutsideFresh` is an exact right inverse of
the embedding which omits `fresh`. -/
theorem succAbove_oldColorOutsideFresh (fresh : Fin (q + 1))
    (fallback : Fin q) (c : Fin (q + 1)) (hc : c ≠ fresh) :
    fresh.succAbove (oldColorOutsideFresh fresh fallback c) = c := by
  simp only [oldColorOutsideFresh, dif_neg hc]
  exact Classical.choose_spec (Fin.exists_succAbove_eq hc)

/-- Old edge colors extracted from a supplied total assignment.  Values on
the fresh edge class are the arbitrary fallback and will be ignored. -/
noncomputable def normalizedOldEdgeAssignment
    (a : Assignment G (Fin (q + 1))) (fresh : Fin (q + 1))
    (fallback : Fin q) : EdgeAssignment G (Fin q) where
  color e := oldColorOutsideFresh fresh fallback (a.edgeColor e)

/-- Old vertex colors extracted from a supplied total assignment.  Values on
the fresh vertex class are the arbitrary fallback and will be ignored. -/
noncomputable def normalizedOldVertexColor
    (a : Assignment G (Fin (q + 1))) (fresh : Fin (q + 1))
    (fallback : Fin q) : V → Fin q :=
  fun v ↦ oldColorOutsideFresh fresh fallback (a.vertexColor v)

/-- The complete selector data obtained by choosing one color class in a
supplied assignment.  `decodes` records literal equality with that assignment,
not merely equality up to a palette permutation. -/
structure PartialEdgeSelectorNormalization
    (a : Assignment G (Fin (q + 1))) (fresh : Fin (q + 1)) where
  S : Finset V
  F : Finset G.edgeSet
  oldEdge : EdgeAssignment G (Fin q)
  oldVertex : V → Fin q
  edge_validOutside : oldEdge.ValidOutside F
  vertex_independent : G.IsIndepSet (S : Set V)
  edge_matching : EdgeFinsetIsMatching (G := G) F
  edge_avoids_vertices : EdgeFinsetAvoids (G := G) F S
  vertex_allowed :
    ∀ v, v ∉ S → SelectorOldColorAllowed oldEdge F v (oldVertex v)
  vertex_proper :
    ∀ v, v ∉ S → ∀ w, w ∉ S →
      G.Adj v w → oldVertex v ≠ oldVertex w
  decodes : partialEdgeSelectorAssignment fresh oldEdge S F oldVertex = a

/-- A supplied valid total assignment has an exact partial-edge selector
normalization at every chosen fresh color, once an irrelevant fallback old
color is supplied.  This is a reverse decomposition theorem, not an existence
theorem for total colorings. -/
noncomputable def partialEdgeSelectorNormalization_of_valid
    (a : Assignment G (Fin (q + 1))) (ha : a.Valid)
    (fresh : Fin (q + 1)) (fallback : Fin q) :
    PartialEdgeSelectorNormalization a fresh where
  S := freshVertexClass a fresh
  F := freshEdgeClass a fresh
  oldEdge := normalizedOldEdgeAssignment a fresh fallback
  oldVertex := normalizedOldVertexColor a fresh fallback
  edge_validOutside := by
    intro e f he hf hef heq
    apply ha.2.1 e f hef
    have heFresh : a.edgeColor e ≠ fresh := by
      intro h
      apply he
      simp [freshEdgeClass, h]
    have hfFresh : a.edgeColor f ≠ fresh := by
      intro h
      apply hf
      simp [freshEdgeClass, h]
    calc
      a.edgeColor e = fresh.succAbove
          ((normalizedOldEdgeAssignment a fresh fallback).color e) :=
        (succAbove_oldColorOutsideFresh fresh fallback
          (a.edgeColor e) heFresh).symm
      _ = fresh.succAbove
          ((normalizedOldEdgeAssignment a fresh fallback).color f) := by
        exact congrArg fresh.succAbove heq
      _ = a.edgeColor f :=
        succAbove_oldColorOutsideFresh fresh fallback
          (a.edgeColor f) hfFresh
  vertex_independent := by
    intro v hv w hw hvw hAdj
    apply ha.1 v w hAdj
    have hvFresh : a.vertexColor v = fresh := by
      simpa [freshVertexClass] using hv
    have hwFresh : a.vertexColor w = fresh := by
      simpa [freshVertexClass] using hw
    exact hvFresh.trans hwFresh.symm
  edge_matching := by
    intro e f he hf hAdj
    apply ha.2.1 e f hAdj
    have heFresh : a.edgeColor e = fresh := by
      simpa [freshEdgeClass] using he
    have hfFresh : a.edgeColor f = fresh := by
      simpa [freshEdgeClass] using hf
    exact heFresh.trans hfFresh.symm
  edge_avoids_vertices := by
    intro v hv e he hIncident
    apply ha.2.2 v e hIncident
    have hvFresh : a.vertexColor v = fresh := by
      simpa [freshVertexClass] using hv
    have heFresh : a.edgeColor e = fresh := by
      simpa [freshEdgeClass] using he
    exact hvFresh.trans heFresh.symm
  vertex_allowed := by
    intro v hv e hIncident he heq
    apply ha.2.2 v e hIncident
    have hvFresh : a.vertexColor v ≠ fresh := by
      intro h
      apply hv
      simp [freshVertexClass, h]
    have heFresh : a.edgeColor e ≠ fresh := by
      intro h
      apply he
      simp [freshEdgeClass, h]
    calc
      a.vertexColor v = fresh.succAbove
          (normalizedOldVertexColor a fresh fallback v) :=
        (succAbove_oldColorOutsideFresh fresh fallback
          (a.vertexColor v) hvFresh).symm
      _ = fresh.succAbove
          ((normalizedOldEdgeAssignment a fresh fallback).color e) := by
        exact congrArg fresh.succAbove heq.symm
      _ = a.edgeColor e :=
        succAbove_oldColorOutsideFresh fresh fallback
          (a.edgeColor e) heFresh
  vertex_proper := by
    intro v hv w hw hAdj heq
    apply ha.1 v w hAdj
    have hvFresh : a.vertexColor v ≠ fresh := by
      intro h
      apply hv
      simp [freshVertexClass, h]
    have hwFresh : a.vertexColor w ≠ fresh := by
      intro h
      apply hw
      simp [freshVertexClass, h]
    calc
      a.vertexColor v = fresh.succAbove
          (normalizedOldVertexColor a fresh fallback v) :=
        (succAbove_oldColorOutsideFresh fresh fallback
          (a.vertexColor v) hvFresh).symm
      _ = fresh.succAbove
          (normalizedOldVertexColor a fresh fallback w) := by
        exact congrArg fresh.succAbove heq
      _ = a.vertexColor w :=
        succAbove_oldColorOutsideFresh fresh fallback
          (a.vertexColor w) hwFresh
  decodes := by
    apply assignment_eq_of_colors_eq
    · funext v
      by_cases hv : a.vertexColor v = fresh
      · simp [partialEdgeSelectorAssignment, freshVertexClass, hv]
      · simp [partialEdgeSelectorAssignment, freshVertexClass, hv,
          normalizedOldVertexColor,
          succAbove_oldColorOutsideFresh fresh fallback (a.vertexColor v) hv]
    · funext e
      by_cases he : a.edgeColor e = fresh
      · simp [partialEdgeSelectorAssignment,
          partialEdgeSelectorEdgeAssignment, freshEdgeClass, he]
      · simp [partialEdgeSelectorAssignment,
          partialEdgeSelectorEdgeAssignment, freshEdgeClass, he,
          normalizedOldEdgeAssignment,
          succAbove_oldColorOutsideFresh fresh fallback (a.edgeColor e) he]

/-- Maximum-degree notation for the exact reverse normalization of a supplied
`Delta + 2` total coloring.  The input coloring remains an explicit argument. -/
noncomputable def maxDegreePartialEdgeSelectorNormalization_of_valid
    [DecidableRel G.Adj]
    (a : Assignment G (Fin (G.maxDegree + 2))) (ha : a.Valid)
    (fresh : Fin (G.maxDegree + 2)) :
    PartialEdgeSelectorNormalization
      (q := G.maxDegree + 1) a fresh := by
  exact partialEdgeSelectorNormalization_of_valid a ha fresh
    ⟨0, Nat.succ_pos G.maxDegree⟩

end Normalization

end TotalColoring
