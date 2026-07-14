import TotalColoring.Auxiliary

/-!
# Executable certificate checkers and soundness

These Boolean checkers operate on already well-typed Lean values. Parsing and
validating an external serialization is a separate trust-boundary task.
-/

namespace TotalColoring.Certificate

universe u v w

variable {V : Type u} {W : Type v} {C : Type w}
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Decide whether a finite total-coloring assignment is semantically valid. -/
def checkTotal (a : Assignment G C) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [DecidableEq C] : Bool := by
  letI : DecidableRel G.lineGraph.Adj := lineGraphDecidableAdj G
  let h : Decidable a.Valid := by
    unfold Assignment.Valid
    infer_instance
  exact @decide a.Valid h

/-- The total-coloring checker accepts exactly the valid assignments. -/
theorem checkTotal_eq_true_iff (a : Assignment G C) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [DecidableEq C] :
    checkTotal a = true ↔ a.Valid := by
  unfold checkTotal
  simp

/-- Soundness of the total-coloring checker. -/
theorem checkTotal_sound (a : Assignment G C) [Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] [DecidableEq C] (h : checkTotal a = true) : a.Valid :=
  (checkTotal_eq_true_iff a).mp h

/-- Decide whether a finite edge-coloring assignment is proper. -/
def checkEdge (a : EdgeAssignment H C) [Fintype W] [DecidableEq W]
    [DecidableRel H.Adj] [DecidableEq C] : Bool := by
  letI : DecidableRel H.lineGraph.Adj := lineGraphDecidableAdj H
  let h : Decidable a.Valid := by
    unfold EdgeAssignment.Valid
    infer_instance
  exact @decide a.Valid h

/-- The edge-coloring checker accepts exactly the proper assignments. -/
theorem checkEdge_eq_true_iff (a : EdgeAssignment H C) [Fintype W] [DecidableEq W]
    [DecidableRel H.Adj] [DecidableEq C] :
    checkEdge a = true ↔ a.Valid := by
  unfold checkEdge
  simp

/-- Soundness of the edge-coloring checker. -/
theorem checkEdge_sound (a : EdgeAssignment H C) [Fintype W] [DecidableEq W]
    [DecidableRel H.Adj] [DecidableEq C] (h : checkEdge a = true) : a.Valid :=
  (checkEdge_eq_true_iff a).mp h

/-- Decide whether distinguished auxiliary edges have pairwise distinct colors. -/
def checkRainbow (a : EdgeAssignment H C) (distinguished : V → H.edgeSet)
    [Fintype V] [DecidableEq W] [DecidableEq C] : Bool := by
  let h : Decidable (a.Rainbow distinguished) := by
    unfold EdgeAssignment.Rainbow
    infer_instance
  exact @decide (a.Rainbow distinguished) h

/-- The rainbow checker accepts exactly the rainbow assignments. -/
theorem checkRainbow_eq_true_iff (a : EdgeAssignment H C)
    (distinguished : V → H.edgeSet) [Fintype V] [DecidableEq W] [DecidableEq C] :
    checkRainbow a distinguished = true ↔ a.Rainbow distinguished := by
  unfold checkRainbow
  simp

/-- Soundness of the rainbow checker. -/
theorem checkRainbow_sound (a : EdgeAssignment H C)
    (distinguished : V → H.edgeSet) [Fintype V] [DecidableEq W] [DecidableEq C]
    (h : checkRainbow a distinguished = true) : a.Rainbow distinguished :=
  (checkRainbow_eq_true_iff a distinguished).mp h

/-- Check both obligations on an auxiliary edge-coloring certificate. -/
def checkExtension (X : Auxiliary.Extension G H) (a : EdgeAssignment H C)
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableRel H.Adj]
    [DecidableEq C] : Bool :=
  checkEdge a && checkRainbow a X.classEdge

/-- The combined checker accepts exactly proper, rainbow auxiliary assignments. -/
theorem checkExtension_eq_true_iff (X : Auxiliary.Extension G H)
    (a : EdgeAssignment H C) [Fintype V] [Fintype W] [DecidableEq W]
    [DecidableRel H.Adj] [DecidableEq C] :
    checkExtension X a = true ↔ a.Valid ∧ a.Rainbow X.classEdge := by
  simp [checkExtension, checkEdge_eq_true_iff, checkRainbow_eq_true_iff]

/-- An accepted auxiliary certificate decodes to a valid total coloring. -/
theorem checkExtension_sound (X : Auxiliary.Extension G H)
    (a : EdgeAssignment H C) [Fintype V] [Fintype W] [DecidableEq W]
    [DecidableRel H.Adj] [DecidableEq C] (h : checkExtension X a = true) :
    (X.decode a).Valid := by
  have hchecked := (checkExtension_eq_true_iff X a).mp h
  exact X.decode_valid a hchecked.1 hchecked.2

end TotalColoring.Certificate
