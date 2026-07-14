import TotalColoring.Total

/-!
# Conditional auxiliary-extension reduction

This module isolates the structural facts needed to decode a rainbow proper
edge coloring of an auxiliary graph into a total coloring of the original
graph. Constructing such an extension, and proving that it is colorable with a
particular palette, are deliberately separate obligations.
-/

namespace TotalColoring.Auxiliary

universe u v w

variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Structural data sufficient for the auxiliary decoding argument.

`classEdge v` is the distinguished auxiliary edge whose color becomes the
color of `v`. `originalEdge e` is the copy of an original edge in the
auxiliary graph. The three proof fields are precisely the conflict-preservation
facts used by decoding. -/
structure Extension (G : SimpleGraph V) (H : SimpleGraph W) where
  classEdge : V → H.edgeSet
  originalEdge : G.edgeSet → H.edgeSet
  classEdge_ne_of_adj :
    ∀ {v w}, G.Adj v w → classEdge v ≠ classEdge w
  originalEdge_adj :
    ∀ {e f}, G.lineGraph.Adj e f →
      H.lineGraph.Adj (originalEdge e) (originalEdge f)
  classEdge_adj_original :
    ∀ {v e}, Incident v e →
      H.lineGraph.Adj (classEdge v) (originalEdge e)

namespace Extension

variable {C : Type w} (X : Extension G H)

/-- Decode auxiliary edge colors into vertex and edge colors of the original
graph. -/
def decode (a : EdgeAssignment H C) : Assignment G C where
  vertexColor v := a.color (X.classEdge v)
  edgeColor e := a.color (X.originalEdge e)

/-- A proper auxiliary edge coloring that is rainbow on the distinguished
family decodes to a valid total coloring. -/
theorem decode_valid (a : EdgeAssignment H C) (ha : a.Valid)
    (hr : a.Rainbow X.classEdge) : (X.decode a).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w hv hcolor
    exact hr v w (X.classEdge_ne_of_adj hv) hcolor
  · intro e f hef
    exact ha _ _ (X.originalEdge_adj hef)
  · intro v e hve
    exact ha _ _ (X.classEdge_adj_original hve)

end Extension

end TotalColoring.Auxiliary
