import TotalColoring.Graph

/-!
# Total- and edge-coloring assignments

The definitions in this module are semantic. They do not invoke a search
procedure and make no claim that a valid assignment exists for an arbitrary
graph or palette.
-/

namespace TotalColoring

universe u v w

/-- A candidate total coloring assigns colors to every vertex and edge. -/
structure Assignment {V : Type u} (G : SimpleGraph V) (C : Type v) where
  vertexColor : V → C
  edgeColor : G.edgeSet → C

namespace Assignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Semantic validity of a total-coloring assignment. -/
protected def Valid (a : Assignment G C) : Prop :=
  (∀ v w, G.Adj v w → a.vertexColor v ≠ a.vertexColor w) ∧
  (∀ e f, G.lineGraph.Adj e f → a.edgeColor e ≠ a.edgeColor f) ∧
  (∀ v e, Incident v e → a.vertexColor v ≠ a.edgeColor e)

end Assignment

/-- A candidate edge coloring assigns a color to every edge. -/
structure EdgeAssignment {V : Type u} (G : SimpleGraph V) (C : Type v) where
  color : G.edgeSet → C

namespace EdgeAssignment

variable {V : Type u} {W : Type w} {G : SimpleGraph V} {H : SimpleGraph W}
variable {C : Type v}

/-- Semantic validity of an edge-coloring assignment. -/
protected def Valid (a : EdgeAssignment G C) : Prop :=
  ∀ e f, G.lineGraph.Adj e f → a.color e ≠ a.color f

/-- The distinct edges selected by `distinguished` receive distinct colors.

The selector may take the same value at several vertices, as happens for the
two endpoints of one paired color class. -/
protected def Rainbow (a : EdgeAssignment H C) (distinguished : V → H.edgeSet) : Prop :=
  ∀ v w, distinguished v ≠ distinguished w →
    a.color (distinguished v) ≠ a.color (distinguished w)

end EdgeAssignment

end TotalColoring
