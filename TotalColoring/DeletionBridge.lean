import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import TotalColoring.Partial

/-!
# The deletion-to-one-hole bridge

Deleting one edge changes the edge subtype.  This module keeps that transport
explicit: an ordinary edge coloring of `H.deleteEdges {e}` lifts to a partial
edge coloring of `H` whose unique uncolored edge is `e`.  Properness and a
distinguished-set rainbow condition transfer across the lift.

No existence, minimality, or extension theorem is asserted here.  Supplying a
valid color for the hole remains a separate mathematical obligation.
-/

namespace TotalColoring

universe u v

namespace DeletionBridge

variable {V : Type u} {H : SimpleGraph V} {C : Type v}

/-- The graph obtained by deleting the designated edge. -/
abbrev DeletedGraph (H : SimpleGraph V) (e : H.edgeSet) : SimpleGraph V :=
  H.deleteEdges {(e : Sym2 V)}

/-- Regard an edge of the deletion as an edge of the original graph. -/
def edgeOfDelete (e : H.edgeSet) (f : (DeletedGraph H e).edgeSet) : H.edgeSet :=
  ⟨f.1, by
    have hf : (f : Sym2 V) ∈ H.edgeSet \ {(e : Sym2 V)} := by
      simpa only [SimpleGraph.edgeSet_deleteEdges] using f.2
    exact hf.1⟩

@[simp]
theorem edgeOfDelete_val (e : H.edgeSet) (f : (DeletedGraph H e).edgeSet) :
    ((edgeOfDelete e f : H.edgeSet) : Sym2 V) = (f : Sym2 V) := rfl

/-- An edge surviving the deletion cannot be the deleted edge. -/
theorem edgeOfDelete_ne (e : H.edgeSet) (f : (DeletedGraph H e).edgeSet) :
    edgeOfDelete e f ≠ e := by
  intro h
  have hf : (f : Sym2 V) ∈ H.edgeSet \ {(e : Sym2 V)} := by
    simpa only [SimpleGraph.edgeSet_deleteEdges] using f.2
  exact hf.2 (by simpa using congrArg Subtype.val h)

/-- Regard an original edge different from `e` as an edge of the deletion. -/
def edgeToDelete (e f : H.edgeSet) (hfe : f ≠ e) : (DeletedGraph H e).edgeSet :=
  ⟨f.1, by
    rw [SimpleGraph.edgeSet_deleteEdges]
    refine ⟨f.2, ?_⟩
    simpa only [Set.mem_singleton_iff] using
      (show (f : Sym2 V) ≠ (e : Sym2 V) from fun h ↦ hfe (Subtype.ext h))⟩

@[simp]
theorem edgeToDelete_val (e f : H.edgeSet) (hfe : f ≠ e) :
    ((edgeToDelete e f hfe : (DeletedGraph H e).edgeSet) : Sym2 V) =
      (f : Sym2 V) := rfl

@[simp]
theorem edgeOfDelete_edgeToDelete (e f : H.edgeSet) (hfe : f ≠ e) :
    edgeOfDelete e (edgeToDelete e f hfe) = f := by
  apply Subtype.ext
  rfl

@[simp]
theorem edgeToDelete_edgeOfDelete (e : H.edgeSet)
    (f : (DeletedGraph H e).edgeSet) :
    edgeToDelete e (edgeOfDelete e f) (edgeOfDelete_ne e f) = f := by
  apply Subtype.ext
  rfl

/-- Pull an original distinguished edge set back to the deletion subtype. -/
def distinguishedInDelete (e : H.edgeSet) (J : Set H.edgeSet) :
    Set (DeletedGraph H e).edgeSet :=
  edgeOfDelete e ⁻¹' J

section Decidable

variable [DecidableEq V]

/-- Lift an edge coloring of the deletion to the original graph, leaving
exactly the deleted edge uncolored. -/
def lift (e : H.edgeSet) (a : EdgeAssignment (DeletedGraph H e) C) :
    PartialEdgeAssignment H C where
  color f := if hfe : f = e then none else some (a.color (edgeToDelete e f hfe))

@[simp]
theorem lift_color_deleted (e : H.edgeSet)
    (a : EdgeAssignment (DeletedGraph H e) C) :
    (lift e a).color e = none := by
  simp [lift]

@[simp]
theorem lift_color_of_ne (e f : H.edgeSet)
    (a : EdgeAssignment (DeletedGraph H e) C) (hfe : f ≠ e) :
    (lift e a).color f = some (a.color (edgeToDelete e f hfe)) := by
  simp [lift, hfe]

/-- The lifted partial coloring has exactly the deleted edge as its hole. -/
theorem lift_oneHoleAt (e : H.edgeSet)
    (a : EdgeAssignment (DeletedGraph H e) C) :
    (lift e a).OneHoleAt e := by
  intro f
  by_cases hfe : f = e
  · subst f
    simp
  · simp [lift, hfe]

omit [DecidableEq V] in
/-- Line-graph adjacency is preserved when two surviving edges are transported
to the deletion subtype. -/
theorem lineGraph_adj_edgeToDelete {e f g : H.edgeSet} (hfe : f ≠ e)
    (hge : g ≠ e) (hfg : H.lineGraph.Adj f g) :
    (DeletedGraph H e).lineGraph.Adj (edgeToDelete e f hfe)
      (edgeToDelete e g hge) := by
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hfg with
    ⟨hfgne, x, hxf, hxg⟩
  apply SimpleGraph.lineGraph_adj_iff_exists.mpr
  refine ⟨?_, x, ?_, ?_⟩
  · intro h
    apply hfgne
    exact Subtype.ext
      (congrArg (fun z : (DeletedGraph H e).edgeSet ↦ (z : Sym2 V)) h)
  · exact hxf
  · exact hxg

/-- Properness of the coloring on the deletion transfers to partial
properness of its one-hole lift. -/
theorem lift_valid (e : H.edgeSet) {a : EdgeAssignment (DeletedGraph H e) C}
    (ha : a.Valid) : (lift e a).Valid := by
  intro f g c hfg hfc
  have hfe : f ≠ e := by
    intro h
    subst f
    simp at hfc
  have hfc' : a.color (edgeToDelete e f hfe) = c := by
    simpa [lift, hfe] using hfc
  by_cases hge : g = e
  · subst g
    simp
  · rw [lift_color_of_ne e g a hge]
    intro hgc
    have hgc' : a.color (edgeToDelete e g hge) = c := Option.some.inj hgc
    exact (ha _ _ (lineGraph_adj_edgeToDelete hfe hge hfg))
      (hfc'.trans hgc'.symm)

omit [DecidableEq V] in
/-- Every original distinguished edge different from the deleted edge maps
back into the pulled-back distinguished set. -/
theorem edgeToDelete_mem_distinguishedInDelete {e f : H.edgeSet}
    {J : Set H.edgeSet} (hfJ : f ∈ J) (hfe : f ≠ e) :
    edgeToDelete e f hfe ∈ distinguishedInDelete e J := by
  simpa [distinguishedInDelete] using hfJ

/-- If the deleted edge lies outside `J`, rainbowness on the pulled-back copy
of `J` transfers to partial rainbowness on the original graph. -/
theorem lift_rainbowOn (e : H.edgeSet) {a : EdgeAssignment (DeletedGraph H e) C}
    {J : Set H.edgeSet} (heJ : e ∉ J)
    (ha : a.RainbowOn (distinguishedInDelete e J)) :
    (lift e a).RainbowOn J := by
  constructor
  · intro f hfJ
    have hfe : f ≠ e := ne_of_mem_of_not_mem hfJ heJ
    exact ⟨a.color (edgeToDelete e f hfe), lift_color_of_ne e f a hfe⟩
  · intro f hfJ g hgJ hfg
    have hfe : f ≠ e := ne_of_mem_of_not_mem hfJ heJ
    have hge : g ≠ e := ne_of_mem_of_not_mem hgJ heJ
    rw [lift_color_of_ne e f a hfe, lift_color_of_ne e g a hge]
    intro h
    apply ha (edgeToDelete_mem_distinguishedInDelete hfJ hfe)
      (edgeToDelete_mem_distinguishedInDelete hgJ hge)
      (fun h' ↦ hfg (by simpa using congrArg (edgeOfDelete e) h'))
    exact Option.some.inj h

/-- Filling the lifted hole always gives a complete partial assignment. -/
theorem fill_lift_complete (e : H.edgeSet)
    (a : EdgeAssignment (DeletedGraph H e) C) (c : C) :
    ((lift e a).fill e c).Complete :=
  PartialEdgeAssignment.fill_complete_of_oneHoleAt (lift_oneHoleAt e a)

/-- Any proper fill of the lifted hole induces an ordinary proper edge
coloring of the original graph. -/
theorem fill_toEdgeAssignment_valid (e : H.edgeSet)
    (a : EdgeAssignment (DeletedGraph H e) C) (c : C)
    (hvalid : ((lift e a).fill e c).Valid) :
    (((lift e a).fill e c).toEdgeAssignment (fill_lift_complete e a c)).Valid :=
  PartialEdgeAssignment.toEdgeAssignment_valid (fill_lift_complete e a c) hvalid

/-- A proper, partial-rainbow fill induces an ordinary edge coloring that is
both proper and rainbow on the same distinguished edge set. -/
theorem fill_toEdgeAssignment_valid_rainbowOn (e : H.edgeSet)
    (a : EdgeAssignment (DeletedGraph H e) C) (c : C) {J : Set H.edgeSet}
    (hvalid : ((lift e a).fill e c).Valid)
    (hrainbow : ((lift e a).fill e c).RainbowOn J) :
    (((lift e a).fill e c).toEdgeAssignment (fill_lift_complete e a c)).Valid ∧
      (((lift e a).fill e c).toEdgeAssignment
        (fill_lift_complete e a c)).RainbowOn J := by
  exact ⟨PartialEdgeAssignment.toEdgeAssignment_valid
      (fill_lift_complete e a c) hvalid,
    PartialEdgeAssignment.toEdgeAssignment_rainbowOn
      (fill_lift_complete e a c) hrainbow⟩

/-- A valid coloring of the deletion plus a color available at the deleted
edge yields an ordinary proper edge coloring of the original graph. -/
theorem exists_valid_full_of_available (e : H.edgeSet)
    {a : EdgeAssignment (DeletedGraph H e) C} {c : C}
    (ha : a.Valid) (hc : (lift e a).AvailableAtEdge e c) :
    ∃ b : EdgeAssignment H C, b.Valid ∧
      ∀ f, ((lift e a).fill e c).color f = some (b.color f) := by
  have hlift : (lift e a).Valid := lift_valid e ha
  have hfill : ((lift e a).fill e c).Valid :=
    PartialEdgeAssignment.fill_valid hlift hc
  have hcomplete := fill_lift_complete e a c
  let b := ((lift e a).fill e c).toEdgeAssignment hcomplete
  exact ⟨b, PartialEdgeAssignment.toEdgeAssignment_valid hcomplete hfill,
    fun f ↦ PartialEdgeAssignment.color_toEdgeAssignment _ hcomplete f⟩

end Decidable

end DeletionBridge

end TotalColoring
