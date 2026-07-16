import TotalColoring.OrderedFan
import TotalColoring.Fan

/-!
# Shifting a hole along an ordered fan

This module specializes the generic cyclic edge shift to a `LinearFanPath`.
The fan edges form the shift sequence in path order.  If the root edge is the
unique hole, the wrapped color at the terminal edge is therefore `none`, so
the cyclic operation is exactly the usual noncyclic fan shift.

The main point is properness.  It is not assumed as an extra fan condition: the
affected-incidence obligation is derived from consecutive `FanStep`s, the
common-center geometry, and validity of the old partial coloring.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment.LinearFanPath

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {a : PartialEdgeAssignment G C} {J : Set G.edgeSet} {center : V}

/-- The generic edge-shift sequence underlying a linear fan shift. -/
def shiftSequence (F : LinearFanPath a J center) : EdgeShiftSequence G where
  edges := F.edges
  nonempty := by
    intro hempty
    have := F.root_edge_mem_edges
    simp [hempty] at this
  nodup := F.nodup_edges

@[simp]
theorem shiftSequence_edges (F : LinearFanPath a J center) :
    F.shiftSequence.edges = F.edges :=
  rfl

@[simp]
theorem shiftSequence_first (F : LinearFanPath a J center) :
    F.shiftSequence.first = F.root.edge :=
  rfl

@[simp]
theorem shiftSequence_last (F : LinearFanPath a J center) :
    F.shiftSequence.last = F.terminal.edge := by
  simp [shiftSequence, EdgeShiftSequence.last, LinearFanPath.edges,
    LinearFanPath.terminal]

section Decidable

variable [DecidableEq G.edgeSet]

/-- The fan shift is the generic cyclic shift along the path's edge list. -/
def shift (F : LinearFanPath a J center) : PartialEdgeAssignment G C :=
  a.shiftAlong F.shiftSequence

@[simp]
theorem shift_color (F : LinearFanPath a J center) (e : G.edgeSet) :
    F.shift.color e = a.color (F.shiftSequence.source e) :=
  rfl

/-- Edges outside the fan keep their colors exactly. -/
theorem shift_color_of_not_mem (F : LinearFanPath a J center)
    {e : G.edgeSet} (he : e ∉ F.edges) : F.shift.color e = a.color e := by
  exact PartialEdgeAssignment.shiftAlong_color_of_not_mem a F.shiftSequence he

/-- Exact indexed color transport along the fan edge list. -/
theorem shift_color_getElem (F : LinearFanPath a J center)
    (i : ℕ) (hi : i < F.edges.length) :
    F.shift.color F.edges[i] =
      a.color (F.edges[(i + 1) % F.edges.length]'(Nat.mod_lt _ (by
        exact lt_of_le_of_lt (Nat.zero_le i) hi))) := by
  exact PartialEdgeAssignment.shiftAlong_color_getElem a F.shiftSequence i hi

/-- The positional source of an edge incident with the fan center is again
incident with the center. -/
private theorem source_incident_center (F : LinearFanPath a J center)
    {e : G.edgeSet} (he : Incident center e) :
    Incident center (F.shiftSequence.source e) := by
  by_cases hmem : e ∈ F.edges
  · have hsource : F.shiftSequence.source e ∈ F.edges := by
      simpa using (EdgeShiftSequence.source_mem_iff F.shiftSequence e).2 hmem
    rcases List.mem_map.mp hsource with ⟨p, hp, hedge⟩
    rw [← hedge]
    exact p.center_incident
  · simpa [EdgeShiftSequence.source_of_not_mem F.shiftSequence hmem] using he

/-- The positional target of an edge incident with the fan center is again
incident with the center. -/
private theorem target_incident_center (F : LinearFanPath a J center)
    {e : G.edgeSet} (he : Incident center e) :
    Incident center (F.shiftSequence.target e) := by
  by_cases hmem : e ∈ F.edges
  · have htarget : F.shiftSequence.target e ∈ F.edges := by
      simpa using (EdgeShiftSequence.target_mem_iff F.shiftSequence e).2 hmem
    rcases List.mem_map.mp htarget with ⟨p, hp, hedge⟩
    rw [← hedge]
    exact p.center_incident
  · simpa [EdgeShiftSequence.target_of_not_mem F.shiftSequence hmem] using he

/-- The fan chain itself supplies every local properness obligation touched
by the cyclic shift.  The final edge is harmless because its source is the
uncolored root. -/
theorem shiftValidOnAffectedIncidences (F : LinearFanPath a J center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge) :
    a.ShiftValidOnAffectedIncidences F.shiftSequence := by
  intro e he f c hef hec
  change e ∈ F.edges at he
  obtain ⟨i, hi, hie⟩ := List.getElem_of_mem he
  subst e
  change G.lineGraph.Adj F.edges[i] f at hef
  change a.color (F.shiftSequence.source F.edges[i]) = some c at hec
  have hiSpokes : i < F.spokes.length := by
    simpa [LinearFanPath.edges] using hi
  by_cases hnext : i + 1 < F.spokes.length
  · let p : CenterSpoke G center := F.spokes[i]
    let q : CenterSpoke G center := F.spokes[i + 1]
    have hpedge : F.edges[i] = p.edge := by
      simp [LinearFanPath.edges, p]
    have hstep : a.FanStep J p q := by
      exact F.chain.getElem i hnext
    have hsource :
        F.shiftSequence.source F.edges[i] = q.edge := by
      rw [EdgeShiftSequence.source_of_mem F.shiftSequence
        (List.getElem_mem hi)]
      change F.edges.next F.edges[i] (List.getElem_mem hi) = q.edge
      rw [List.next_getElem F.edges F.nodup_edges i hi]
      simp [LinearFanPath.edges, q, Nat.mod_eq_of_lt hnext]
    have hqcolor : a.color q.edge = some c := by
      rw [hsource] at hec
      exact hec
    rcases hstep with ⟨d, hqJ, hdcolor, hmissing⟩
    have hdc : d = c := Option.some.inj (hdcolor.symm.trans hqcolor)
    subst d
    by_cases hfmem : f ∈ F.edges
    · have hsourcefmem : F.shiftSequence.source f ∈ F.edges := by
        simpa using
          (EdgeShiftSequence.source_mem_iff F.shiftSequence f).2 hfmem
      have hsourcene : q.edge ≠ F.shiftSequence.source f := by
        intro heq
        have hsources :
            F.shiftSequence.source F.edges[i] =
              F.shiftSequence.source f := hsource.trans heq
        have hef_eq : F.edges[i] = f :=
          F.shiftSequence.source_injective hsources
        exact hef.ne hef_eq
      rcases List.mem_map.mp hsourcefmem with ⟨r, hr, hrEdge⟩
      have hqr : q ≠ r := by
        apply CenterSpoke.ne_iff_edge_ne.mpr
        simpa [hrEdge] using hsourcene
      have hqadj : G.lineGraph.Adj q.edge (F.shiftSequence.source f) := by
        rw [← hrEdge]
        exact q.lineGraph_adj hqr
      exact hvalid q.edge (F.shiftSequence.source f) c hqadj hqcolor
    · have hsourcef : F.shiftSequence.source f = f :=
        EdgeShiftSequence.source_of_not_mem F.shiftSequence hfmem
      rw [hsourcef]
      have hefp : G.lineGraph.Adj p.edge f := by simpa [hpedge] using hef
      rcases SimpleGraph.lineGraph_adj_iff_exists.mp hefp with
        ⟨hEdgeNe, x, hxp, hxf⟩
      rcases p.incident_iff.mp hxp with hxcenter | hxleaf
      · have hqf_ne : q.edge ≠ f := by
          intro hqf
          apply hfmem
          rw [← hqf]
          exact List.mem_map.mpr
            ⟨q, List.getElem_mem hnext, rfl⟩
        have hqf : G.lineGraph.Adj q.edge f := by
          apply SimpleGraph.lineGraph_adj_iff_exists.mpr
          exact ⟨hqf_ne, center, q.center_incident, by simpa [hxcenter] using hxf⟩
        exact hvalid q.edge f c hqf hqcolor
      · exact hmissing f (by simpa [hxleaf] using hxf)
  · have hilast : i + 1 = F.spokes.length := by omega
    have hsource :
        F.shiftSequence.source F.edges[i] = F.root.edge := by
      rw [EdgeShiftSequence.source_of_mem F.shiftSequence
        (List.getElem_mem hi)]
      change F.edges.next F.edges[i] (List.getElem_mem hi) = F.root.edge
      rw [List.next_getElem F.edges F.nodup_edges i hi]
      simp [LinearFanPath.edges, hilast, LinearFanPath.spokes]
    have hrootnone : a.color F.root.edge = none :=
      (hhole F.root.edge).2 rfl
    rw [hsource, hrootnone] at hec
    simp at hec

/-- Shifting along a valid fan preserves validity. -/
theorem valid_shift (F : LinearFanPath a J center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge) :
    F.shift.Valid := by
  exact PartialEdgeAssignment.valid_shiftAlong_of_affected a F.shiftSequence
    hvalid (F.shiftValidOnAffectedIncidences hvalid hhole)

/-- The unique hole moves from the root edge to the terminal edge. -/
theorem oneHoleAt_shift (F : LinearFanPath a J center)
    (hhole : a.OneHoleAt F.root.edge) :
    F.shift.OneHoleAt F.terminal.edge := by
  change (a.shiftAlong F.shiftSequence).OneHoleAt F.terminal.edge
  rw [← F.shiftSequence_last]
  exact (PartialEdgeAssignment.shiftAlong_oneHoleAt_last_iff
    a F.shiftSequence).2 (by simpa using hhole)

/-- Since all fan edges avoid `J`, a fan shift preserves the distinguished
rainbow condition. -/
theorem rainbowOn_shift (F : LinearFanPath a J center)
    (hrainbow : a.RainbowOn J) : F.shift.RainbowOn J := by
  apply PartialEdgeAssignment.rainbowOn_shiftAlong_of_disjoint
    a F.shiftSequence J hrainbow
  intro e heJ heFan
  exact F.edge_not_mem heFan heJ

/-- Combined fan-shift preservation theorem. -/
theorem valid_oneHoleAt_rainbowOn_shift (F : LinearFanPath a J center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn J) :
    F.shift.Valid ∧ F.shift.OneHoleAt F.terminal.edge ∧
      F.shift.RainbowOn J :=
  ⟨F.valid_shift hvalid hhole, F.oneHoleAt_shift hhole,
    F.rainbowOn_shift hrainbow⟩

/-- The set of colors missing at the common center is invariant under a fan
shift. -/
theorem missingAt_center_shift_iff (F : LinearFanPath a J center) (c : C) :
    F.shift.MissingAt center c ↔ a.MissingAt center c := by
  constructor
  · intro hshift e he
    have htarget := F.target_incident_center he
    have hne := hshift (F.shiftSequence.target e) htarget
    simpa using hne
  · intro hold e he
    exact hold (F.shiftSequence.source e) (F.source_incident_center he)

/-- Every color missing at the original terminal leaf is still missing there
after the fan shift. -/
theorem missingAt_terminal_shift (F : LinearFanPath a J center)
    (hhole : a.OneHoleAt F.root.edge) {c : C}
    (hmissing : a.MissingAt F.terminal.leaf c) :
    F.shift.MissingAt F.terminal.leaf c := by
  intro e heInc
  by_cases heFan : e ∈ F.edges
  · rcases List.mem_map.mp heFan with ⟨p, hp, hpEdge⟩
    have hpterminal : p = F.terminal := by
      by_contra hpne
      exact p.not_incident_leaf_of_ne hpne (by simpa [hpEdge] using heInc)
    have heTerminal : e = F.terminal.edge := by
      simpa [hpterminal] using hpEdge.symm
    have hrootnone : a.color F.root.edge = none :=
      (hhole F.root.edge).2 rfl
    rw [heTerminal, ← F.shiftSequence_last]
    change (a.shiftAlong F.shiftSequence).color F.shiftSequence.last ≠ some c
    rw [
      PartialEdgeAssignment.shiftAlong_color_last, F.shiftSequence_first,
      hrootnone]
    simp
  · rw [F.shift_color_of_not_mem heFan]
    exact hmissing e heInc

end Decidable

end PartialEdgeAssignment.LinearFanPath

end TotalColoring
