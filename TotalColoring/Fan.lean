import Mathlib.Data.List.Cycle
import TotalColoring.Missing

/-!
# Ordered edge shifts

This module isolates the generic operation underlying a fan shift.  An
`EdgeShiftSequence` is a nonempty finite list of distinct edges.  Shifting a
partial coloring along it makes each listed edge pull the old color of its
cyclic successor; edges outside the list are unchanged.  Thus, when the first
listed edge is the unique hole, the usual noncyclic description is recovered:
every nonlast edge receives its successor's color and the last edge becomes
the unique hole.

No graph-theoretic fan or adjacency condition is built into the sequence.
Such conditions belong to later layers.  Properness is preserved here under
an explicit hypothesis covering every incidence touched by the shift, and
`J`-rainbowness is preserved here when the source permutation maps `J` back
into `J` (with the useful disjoint-sequence corollary stated separately).
-/

namespace TotalColoring

universe u v

/-- A finite ordered sequence of distinct edges on which colors may be
shifted.  Nonemptiness makes its first and last edges canonical. -/
structure EdgeShiftSequence {V : Type u} (G : SimpleGraph V) where
  edges : List G.edgeSet
  nonempty : edges ≠ []
  nodup : edges.Nodup

namespace EdgeShiftSequence

variable {V : Type u} {G : SimpleGraph V}

/-- The edge at which a shift starts. -/
def first (s : EdgeShiftSequence G) : G.edgeSet :=
  s.edges.head s.nonempty

/-- The edge at which a shift ends. -/
def last (s : EdgeShiftSequence G) : G.edgeSet :=
  s.edges.getLast s.nonempty

@[simp]
theorem first_mem (s : EdgeShiftSequence G) : s.first ∈ s.edges :=
  List.head_mem s.nonempty

@[simp]
theorem last_mem (s : EdgeShiftSequence G) : s.last ∈ s.edges :=
  List.getLast_mem s.nonempty

/-- The two-edge sequence used by one primitive hole move. -/
def pair (firstEdge secondEdge : G.edgeSet) (hne : firstEdge ≠ secondEdge) :
    EdgeShiftSequence G where
  edges := [firstEdge, secondEdge]
  nonempty := by simp
  nodup := by simp [hne]

@[simp]
theorem first_pair (firstEdge secondEdge : G.edgeSet)
    (hne : firstEdge ≠ secondEdge) :
    (pair firstEdge secondEdge hne).first = firstEdge :=
  rfl

@[simp]
theorem last_pair (firstEdge secondEdge : G.edgeSet)
    (hne : firstEdge ≠ secondEdge) :
    (pair firstEdge secondEdge hne).last = secondEdge := by
  simp [last, pair]

section Decidable

variable [DecidableEq G.edgeSet]

/-- The old edge whose color is pulled into `e` by the shift.  It is the
cyclic successor of `e` on the sequence and is `e` off the sequence. -/
def source (s : EdgeShiftSequence G) (e : G.edgeSet) : G.edgeSet :=
  if he : e ∈ s.edges then s.edges.next e he else e

/-- The inverse positional map to `source`: cyclic predecessor on the
sequence and identity off it. -/
def target (s : EdgeShiftSequence G) (e : G.edgeSet) : G.edgeSet :=
  if he : e ∈ s.edges then s.edges.prev e he else e

@[simp]
theorem source_of_mem (s : EdgeShiftSequence G) {e : G.edgeSet}
    (he : e ∈ s.edges) : s.source e = s.edges.next e he := by
  simp [source, he]

@[simp]
theorem source_of_not_mem (s : EdgeShiftSequence G) {e : G.edgeSet}
    (he : e ∉ s.edges) : s.source e = e := by
  simp [source, he]

@[simp]
theorem target_of_mem (s : EdgeShiftSequence G) {e : G.edgeSet}
    (he : e ∈ s.edges) : s.target e = s.edges.prev e he := by
  simp [target, he]

@[simp]
theorem target_of_not_mem (s : EdgeShiftSequence G) {e : G.edgeSet}
    (he : e ∉ s.edges) : s.target e = e := by
  simp [target, he]

@[simp]
theorem source_mem_iff (s : EdgeShiftSequence G) (e : G.edgeSet) :
    s.source e ∈ s.edges ↔ e ∈ s.edges := by
  by_cases he : e ∈ s.edges
  · simp [source, he, List.next_mem]
  · simp [source, he]

@[simp]
theorem target_mem_iff (s : EdgeShiftSequence G) (e : G.edgeSet) :
    s.target e ∈ s.edges ↔ e ∈ s.edges := by
  by_cases he : e ∈ s.edges
  · simp [target, he, List.prev_mem]
  · simp [target, he]

@[simp]
theorem source_target (s : EdgeShiftSequence G) (e : G.edgeSet) :
    s.source (s.target e) = e := by
  by_cases he : e ∈ s.edges
  · have hprev : s.edges.prev e he ∈ s.edges := List.prev_mem _ _ _
    simp only [target_of_mem s he, source_of_mem s hprev]
    exact List.next_prev s.edges s.nodup e he
  · have htarget : s.target e = e := target_of_not_mem s he
    rw [htarget, source_of_not_mem s he]

@[simp]
theorem target_source (s : EdgeShiftSequence G) (e : G.edgeSet) :
    s.target (s.source e) = e := by
  by_cases he : e ∈ s.edges
  · have hnext : s.edges.next e he ∈ s.edges := List.next_mem _ _ _
    simp only [source_of_mem s he, target_of_mem s hnext]
    exact List.prev_next s.edges s.nodup e he
  · have hsource : s.source e = e := source_of_not_mem s he
    rw [hsource, target_of_not_mem s he]

theorem source_injective (s : EdgeShiftSequence G) :
    Function.Injective s.source := by
  intro e f hef
  have := congrArg s.target hef
  simpa using this

theorem target_injective (s : EdgeShiftSequence G) :
    Function.Injective s.target := by
  intro e f hef
  have := congrArg s.source hef
  simpa using this

@[simp]
theorem source_last (s : EdgeShiftSequence G) : s.source s.last = s.first := by
  rw [source_of_mem s (last_mem s)]
  exact List.next_getLast_eq_head s.edges s.nonempty s.nodup

@[simp]
theorem target_first (s : EdgeShiftSequence G) : s.target s.first = s.last := by
  rw [target_of_mem s (first_mem s)]
  exact List.prev_head_eq_getLast s.edges s.nonempty

end Decidable

end EdgeShiftSequence

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

private theorem eq_of_color_eq {a b : PartialEdgeAssignment G C}
    (h : a.color = b.color) : a = b := by
  cases a
  cases b
  simpa using h

section MoveHole

variable [DecidableEq G.edgeSet]

/-- Move the color of `donor` into `hole` and leave `donor` uncolored.  The
operation itself does not assume that `hole` was uncolored or that `donor`
was colored; those facts are hypotheses of the corresponding relocation
theorem. -/
def moveHole (a : PartialEdgeAssignment G C) (hole donor : G.edgeSet) :
    PartialEdgeAssignment G C where
  color e := if e = hole then a.color donor else if e = donor then none else a.color e

@[simp]
theorem moveHole_color_hole (a : PartialEdgeAssignment G C)
    (hole donor : G.edgeSet) :
    (a.moveHole hole donor).color hole = a.color donor := by
  simp [moveHole]

@[simp]
theorem moveHole_color_donor (a : PartialEdgeAssignment G C)
    {hole donor : G.edgeSet} (hne : donor ≠ hole) :
    (a.moveHole hole donor).color donor = none := by
  simp [moveHole, hne]

@[simp]
theorem moveHole_color_of_ne (a : PartialEdgeAssignment G C)
    {hole donor e : G.edgeSet} (heh : e ≠ hole) (hed : e ≠ donor) :
    (a.moveHole hole donor).color e = a.color e := by
  simp [moveHole, heh, hed]

/-- The donor's color is available at the hole after exempting the donor
itself, which will be uncolored by `moveHole`.  This is the exact local seam
needed for properness at the newly colored hole. -/
def DonorAvailableAtHoleExcept (a : PartialEdgeAssignment G C)
    (hole donor : G.edgeSet) : Prop :=
  ∀ {c : C}, a.color donor = some c → ∀ f,
    G.lineGraph.Adj hole f → f ≠ donor → a.color f ≠ some c

/-- Moving a distinct donor into a unique hole relocates that unique hole
exactly to the donor. -/
theorem oneHoleAt_moveHole {a : PartialEdgeAssignment G C}
    {hole donor : G.edgeSet} (hhole : a.OneHoleAt hole)
    (hne : donor ≠ hole) :
    (a.moveHole hole donor).OneHoleAt donor := by
  intro e
  by_cases heh : e = hole
  · subst e
    have hcolored : a.color donor ≠ none := by
      intro hnone
      exact hne ((hhole donor).mp hnone)
    simp [moveHole, hcolored, Ne.symm hne]
  · by_cases hed : e = donor
    · subst e
      simp [moveHole, hne]
    · rw [moveHole_color_of_ne a heh hed]
      exact (hhole e).trans (iff_of_false (fun h ↦ heh h)
        (fun h ↦ hed h))

/-- A genuine move to a distinct donor necessarily leaves an uncolored edge,
so the result is not complete. -/
theorem not_complete_moveHole (a : PartialEdgeAssignment G C)
    {hole donor : G.edgeSet} (hne : donor ≠ hole) :
    ¬(a.moveHole hole donor).Complete := by
  intro hcomplete
  rcases hcomplete donor with ⟨c, hc⟩
  rw [moveHole_color_donor a hne] at hc
  exact Option.some_ne_none c hc.symm

/-- Properness is preserved when the original assignment is valid and the
donor color is absent at every edge adjacent to the hole except the donor
itself. -/
theorem valid_moveHole_of_availableExcept {a : PartialEdgeAssignment G C}
    {hole donor : G.edgeSet} (hvalid : a.Valid) (hne : donor ≠ hole)
    (havailable : a.DonorAvailableAtHoleExcept hole donor) :
    (a.moveHole hole donor).Valid := by
  intro e f c hef hec
  by_cases heh : e = hole
  · subst e
    have hdonorColor : a.color donor = some c := by
      simpa using hec
    by_cases hfd : f = donor
    · subst f
      simp [moveHole, hne]
    · have hfh : f ≠ hole := hef.ne'
      simpa [moveHole, hfh, hfd] using
        havailable hdonorColor f hef hfd
  · by_cases hed : e = donor
    · subst e
      simp [moveHole, hne] at hec
    · have hec' : a.color e = some c := by
        simpa [moveHole, heh, hed] using hec
      by_cases hfh : f = hole
      · subst f
        rw [moveHole_color_hole]
        intro hdonorColor
        exact (havailable hdonorColor e hef.symm hed) hec'
      · by_cases hfd : f = donor
        · subst f
          simp [moveHole, hne]
        · simpa [moveHole, hfh, hfd] using hvalid e f c hef hec'

/-- If both modified edges lie outside `J`, every distinguished color is
unchanged and the rainbow invariant is preserved. -/
theorem rainbowOn_moveHole_of_not_mem {a : PartialEdgeAssignment G C}
    {hole donor : G.edgeSet} {J : Set G.edgeSet}
    (hrainbow : a.RainbowOn J) (hholeJ : hole ∉ J) (hdonorJ : donor ∉ J) :
    (a.moveHole hole donor).RainbowOn J := by
  constructor
  · intro e he
    rcases hrainbow.1 e he with ⟨c, hc⟩
    exact ⟨c, by simpa [moveHole, ne_of_mem_of_not_mem he hholeJ,
      ne_of_mem_of_not_mem he hdonorJ] using hc⟩
  · intro e he f hf hef
    simpa [moveHole, ne_of_mem_of_not_mem he hholeJ,
      ne_of_mem_of_not_mem he hdonorJ,
      ne_of_mem_of_not_mem hf hholeJ,
      ne_of_mem_of_not_mem hf hdonorJ] using hrainbow.2 he hf hef

/-- The primitive move preserves all three one-hole invariants when their
independent local hypotheses are supplied. -/
theorem valid_oneHoleAt_rainbowOn_moveHole
    {a : PartialEdgeAssignment G C} {hole donor : G.edgeSet}
    {J : Set G.edgeSet} (hvalid : a.Valid) (hhole : a.OneHoleAt hole)
    (hrainbow : a.RainbowOn J) (hne : donor ≠ hole)
    (havailable : a.DonorAvailableAtHoleExcept hole donor)
    (hholeJ : hole ∉ J) (hdonorJ : donor ∉ J) :
    (a.moveHole hole donor).Valid ∧
      (a.moveHole hole donor).OneHoleAt donor ∧
      (a.moveHole hole donor).RainbowOn J :=
  ⟨valid_moveHole_of_availableExcept hvalid hne havailable,
    oneHoleAt_moveHole hhole hne,
    rainbowOn_moveHole_of_not_mem hrainbow hholeJ hdonorJ⟩

end MoveHole

section Shift

variable [DecidableEq G.edgeSet]

/-- Pull colors one position toward the first edge of the ordered sequence.
The positional map is a cyclic permutation; if the first edge is uncolored,
the value wrapped to the last edge is therefore exactly `none`. -/
def shiftAlong (a : PartialEdgeAssignment G C) (s : EdgeShiftSequence G) :
    PartialEdgeAssignment G C where
  color e := a.color (s.source e)

@[simp]
theorem shiftAlong_color (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (e : G.edgeSet) :
    (a.shiftAlong s).color e = a.color (s.source e) :=
  rfl

@[simp]
theorem shiftAlong_color_of_not_mem (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) {e : G.edgeSet} (he : e ∉ s.edges) :
    (a.shiftAlong s).color e = a.color e := by
  simp [EdgeShiftSequence.source_of_not_mem s he]

/-- Exact indexed color formula: every listed edge receives the old color at
the next cyclic position. -/
theorem shiftAlong_color_getElem (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (i : ℕ) (hi : i < s.edges.length) :
    (a.shiftAlong s).color s.edges[i] =
      a.color (s.edges[(i + 1) % s.edges.length]'(Nat.mod_lt _ (by
        exact lt_of_le_of_lt (Nat.zero_le i) hi))) := by
  rw [shiftAlong_color, EdgeShiftSequence.source_of_mem s (List.getElem_mem hi)]
  exact congrArg a.color (List.next_getElem s.edges s.nodup i hi)

/-- The last edge receives the old color of the first edge. -/
@[simp]
theorem shiftAlong_color_last (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) :
    (a.shiftAlong s).color s.last = a.color s.first := by
  rw [shiftAlong_color, EdgeShiftSequence.source_last]

/-- Rotating edge positions preserves completeness exactly. -/
theorem shiftAlong_complete_iff (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) :
    (a.shiftAlong s).Complete ↔ a.Complete := by
  constructor
  · intro h e
    rcases h (s.target e) with ⟨c, hc⟩
    exact ⟨c, by simpa using hc⟩
  · intro h e
    rcases h (s.source e) with ⟨c, hc⟩
    exact ⟨c, hc⟩

/-- Exact transport law for a unique hole under the source permutation. -/
theorem shiftAlong_oneHoleAt_target_iff (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (hole : G.edgeSet) :
    (a.shiftAlong s).OneHoleAt (s.target hole) ↔ a.OneHoleAt hole := by
  constructor
  · intro h e
    constructor
    · intro he
      have hshift : (a.shiftAlong s).color (s.target e) = none := by
        simpa using he
      have htargets : s.target e = s.target hole := (h (s.target e)).mp hshift
      exact EdgeShiftSequence.target_injective s htargets
    · intro he
      subst e
      have : (a.shiftAlong s).color (s.target hole) = none :=
        (h (s.target hole)).mpr rfl
      simpa using this
  · intro h e
    constructor
    · intro he
      have hsource : s.source e = hole := (h (s.source e)).mp (by simpa using he)
      apply EdgeShiftSequence.source_injective s
      simpa using hsource
    · intro he
      subst e
      simp [h hole]

/-- In the usual shift orientation, a unique hole at the first edge moves
exactly to the last edge. -/
theorem shiftAlong_oneHoleAt_last_iff (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) :
    (a.shiftAlong s).OneHoleAt s.last ↔ a.OneHoleAt s.first := by
  rw [← EdgeShiftSequence.target_first s]
  exact shiftAlong_oneHoleAt_target_iff a s s.first

/-- For a genuine hole, the two-edge sequence rotation is exactly the
primitive `moveHole` operation.  Without the hole hypothesis the two notions
differ at the donor: rotation wraps the old first value, whereas `moveHole`
always writes `none`. -/
theorem shiftAlong_pair_eq_moveHole (a : PartialEdgeAssignment G C)
    {hole donor : G.edgeSet} (hne : donor ≠ hole)
    (hhole : a.color hole = none) :
    a.shiftAlong (EdgeShiftSequence.pair hole donor (Ne.symm hne)) =
      a.moveHole hole donor := by
  apply eq_of_color_eq
  funext e
  by_cases heh : e = hole
  · subst e
    simp [shiftAlong, EdgeShiftSequence.source, EdgeShiftSequence.pair,
      moveHole]
  · by_cases hed : e = donor
    · subst e
      calc
        (a.shiftAlong (EdgeShiftSequence.pair hole donor (Ne.symm hne))).color donor =
            a.color hole := by
          simpa using shiftAlong_color_last a
            (EdgeShiftSequence.pair hole donor (Ne.symm hne))
        _ = none := hhole
        _ = (a.moveHole hole donor).color donor :=
          (moveHole_color_donor a hne).symm
    · simp [shiftAlong, EdgeShiftSequence.source, EdgeShiftSequence.pair,
        moveHole, heh, hed]

/-- The explicit local properness obligation for a shift.  Only incidences
touching a listed edge are included; incidences between two unlisted edges
remain governed by the original coloring's validity. -/
def ShiftValidOnAffectedIncidences (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) : Prop :=
  ∀ {e}, e ∈ s.edges → ∀ {f c}, G.lineGraph.Adj e f →
    a.color (s.source e) = some c → a.color (s.source f) ≠ some c

/-- Assuming the original assignment is valid, the shifted assignment is
valid exactly when the explicit affected-incidence obligation holds. -/
theorem valid_shiftAlong_iff (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (hvalid : a.Valid) :
    (a.shiftAlong s).Valid ↔ a.ShiftValidOnAffectedIncidences s := by
  constructor
  · intro hshift e he f c hef hec
    exact hshift e f c hef hec
  · intro hlocal e f c hef hec
    by_cases he : e ∈ s.edges
    · exact hlocal he hef hec
    · by_cases hf : f ∈ s.edges
      · intro hfc
        exact (hlocal hf hef.symm hfc) hec
      · have hec' : a.color e = some c := by
          simpa [EdgeShiftSequence.source_of_not_mem s he] using hec
        simpa [EdgeShiftSequence.source_of_not_mem s hf] using
          hvalid e f c hef hec'

/-- A direct preservation form of `valid_shiftAlong_iff`. -/
theorem valid_shiftAlong_of_affected (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (hvalid : a.Valid)
    (hlocal : a.ShiftValidOnAffectedIncidences s) :
    (a.shiftAlong s).Valid :=
  (valid_shiftAlong_iff a s hvalid).2 hlocal

/-- The positional source of every distinguished edge remains distinguished.
This is the structural hypothesis needed to reuse an existing rainbow
assignment after a shift. -/
def ShiftSourceClosedOn (s : EdgeShiftSequence G) (J : Set G.edgeSet) : Prop :=
  ∀ {e}, e ∈ J → s.source e ∈ J

/-- A source-closed distinguished set remains rainbow under a shift. -/
theorem rainbowOn_shiftAlong_of_sourceClosed (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (J : Set G.edgeSet)
    (hrainbow : a.RainbowOn J) (hclosed : ShiftSourceClosedOn s J) :
    (a.shiftAlong s).RainbowOn J := by
  constructor
  · intro e he
    exact hrainbow.1 (s.source e) (hclosed he)
  · intro e he f hf hef
    exact hrainbow.2 (hclosed he) (hclosed hf)
      (fun h ↦ hef (EdgeShiftSequence.source_injective s h))

/-- If the shift sequence avoids `J`, every color on `J` is unchanged and
the rainbow invariant is preserved. -/
theorem rainbowOn_shiftAlong_of_disjoint (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (J : Set G.edgeSet)
    (hrainbow : a.RainbowOn J)
    (hdisjoint : ∀ {e}, e ∈ J → e ∉ s.edges) :
    (a.shiftAlong s).RainbowOn J := by
  apply rainbowOn_shiftAlong_of_sourceClosed a s J hrainbow
  intro e he
  simpa [EdgeShiftSequence.source_of_not_mem s (hdisjoint he)] using he

/-- Combined preservation theorem keeping the properness and rainbow seams
as two independent explicit hypotheses. -/
theorem valid_and_rainbowOn_shiftAlong (a : PartialEdgeAssignment G C)
    (s : EdgeShiftSequence G) (J : Set G.edgeSet)
    (hvalid : a.Valid) (hrainbow : a.RainbowOn J)
    (hlocal : a.ShiftValidOnAffectedIncidences s)
    (hclosed : ShiftSourceClosedOn s J) :
    (a.shiftAlong s).Valid ∧ (a.shiftAlong s).RainbowOn J :=
  ⟨valid_shiftAlong_of_affected a s hvalid hlocal,
    rainbowOn_shiftAlong_of_sourceClosed a s J hrainbow hclosed⟩

end Shift

end PartialEdgeAssignment

end TotalColoring
