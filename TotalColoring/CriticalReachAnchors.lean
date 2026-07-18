import TotalColoring.CriticalGlobalMaximal

/-!
# Conditional three-anchor reach comparison

This module isolates the finite reachability argument used after a supplied
two-color carrier swap in the two-satellite (`q = 2`) envelope.  It does not
construct a carrier component, prove that a swap is valid or rainbow-safe,
select a strong-palette critical state, or extract the paired-hole envelope.

The palette-generic layer proves three lower-bound interfaces.  Three distinct
reachable vertices suffice; two distinct dependencies out of the root supply
such vertices; and a two-step dependency chain does the same when its terminal
does not return to the root.  The oriented-state wrappers use the unique hole
to rule out that return automatically.  Finally, a numerical comparison lemma
shows that a target with at least three anchors has reach-card exactly three,
and remains globally maximal, when compared with a globally maximal source of
reach-card three.

These statements are deliberately conditional.  In particular, they neither
formalize the six role-specific swap analyses nor assert a `D + 1` palette
theorem; the lower-bound layer is generic in the color type, while the final
comparison reuses the existing `OrientedOneHoleState` interface.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {C : Type v}

/-- Three supplied, pairwise distinct reachable anchors force reach-card at
least three. -/
theorem three_le_card_centerReachableFinset_of_three_reachable
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {center root first second third : V}
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirst : a.CenterReachable J center root first)
    (hsecond : a.CenterReachable J center root second)
    (hthird : a.CenterReachable J center root third) :
    3 ≤ (a.centerReachableFinset J center root).card := by
  classical
  let anchors : Finset V := {first, second, third}
  have hsecondNot : second ∉ ({third} : Finset V) := by
    simpa using hsecondThird
  have hfirstNot : first ∉ ({second, third} : Finset V) := by
    simp [hfirstSecond, hfirstThird]
  have hanchorsCard : anchors.card = 3 := by
    rw [show anchors = insert first {second, third} by rfl,
      Finset.card_insert_of_notMem hfirstNot,
      Finset.card_insert_of_notMem hsecondNot]
    simp
  have hanchorsSub :
      anchors ⊆ a.centerReachableFinset J center root := by
    intro vertex hvertex
    simp only [anchors, Finset.mem_insert, Finset.mem_singleton] at hvertex
    rcases hvertex with hvertex | hvertex | hvertex
    · subst vertex
      exact (mem_centerReachableFinset_iff a J center root first).2 hfirst
    · subst vertex
      exact (mem_centerReachableFinset_iff a J center root second).2 hsecond
    · subst vertex
      exact (mem_centerReachableFinset_iff a J center root third).2 hthird
  rw [← hanchorsCard]
  exact Finset.card_le_card hanchorsSub

/-- Two distinct direct dependency targets out of the root, together with the
root itself, force reach-card at least three. -/
theorem three_le_card_centerReachableFinset_of_two_root_dependencies
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {center root first second : V}
    (hfirstSecond : first ≠ second)
    (hfirst : a.CenterDependency J center root first)
    (hsecond : a.CenterDependency J center root second) :
    3 ≤ (a.centerReachableFinset J center root).card := by
  have hrootFirst : root ≠ first := by
    intro h
    subst first
    exact a.centerDependency_irrefl J center root hfirst
  have hrootSecond : root ≠ second := by
    intro h
    subst second
    exact a.centerDependency_irrefl J center root hsecond
  apply a.three_le_card_centerReachableFinset_of_three_reachable J
    hrootFirst hrootSecond hfirstSecond
  · exact centerReachable_refl a J center root
  · exact centerReachable_tail (centerReachable_refl a J center root) hfirst
  · exact centerReachable_tail (centerReachable_refl a J center root) hsecond

/-- A dependency from the root followed by one more dependency forces three
reachable anchors, provided the terminal does not return to the root. -/
theorem three_le_card_centerReachableFinset_of_root_dependency_chain
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {center root middle terminal : V}
    (hrootTerminal : root ≠ terminal)
    (hfirst : a.CenterDependency J center root middle)
    (hsecond : a.CenterDependency J center middle terminal) :
    3 ≤ (a.centerReachableFinset J center root).card := by
  have hrootMiddle : root ≠ middle := by
    intro h
    subst middle
    exact a.centerDependency_irrefl J center root hfirst
  have hmiddleTerminal : middle ≠ terminal := by
    intro h
    subst terminal
    exact a.centerDependency_irrefl J center middle hsecond
  have hmiddleReach : a.CenterReachable J center root middle :=
    centerReachable_tail (centerReachable_refl a J center root) hfirst
  apply a.three_le_card_centerReachableFinset_of_three_reachable J
    hrootMiddle hrootTerminal hmiddleTerminal
  · exact centerReachable_refl a J center root
  · exact hmiddleReach
  · exact centerReachable_tail hmiddleReach hsecond

end PartialEdgeAssignment

namespace OrientedOneHoleState

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}

/-- State-level form of the three-explicit-anchor lower bound.  This is the
interface for a comparison state in which three old reachable vertices are
supplied directly. -/
theorem three_le_canonicalReachCard_of_three_reachable
    (state : OrientedOneHoleState D H J) {first second third : V}
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfirst : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf first)
    (hsecond : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf second)
    (hthird : state.assignment.CenterReachable
      (distinguishedEdgeSet H J) state.center state.root.leaf third) :
    3 ≤ state.canonicalReachCard := by
  exact state.assignment.three_le_card_centerReachableFinset_of_three_reachable
    (distinguishedEdgeSet H J) hfirstSecond hfirstThird hsecondThird
    hfirst hsecond hthird

/-- State-level form of the two-direct-anchor lower bound. -/
theorem three_le_canonicalReachCard_of_two_root_dependencies
    (state : OrientedOneHoleState D H J) {first second : V}
    (hfirstSecond : first ≠ second)
    (hfirst : state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center state.root.leaf first)
    (hsecond : state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center state.root.leaf second) :
    3 ≤ state.canonicalReachCard := by
  exact state.assignment.three_le_card_centerReachableFinset_of_two_root_dependencies
    (distinguishedEdgeSet H J) hfirstSecond hfirst hsecond

/-- In an oriented one-hole state, the unique hole excludes a dependency back
into the root, so a supplied two-step chain always gives three anchors. -/
theorem three_le_canonicalReachCard_of_root_dependency_chain
    (state : OrientedOneHoleState D H J) {middle terminal : V}
    (hfirst : state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center state.root.leaf middle)
    (hsecond : state.assignment.CenterDependency
      (distinguishedEdgeSet H J) state.center middle terminal) :
    3 ≤ state.canonicalReachCard := by
  have hrootTerminal : state.root.leaf ≠ terminal := by
    intro h
    subst terminal
    exact PartialEdgeAssignment.centerDependency_target_ne_root_of_oneHoleAt
      state.root.endpoints state.oneHole hsecond
  exact state.assignment.three_le_card_centerReachableFinset_of_root_dependency_chain
    (distinguishedEdgeSet H J) hrootTerminal hfirst hsecond

omit [DecidableEq V] in
/-- Global reach-card maximality transfers to any state with the same
canonical reach-card. -/
theorem IsGloballyReachCardMaximal.of_canonicalReachCard_eq
    {source target : OrientedOneHoleState D H J}
    (hsource : source.IsGloballyReachCardMaximal)
    (hcard : target.canonicalReachCard = source.canonicalReachCard) :
    target.IsGloballyReachCardMaximal := by
  intro candidate
  calc
    candidate.canonicalReachCard ≤ source.canonicalReachCard := hsource candidate
    _ = target.canonicalReachCard := hcard.symm

omit [DecidableEq V] in
/-- The numerical comparison interface used by each conditional carrier-swap
case: a target with three supplied anchors must have exact reach-card three and
remain globally maximal when the source is globally maximal of card three. -/
theorem comparison_eq_three_and_globallyMaximal
    (source target : OrientedOneHoleState D H J)
    (hsourceMaximal : source.IsGloballyReachCardMaximal)
    (hsourceCard : source.canonicalReachCard = 3)
    (htargetLower : 3 ≤ target.canonicalReachCard) :
    target.canonicalReachCard = 3 ∧
      target.IsGloballyReachCardMaximal := by
  have htargetUpper : target.canonicalReachCard ≤ 3 := by
    calc
      target.canonicalReachCard ≤ source.canonicalReachCard :=
        hsourceMaximal target
      _ = 3 := hsourceCard
  have htargetCard : target.canonicalReachCard = 3 :=
    Nat.le_antisymm htargetUpper htargetLower
  refine ⟨htargetCard, ?_⟩
  apply hsourceMaximal.of_canonicalReachCard_eq
  exact htargetCard.trans hsourceCard.symm

end OrientedOneHoleState

end TotalColoring
