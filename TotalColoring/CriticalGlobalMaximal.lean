import TotalColoring.CriticalReachableCount
import Mathlib.Data.Nat.Find

/-!
# Global maximality of the canonical reachable fan

This module packages the data over which a later extremal recentering argument
may maximize.  An `OrientedOneHoleState` consists of a valid partial assignment,
an explicitly oriented root edge outside the distinguished set, one hole at
that root, and the rainbow condition on the distinguished set.  Its canonical
reachable finset is the full center-dependency reachable set from the root
leaf, not a chosen linear fan path.

Global maximality below compares the cardinality of that canonical finset over
all such assignments, centers, and root orientations for the fixed `H`, `J`,
and `D`.  The maximizing state itself is retained as a witness.  In particular,
equal reachable cardinalities are never used to identify states.

The existence proof is conditional on the supplied outside-edge-minimal
noncolorable member.  Its only finiteness input is that every reachable finset
is contained in the finite vertex universe.
-/

namespace TotalColoring

universe u

/-- A valid rainbow one-hole state with an explicitly oriented root outside
the distinguished set. -/
structure OrientedOneHoleState {V : Type u} (D : ℕ) (H : SimpleGraph V)
    (J : Finset (Sym2 V)) where
  assignment : PartialEdgeAssignment H (ExtensionPalette D)
  center : V
  root : CenterSpoke H center
  rootOutside : root.edge ∉ distinguishedEdgeSet H J
  valid : assignment.Valid
  oneHole : assignment.OneHoleAt root.edge
  rainbow : assignment.RainbowOn (distinguishedEdgeSet H J)

namespace OrientedOneHoleState

variable {V : Type u} {D : ℕ} {H : SimpleGraph V}
variable {J : Finset (Sym2 V)}

/-- The canonical full center-dependency reachable finset of an oriented
one-hole state. -/
noncomputable def canonicalReachableFinset [Fintype V]
    (state : OrientedOneHoleState D H J) : Finset V :=
  state.assignment.centerReachableFinset (distinguishedEdgeSet H J)
    state.center state.root.leaf

/-- The cardinality maximized by the global extremal choice. -/
noncomputable def canonicalReachCard [Fintype V]
    (state : OrientedOneHoleState D H J) : ℕ :=
  state.canonicalReachableFinset.card

/-- A state is globally reach-card maximal when every oriented valid rainbow
one-hole state for the same fixed data has no larger canonical reachable set. -/
def IsGloballyReachCardMaximal [Fintype V]
    (state : OrientedOneHoleState D H J) : Prop :=
  ∀ other : OrientedOneHoleState D H J,
    other.canonicalReachCard ≤ state.canonicalReachCard

/-- The canonical reach-card is bounded by the finite vertex universe. -/
theorem canonicalReachCard_le_card_vertices [Fintype V]
    (state : OrientedOneHoleState D H J) :
    state.canonicalReachCard ≤ Fintype.card V := by
  exact Finset.card_le_univ state.canonicalReachableFinset

/-- Global reach-card maximality forbids a strict inclusion of the current
canonical reachable finset into that of any other oriented one-hole state. -/
theorem IsGloballyReachCardMaximal.not_ssubset_canonicalReachableFinset
    [Fintype V]
    {state : OrientedOneHoleState D H J}
    (hmaximal : state.IsGloballyReachCardMaximal)
    (other : OrientedOneHoleState D H J) :
    ¬state.canonicalReachableFinset ⊂ other.canonicalReachableFinset := by
  intro hstrict
  have hcardStrict : state.canonicalReachCard < other.canonicalReachCard := by
    simpa [canonicalReachCard] using Finset.card_lt_card hstrict
  exact (Nat.not_lt_of_ge (hmaximal other)) hcardStrict

end OrientedOneHoleState

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A supplied outside-edge-minimal noncolorable member admits at least one
oriented valid rainbow one-hole state.  The blocked deletion state supplies
the assignment; surjectivity of `Sym2.mk` supplies an orientation of its
outside root edge. -/
theorem exists_orientedOneHoleState
    (h : IsOutsideEdgeMinimalNoncolorable D H J) :
    Nonempty (OrientedOneHoleState D H J) := by
  rcases h.exists_outside_edge with ⟨e, heJ⟩
  rcases h.exists_blocked_oneHoleState e heJ with
    ⟨assignment, hvalid, honeHole, hrainbow, _hblocked⟩
  rcases Sym2.mk_surjective (e : Sym2 V) with
    ⟨⟨center, leaf⟩, hends⟩
  let root : CenterSpoke H center :=
    {
      leaf := leaf
      edge := e
      endpoints := hends.symm
    }
  refine ⟨{
    assignment := assignment
    center := center
    root := root
    rootOutside := ?_
    valid := hvalid
    oneHole := honeHole
    rainbow := hrainbow
  }⟩
  simpa [root, distinguishedEdgeSet] using heJ

/-- Every supplied outside-edge-minimal noncolorable member admits a globally
canonical-reach-card-maximal oriented state.  The maximum is taken over all
valid rainbow one-hole assignments and all outside root orientations for the
fixed `H`, `J`, and `D`.

The proof maximizes the realized natural-number cards below
`Fintype.card V`; it retains a state realizing the greatest card and makes no
claim that another state with the same card is equal to it. -/
theorem exists_globallyReachCardMaximal_orientedOneHoleState
    (h : IsOutsideEdgeMinimalNoncolorable D H J) :
    ∃ state : OrientedOneHoleState D H J,
      state.IsGloballyReachCardMaximal := by
  classical
  rcases h.exists_orientedOneHoleState with ⟨initial⟩
  let Realized : ℕ → Prop := fun k ↦
    ∃ state : OrientedOneHoleState D H J,
      state.canonicalReachCard = k
  have hinitialRealized : Realized initial.canonicalReachCard :=
    ⟨initial, rfl⟩
  have hgreatestRealized :
      Realized (Nat.findGreatest Realized (Fintype.card V)) :=
    Nat.findGreatest_spec initial.canonicalReachCard_le_card_vertices
      hinitialRealized
  rcases hgreatestRealized with ⟨maximal, hmaximalCard⟩
  refine ⟨maximal, ?_⟩
  intro other
  rw [hmaximalCard]
  exact Nat.le_findGreatest other.canonicalReachCard_le_card_vertices
    (⟨other, rfl⟩ : Realized other.canonicalReachCard)

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
