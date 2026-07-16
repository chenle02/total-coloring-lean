import TotalColoring.RainbowSwap

/-!
# Physical two-color Kempe components

This module realizes the abstract swap set from `RainbowSwap` through the
line graph induced by two colors.  Reachability is the reflexive-transitive
closure of adjacent steps whose two endpoint edges both have color `α` or
`β`.  A supported root gives its genuine connected component; an unsupported
root deliberately gives the empty set.

The component construction itself is purely graph-theoretic.  Properness of
the original assignment is used only when the existing swap theorem is
invoked.  Distinguished-set safety remains a separate, exact condition: a
supported-root physical Kempe component preserves `J`-rainbowness exactly
when it satisfies `SwapCompatibleOn`; the unsupported-root empty case is the
identity.
-/

namespace TotalColoring

universe u v

namespace EdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- An edge has one of the two colors supporting a Kempe component. -/
def TwoColorSupported (a : EdgeAssignment G C) (α β : C)
    (e : G.edgeSet) : Prop :=
  a.color e = α ∨ a.color e = β

/-- One physical step in the line graph induced by the `α`- and `β`-colored
edges.  The definition is symmetric and does not assume that `a` is proper. -/
def TwoColorStep (a : EdgeAssignment G C) (α β : C)
    (e f : G.edgeSet) : Prop :=
  G.lineGraph.Adj e f ∧
    a.TwoColorSupported α β e ∧ a.TwoColorSupported α β f

theorem twoColorStep_symm (a : EdgeAssignment G C) (α β : C)
    {e f : G.edgeSet} (hef : a.TwoColorStep α β e f) :
    a.TwoColorStep α β f e := by
  rcases hef with ⟨hadj, he, hf⟩
  exact ⟨hadj.symm, hf, he⟩

/-- Reachability by finitely many physical `α`-`β` steps in the line graph.
The explicit root-support conjunct prevents an edge of some third color from
becoming a spurious singleton component by reflexivity alone. -/
def KempeReachable (a : EdgeAssignment G C) (α β : C)
    (root e : G.edgeSet) : Prop :=
  a.TwoColorSupported α β root ∧
    Relation.ReflTransGen (a.TwoColorStep α β) root e

/-- The physical two-color Kempe component containing `root` when `root` is
supported, and the empty set otherwise. -/
def kempeComponent (a : EdgeAssignment G C) (α β : C)
    (root : G.edgeSet) : Set G.edgeSet :=
  {e | a.KempeReachable α β root e}

@[simp]
theorem root_mem_kempeComponent_iff (a : EdgeAssignment G C) (α β : C)
    (root : G.edgeSet) :
    root ∈ a.kempeComponent α β root ↔ a.TwoColorSupported α β root := by
  constructor
  · exact fun h ↦ h.1
  · exact fun h ↦ ⟨h, Relation.ReflTransGen.refl⟩

/-- A physical step cannot cross the boundary of the supported-root component;
the statement is vacuous for the empty unsupported-root sentinel. -/
theorem mem_kempeComponent_iff_of_twoColorStep (a : EdgeAssignment G C)
    (α β : C) (root : G.edgeSet) {e f : G.edgeSet}
    (hef : a.TwoColorStep α β e f) :
    e ∈ a.kempeComponent α β root ↔ f ∈ a.kempeComponent α β root := by
  constructor
  · rintro ⟨hroot, he⟩
    exact ⟨hroot, Relation.ReflTransGen.tail he hef⟩
  · rintro ⟨hroot, hf⟩
    exact ⟨hroot,
      Relation.ReflTransGen.tail hf (a.twoColorStep_symm α β hef)⟩

/-- Every supported-root component, and also the empty unsupported-root
sentinel, supplies the boundary-closure hypothesis required by
`valid_swapOn_of_boundaryClosed`. -/
theorem kempeComponent_twoColorBoundaryClosed (a : EdgeAssignment G C)
    (α β : C) (root : G.edgeSet) :
    a.TwoColorBoundaryClosed α β (a.kempeComponent α β root) := by
  intro e f hef heα hfβ
  apply a.mem_kempeComponent_iff_of_twoColorStep α β root
  exact ⟨hef, Or.inl heα, Or.inr hfβ⟩

/-- Swapping the two colors on the supported-root component preserves a proper
edge coloring; for an unsupported root this is the identity swap on the empty
set. -/
theorem valid_swapOn_kempeComponent [DecidableEq C]
    (a : EdgeAssignment G C) (α β : C) (root : G.edgeSet)
    [DecidablePred (· ∈ a.kempeComponent α β root)] (hvalid : a.Valid) :
    (a.swapOn α β (a.kempeComponent α β root)).Valid :=
  valid_swapOn_of_boundaryClosed a (a.kempeComponent α β root) hvalid
    (a.kempeComponent_twoColorBoundaryClosed α β root)

/-- Exact combined physical-swap theorem.

For a proper assignment and a rainbow distinguished set, the supported-root
physical Kempe swap is both proper and `J`-rainbow exactly when the unique
`α`- and `β`-colored members of `J` (when both exist) lie on the same side of
the component.  For an unsupported root the set is empty and the same iff is
the identity case.  The right-hand side is the carrier-free formulation of
that exact condition. -/
theorem valid_and_rainbowOn_swapOn_kempeComponent_iff [DecidableEq C]
    (a : EdgeAssignment G C) (J : Set G.edgeSet) {α β : C}
    (root : G.edgeSet) [DecidablePred (· ∈ a.kempeComponent α β root)]
    (hvalid : a.Valid) (hrainbow : a.RainbowOn J) (hαβ : α ≠ β) :
    ((a.swapOn α β (a.kempeComponent α β root)).Valid ∧
        (a.swapOn α β (a.kempeComponent α β root)).RainbowOn J) ↔
      a.SwapCompatibleOn J α β (a.kempeComponent α β root) := by
  constructor
  · intro hswap
    exact (rainbowOn_swapOn_iff a J (a.kempeComponent α β root)
      hrainbow hαβ).1 hswap.2
  · intro hcompatible
    exact ⟨a.valid_swapOn_kempeComponent α β root hvalid,
      (rainbowOn_swapOn_iff a J (a.kempeComponent α β root)
        hrainbow hαβ).2 hcompatible⟩

/-- Common safe case: if either swap color is unused on `J`, the
component-or-empty swap preserves properness and `J`-rainbowness. -/
theorem valid_and_rainbowOn_swapOn_kempeComponent_of_one_unused
    [DecidableEq C] (a : EdgeAssignment G C) (J : Set G.edgeSet) {α β : C}
    (root : G.edgeSet) [DecidablePred (· ∈ a.kempeComponent α β root)]
    (hvalid : a.Valid) (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (hunused : a.ColorUnusedOn J α ∨ a.ColorUnusedOn J β) :
    (a.swapOn α β (a.kempeComponent α β root)).Valid ∧
      (a.swapOn α β (a.kempeComponent α β root)).RainbowOn J :=
  ⟨a.valid_swapOn_kempeComponent α β root hvalid,
    rainbowOn_swapOn_of_one_unused a J (a.kempeComponent α β root)
      hrainbow hαβ hunused⟩

end EdgeAssignment

end TotalColoring
