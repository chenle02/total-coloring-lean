import TotalColoring.PartialSwap

/-!
# Physical two-color components for partial edge colorings

This module realizes the abstract swap sets from `TotalColoring.PartialSwap`
as line-graph reachability classes supported on two actual colors.  A
reflexive reachability class always contains its root, even if that root is
uncolored or has a different color.  Accordingly, the primitive set below is
named `TwoColorReachabilityClass`.  The predicate
`IsTwoColorKempeComponent` additionally requires a supported root.

For either realization, membership is closed across every adjacent
`α`-`β` pair.  The preservation theorems can therefore combine the physical
properness condition with the exact distinguished-set compatibility criterion
from `PartialSwap` without conflating the two invariants.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- An edge is supported by the two-color subgraph when it is actually colored
`α` or `β`.  In particular, an uncolored edge is never supported. -/
def TwoColorSupported (a : PartialEdgeAssignment G C) (α β : C)
    (e : G.edgeSet) : Prop :=
  a.color e = some α ∨ a.color e = some β

/-- One physical step in the two-color line subgraph: the two edges are
incident and both are supported by `α` or `β`. -/
def TwoColorStep (a : PartialEdgeAssignment G C) (α β : C)
    (e f : G.edgeSet) : Prop :=
  G.lineGraph.Adj e f ∧ a.TwoColorSupported α β e ∧
    a.TwoColorSupported α β f

/-- Reflexive-transitive reachability through the supported two-color line
subgraph. -/
def TwoColorReachable (a : PartialEdgeAssignment G C) (α β : C)
    (e f : G.edgeSet) : Prop :=
  Relation.ReflTransGen (a.TwoColorStep α β) e f

/-- The two-color reachability class rooted at `root`.

This deliberately does not assert that `root` is supported: reflexive closure
contains every root.  Use `IsTwoColorKempeComponent` when supported-root
semantics are required. -/
def TwoColorReachabilityClass (a : PartialEdgeAssignment G C) (α β : C)
    (root : G.edgeSet) : Set G.edgeSet :=
  {e | a.TwoColorReachable α β root e}

/-- A genuine two-color Kempe component is a reachability class with an
explicitly supported root. -/
def IsTwoColorKempeComponent (a : PartialEdgeAssignment G C) (α β : C)
    (K : Set G.edgeSet) : Prop :=
  ∃ root, a.TwoColorSupported α β root ∧
    K = a.TwoColorReachabilityClass α β root

theorem twoColorStep_symm (a : PartialEdgeAssignment G C) (α β : C)
    {e f : G.edgeSet} (h : a.TwoColorStep α β e f) :
    a.TwoColorStep α β f e := by
  exact ⟨h.1.symm, h.2.2, h.2.1⟩

theorem twoColorReachable_refl (a : PartialEdgeAssignment G C) (α β : C)
    (e : G.edgeSet) : a.TwoColorReachable α β e e :=
  Relation.ReflTransGen.refl

theorem twoColorReachable_trans (a : PartialEdgeAssignment G C) (α β : C)
    {e f g : G.edgeSet} (hef : a.TwoColorReachable α β e f)
    (hfg : a.TwoColorReachable α β f g) :
    a.TwoColorReachable α β e g :=
  hef.trans hfg

theorem twoColorReachable_symm (a : PartialEdgeAssignment G C) (α β : C)
    {e f : G.edgeSet} (h : a.TwoColorReachable α β e f) :
    a.TwoColorReachable α β f e := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact (Relation.ReflTransGen.single
        (twoColorStep_symm a α β hstep)).trans ih

@[simp]
theorem mem_twoColorReachabilityClass_iff
    (a : PartialEdgeAssignment G C) (α β : C) (root e : G.edgeSet) :
    e ∈ a.TwoColorReachabilityClass α β root ↔
      a.TwoColorReachable α β root e :=
  Iff.rfl

theorem root_mem_twoColorReachabilityClass
    (a : PartialEdgeAssignment G C) (α β : C) (root : G.edgeSet) :
    root ∈ a.TwoColorReachabilityClass α β root :=
  Relation.ReflTransGen.refl

/-- Once the root is supported, every member of its reachability class is
supported as well. -/
theorem twoColorSupported_of_mem_reachabilityClass
    (a : PartialEdgeAssignment G C) (α β : C) {root e : G.edgeSet}
    (hroot : a.TwoColorSupported α β root)
    (he : e ∈ a.TwoColorReachabilityClass α β root) :
    a.TwoColorSupported α β e := by
  change a.TwoColorReachable α β root e at he
  induction he with
  | refl => exact hroot
  | tail _ hstep _ => exact hstep.2.2

/-- A supported two-color reachability class cannot cut an adjacent
`α`-`β` pair.  The statement remains true for an unsupported root because
such a root cannot be either endpoint of the pair. -/
theorem twoColorBoundaryClosed_reachabilityClass
    (a : PartialEdgeAssignment G C) (α β : C) (root : G.edgeSet) :
    a.TwoColorBoundaryClosed α β
      (a.TwoColorReachabilityClass α β root) := by
  intro e f hef heα hfβ
  have heSupported : a.TwoColorSupported α β e := Or.inl heα
  have hfSupported : a.TwoColorSupported α β f := Or.inr hfβ
  constructor
  · intro he
    exact he.tail ⟨hef, heSupported, hfSupported⟩
  · intro hf
    exact hf.tail ⟨hef.symm, hfSupported, heSupported⟩

/-- Every genuine two-color Kempe component supplies the physical boundary
closure condition required by `PartialSwap`. -/
theorem twoColorBoundaryClosed_of_isTwoColorKempeComponent
    (a : PartialEdgeAssignment G C) {α β : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent α β K) :
    a.TwoColorBoundaryClosed α β K := by
  rcases hK with ⟨root, -, rfl⟩
  exact twoColorBoundaryClosed_reachabilityClass a α β root

/-- Swapping an entire reachability class preserves partial properness. -/
theorem valid_swapOn_reachabilityClass [DecidableEq C]
    (a : PartialEdgeAssignment G C) (α β : C) (root : G.edgeSet)
    [DecidablePred (· ∈ a.TwoColorReachabilityClass α β root)]
    (hvalid : a.Valid) :
    (a.swapOn α β (a.TwoColorReachabilityClass α β root)).Valid :=
  valid_swapOn_of_boundaryClosed a
    (a.TwoColorReachabilityClass α β root) hvalid
    (twoColorBoundaryClosed_reachabilityClass a α β root)

/-- Swapping any genuine two-color Kempe component preserves partial
properness. -/
theorem valid_swapOn_of_isTwoColorKempeComponent [DecidableEq C]
    (a : PartialEdgeAssignment G C) {α β : C} (K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] (hvalid : a.Valid)
    (hK : a.IsTwoColorKempeComponent α β K) :
    (a.swapOn α β K).Valid :=
  valid_swapOn_of_boundaryClosed a K hvalid
    (twoColorBoundaryClosed_of_isTwoColorKempeComponent a hK)

/-- For a physical reachability-class swap, properness is automatic from the
original valid coloring.  Thus simultaneous preservation of properness and
the partial rainbow invariant is equivalent exactly to distinguished-set
compatibility. -/
theorem valid_and_rainbowOn_swapOn_reachabilityClass_iff [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet) {α β : C}
    (root : G.edgeSet)
    [DecidablePred (· ∈ a.TwoColorReachabilityClass α β root)]
    (hvalid : a.Valid) (hrainbow : a.RainbowOn J) (hαβ : α ≠ β) :
    (a.swapOn α β (a.TwoColorReachabilityClass α β root)).Valid ∧
        (a.swapOn α β
          (a.TwoColorReachabilityClass α β root)).RainbowOn J ↔
      a.SwapCompatibleOn J α β
        (a.TwoColorReachabilityClass α β root) := by
  constructor
  · exact fun h ↦
      (rainbowOn_swapOn_iff a J
        (a.TwoColorReachabilityClass α β root) hrainbow hαβ).1 h.2
  · intro hcompatible
    exact ⟨valid_swapOn_reachabilityClass a α β root hvalid,
      (rainbowOn_swapOn_iff a J
        (a.TwoColorReachabilityClass α β root) hrainbow hαβ).2
        hcompatible⟩

/-- Component form of the exact combined preservation criterion. -/
theorem valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_iff
    [DecidableEq C] (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} (hvalid : a.Valid)
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (hK : a.IsTwoColorKempeComponent α β K) :
    (a.swapOn α β K).Valid ∧ (a.swapOn α β K).RainbowOn J ↔
      a.SwapCompatibleOn J α β K := by
  constructor
  · exact fun h ↦ (rainbowOn_swapOn_iff a J K hrainbow hαβ).1 h.2
  · intro hcompatible
    exact ⟨valid_swapOn_of_isTwoColorKempeComponent a K hvalid hK,
      (rainbowOn_swapOn_iff a J K hrainbow hαβ).2 hcompatible⟩

/-- If either swap color is unused on `J`, swapping a physical reachability
class preserves both partial properness and the partial rainbow invariant. -/
theorem valid_and_rainbowOn_swapOn_reachabilityClass_of_one_unused
    [DecidableEq C] (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {α β : C} (root : G.edgeSet)
    [DecidablePred (· ∈ a.TwoColorReachabilityClass α β root)]
    (hvalid : a.Valid) (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (hunused : a.ColorUnusedOn J α ∨ a.ColorUnusedOn J β) :
    (a.swapOn α β (a.TwoColorReachabilityClass α β root)).Valid ∧
      (a.swapOn α β
        (a.TwoColorReachabilityClass α β root)).RainbowOn J := by
  refine (valid_and_rainbowOn_swapOn_reachabilityClass_iff
    a J root hvalid hrainbow hαβ).2 ?_
  rcases hunused with hunused | hunused
  · exact swapCompatibleOn_of_unused_left a J
      (a.TwoColorReachabilityClass α β root) hunused
  · exact swapCompatibleOn_of_unused_right a J
      (a.TwoColorReachabilityClass α β root) hunused

/-- Genuine-component form of the one-unused-color safety theorem. -/
theorem valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_of_one_unused
    [DecidableEq C] (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} (hvalid : a.Valid)
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (hK : a.IsTwoColorKempeComponent α β K)
    (hunused : a.ColorUnusedOn J α ∨ a.ColorUnusedOn J β) :
    (a.swapOn α β K).Valid ∧ (a.swapOn α β K).RainbowOn J := by
  refine (valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_iff
    a J K hvalid hrainbow hαβ hK).2 ?_
  rcases hunused with hunused | hunused
  · exact swapCompatibleOn_of_unused_left a J K hunused
  · exact swapCompatibleOn_of_unused_right a J K hunused

/-- Swapping a two-color reachability class preserves the exact location of a
unique hole. -/
theorem oneHoleAt_swapOn_reachabilityClass_iff [DecidableEq C]
    (a : PartialEdgeAssignment G C) (α β : C) (root hole : G.edgeSet)
    [DecidablePred (· ∈ a.TwoColorReachabilityClass α β root)] :
    (a.swapOn α β
      (a.TwoColorReachabilityClass α β root)).OneHoleAt hole ↔
      a.OneHoleAt hole :=
  swapOn_oneHoleAt_iff a α β
    (a.TwoColorReachabilityClass α β root) hole

end PartialEdgeAssignment

end TotalColoring
