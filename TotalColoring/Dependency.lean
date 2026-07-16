import TotalColoring.Partial
import TotalColoring.SimpleReachability

/-!
# Center-dependency reachability

This module formalizes the directed dependency relation used to generate a
centered fan.  A dependency `p -> q` is witnessed by a colored edge `uq`
outside the distinguished set whose color is missing at `p`.  The definition
keeps the witnessing edge explicit; in particular, it does not silently choose
an orientation of an unordered edge.

Only the elementary reachability interface is proved here.  No maximality,
fan-capacity, endpoint-location, or coloring-existence conclusion is asserted.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- A directed fan dependency at center `center`: the color on a
non-distinguished center edge with other endpoint `target` is missing at
`source`.  The equality records the orientation of the edge explicitly. -/
def CenterDependency (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center source target : V) : Prop :=
  ∃ (e : G.edgeSet) (c : C),
    (e : Sym2 V) = s(center, target) ∧ e ∉ J ∧
      a.color e = some c ∧ a.MissingAt source c

/-- A vertex is reachable from `root` by zero or more center dependencies. -/
def CenterReachable (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root target : V) : Prop :=
  Relation.ReflTransGen (a.CenterDependency J center) root target

/-- The canonical root-reachable vertex set of the center-dependency
relation. -/
def centerReachableSet (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) : Set V :=
  {target | a.CenterReachable J center root target}

/-- A non-distinguished colored center edge has `target` as its other
endpoint.  This is the target-side projection of `CenterDependency`. -/
def IsCenterTarget (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center target : V) : Prop :=
  ∃ (e : G.edgeSet) (c : C),
    (e : Sym2 V) = s(center, target) ∧ e ∉ J ∧ a.color e = some c

/-- The physical vertex universe used by the dependency digraph: the root
together with the heads of colored center edges outside `J`. -/
def centerPhysicalSet (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) : Set V :=
  {root} ∪ {target | a.IsCenterTarget J center target}

theorem centerDependency_isCenterTarget
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center source target : V}
    (h : a.CenterDependency J center source target) :
    a.IsCenterTarget J center target := by
  rcases h with ⟨e, c, hends, heJ, hcolor, -⟩
  exact ⟨e, c, hends, heJ, hcolor⟩

/-- A dependency cannot be a loop: its witnessing color is present on an edge
incident with the target, but is required to be missing there. -/
theorem centerDependency_irrefl
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet) (center : V) :
    ∀ target, ¬a.CenterDependency J center target target := by
  intro target h
  rcases h with ⟨e, c, hends, -, hcolor, hmissing⟩
  apply hmissing e
  · change target ∈ (e : Sym2 V)
    rw [hends]
    exact Sym2.mem_mk_right center target
  · exact hcolor

/-- The other endpoint of a genuine center edge is different from the
center. -/
theorem isCenterTarget_ne_center
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center target : V} (h : a.IsCenterTarget J center target) :
    target ≠ center := by
  intro htarget
  rcases h with ⟨e, -, hends, -⟩
  have hadj : G.Adj center target := by
    rw [← G.mem_edgeSet]
    rw [← hends]
    exact e.2
  apply G.loopless.irrefl center
  rw [htarget] at hadj
  exact hadj

theorem centerDependency_target_ne_center
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center source target : V}
    (h : a.CenterDependency J center source target) :
    target ≠ center :=
  isCenterTarget_ne_center (centerDependency_isCenterTarget h)

/-- A target has a unique witnessing center edge.  This uses only the
unordered endpoint equalities; the proof terms witnessing edge membership are
irrelevant. -/
theorem centerEdge_eq_of_endpoints
    {center target : V} {e f : G.edgeSet}
    (he : (e : Sym2 V) = s(center, target))
    (hf : (f : Sym2 V) = s(center, target)) :
    e = f := by
  apply Subtype.ext
  exact he.trans hf.symm

/-- If `center-root` is the unique hole, no dependency can enter `root`.
There is only one simple edge with those endpoints, and it is uncolored. -/
theorem centerDependency_target_ne_root_of_oneHoleAt
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root source : V} {hole : G.edgeSet}
    (hends : (hole : Sym2 V) = s(center, root))
    (hhole : a.OneHoleAt hole)
    (hdep : a.CenterDependency J center source root) : False := by
  rcases hdep with ⟨e, c, heEnds, -, heColor, -⟩
  have heq : e = hole := centerEdge_eq_of_endpoints heEnds hends
  have hnone : a.color hole = none := (hhole hole).2 rfl
  rw [heq, hnone] at heColor
  simp at heColor

@[simp]
theorem centerReachable_refl
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) :
    a.CenterReachable J center root root :=
  Relation.ReflTransGen.refl

theorem centerReachable_tail
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root source target : V}
    (hreach : a.CenterReachable J center root source)
    (hstep : a.CenterDependency J center source target) :
    a.CenterReachable J center root target :=
  Relation.ReflTransGen.tail hreach hstep

theorem centerReachable_trans
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center p q r : V}
    (hpq : a.CenterReachable J center p q)
    (hqr : a.CenterReachable J center q r) :
    a.CenterReachable J center p r :=
  Relation.ReflTransGen.trans hpq hqr

@[simp]
theorem mem_centerReachableSet_iff
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root target : V) :
    target ∈ a.centerReachableSet J center root ↔
      a.CenterReachable J center root target :=
  Iff.rfl

theorem root_mem_centerReachableSet
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) :
    root ∈ a.centerReachableSet J center root :=
  centerReachable_refl a J center root

/-- The reachable set is closed under one outgoing dependency. -/
theorem centerReachableSet_closed
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root source target : V}
    (hsource : source ∈ a.centerReachableSet J center root)
    (hstep : a.CenterDependency J center source target) :
    target ∈ a.centerReachableSet J center root :=
  centerReachable_tail hsource hstep

/-- Every reachable vertex is either the root or the target of a genuine
non-distinguished colored center edge. -/
theorem centerReachable_eq_root_or_isCenterTarget
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root target : V}
    (h : a.CenterReachable J center root target) :
    target = root ∨ a.IsCenterTarget J center target := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hstep _ =>
      exact Or.inr (centerDependency_isCenterTarget hstep)

/-- If the reachable root differs from the center, then every vertex reached
from it also differs from the center. -/
theorem centerReachable_ne_center
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {center root target : V} (hroot : root ≠ center)
    (hreach : a.CenterReachable J center root target) :
    target ≠ center := by
  rcases centerReachable_eq_root_or_isCenterTarget hreach with htarget | htarget
  · subst target
    exact hroot
  · exact isCenterTarget_ne_center htarget

/-- Root reachability never leaves the physical vertex universe. -/
theorem centerReachable_mem_centerPhysicalSet
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root target : V}
    (h : a.CenterReachable J center root target) :
    target ∈ a.centerPhysicalSet J center root := by
  rcases centerReachable_eq_root_or_isCenterTarget h with hroot | htarget
  · subst target
    exact Set.mem_union_left _ (Set.mem_singleton root)
  · exact Set.mem_union_right _ htarget

theorem centerReachableSet_subset_centerPhysicalSet
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) :
    a.centerReachableSet J center root ⊆
      a.centerPhysicalSet J center root := by
  intro target htarget
  exact centerReachable_mem_centerPhysicalSet htarget

/-- In particular, a nonroot reachable vertex has a witnessing colored
center edge outside `J`. -/
theorem isCenterTarget_of_centerReachable_of_ne_root
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root target : V}
    (hreach : a.CenterReachable J center root target)
    (hne : target ≠ root) :
    a.IsCenterTarget J center target := by
  rcases centerReachable_eq_root_or_isCenterTarget hreach with hroot | htarget
  · exact (hne hroot).elim
  · exact htarget

/-- Abstract dependency reachability always has a simple directed list
witness.  This removes repeated vertices before any color shift is attempted;
the conversion of its edge witnesses into oriented spokes belongs to the
ordered-fan layer. -/
theorem exists_simple_centerDependency_path [DecidableEq V]
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {center root target : V}
    (hreach : a.CenterReachable J center root target) :
    ∃ l : List V, ∃ hlne : l ≠ [],
      l.IsChain (a.CenterDependency J center) ∧ l.Nodup ∧
        l.head hlne = root ∧ l.getLast hlne = target :=
  SimpleReachability.exists_nodup_isChain_of_reflTransGen hreach

end PartialEdgeAssignment

end TotalColoring
