import TotalColoring.CenterSpoke
import TotalColoring.Dependency
import TotalColoring.Fan

/-!
# Ordered centered fans

This module packages a finite fan as a simple, nonempty list of spokes at a
fixed center.  A step from `p` to `q` says that the old color on the
non-distinguished edge `q.edge` is missing at `p.leaf`.  The root edge is also
required to avoid the distinguished set, so every edge of a fan path does.

The principal local theorem is the exact legality seam for moving a hole one
step along a fan: validity turns a fan step into
`DonorAvailableAtHoleExcept`.  No maximality, capacity, criticality, or
coloring-existence assertion is made here.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {center : V}

/-- A directed step in a centered fan.  The target spoke is colored outside
`J`, and its color is missing at the leaf of the source spoke. -/
def FanStep (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (p q : CenterSpoke G center) : Prop :=
  ∃ c : C, q.edge ∉ J ∧ a.color q.edge = some c ∧
    a.MissingAt p.leaf c

theorem FanStep.target_not_mem {a : PartialEdgeAssignment G C}
    {J : Set G.edgeSet} {p q : CenterSpoke G center}
    (h : a.FanStep J p q) : q.edge ∉ J := by
  rcases h with ⟨-, hqJ, -⟩
  exact hqJ

theorem FanStep.target_colored {a : PartialEdgeAssignment G C}
    {J : Set G.edgeSet} {p q : CenterSpoke G center}
    (h : a.FanStep J p q) : ∃ c, a.color q.edge = some c := by
  rcases h with ⟨c, -, hc, -⟩
  exact ⟨c, hc⟩

/-- A fan step supplies a center dependency with the two spoke leaves as
source and target. -/
theorem FanStep.centerDependency {a : PartialEdgeAssignment G C}
    {J : Set G.edgeSet} {p q : CenterSpoke G center}
    (h : a.FanStep J p q) :
    a.CenterDependency J center p.leaf q.leaf := by
  rcases h with ⟨c, hqJ, hcolor, hmissing⟩
  exact ⟨q.edge, c, q.endpoints, hqJ, hcolor, hmissing⟩

/-- A fan step cannot repeat a spoke: the target color is present at the
target leaf but would be required to be missing there. -/
theorem FanStep.ne {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {p q : CenterSpoke G center} (h : a.FanStep J p q) : p ≠ q := by
  intro hpq
  subst q
  rcases h with ⟨c, -, hcolor, hmissing⟩
  exact hmissing p.edge p.leaf_incident hcolor

/-- A nonempty simple directed fan path, written as an explicit root followed
by its tail.  Distinct spokes automatically have distinct underlying edges;
that derived fact is exposed below. -/
structure LinearFanPath (a : PartialEdgeAssignment G C)
    (J : Set G.edgeSet) (center : V) where
  root : CenterSpoke G center
  tail : List (CenterSpoke G center)
  root_not_mem : root.edge ∉ J
  chain : (root :: tail).IsChain (a.FanStep J)
  nodup_spokes : (root :: tail).Nodup

namespace LinearFanPath

variable {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}

/-- The nonempty list of all spokes in path order. -/
def spokes (F : LinearFanPath a J center) : List (CenterSpoke G center) :=
  F.root :: F.tail

@[simp]
theorem spokes_ne_nil (F : LinearFanPath a J center) : F.spokes ≠ [] := by
  simp [spokes]

@[simp]
theorem head_spokes (F : LinearFanPath a J center) :
    F.spokes.head F.spokes_ne_nil = F.root := by
  simp [spokes]

/-- The terminal spoke of the path. -/
def terminal (F : LinearFanPath a J center) : CenterSpoke G center :=
  F.spokes.getLast F.spokes_ne_nil

/-- The underlying edge list, in the same order as the spokes. -/
def edges (F : LinearFanPath a J center) : List G.edgeSet :=
  F.spokes.map CenterSpoke.edge

@[simp]
theorem root_mem_spokes (F : LinearFanPath a J center) :
    F.root ∈ F.spokes := by
  simp [spokes]

@[simp]
theorem terminal_mem_spokes (F : LinearFanPath a J center) :
    F.terminal ∈ F.spokes :=
  List.getLast_mem F.spokes_ne_nil

@[simp]
theorem root_edge_mem_edges (F : LinearFanPath a J center) :
    F.root.edge ∈ F.edges := by
  exact List.mem_map.mpr ⟨F.root, F.root_mem_spokes, rfl⟩

@[simp]
theorem terminal_edge_mem_edges (F : LinearFanPath a J center) :
    F.terminal.edge ∈ F.edges := by
  exact List.mem_map.mpr ⟨F.terminal, F.terminal_mem_spokes, rfl⟩

/-- Simplicity of the spoke list implies simplicity of the edge list because
a center spoke is determined by its edge. -/
theorem nodup_edges (F : LinearFanPath a J center) : F.edges.Nodup := by
  apply List.Nodup.map
  · intro p q hpq
    exact CenterSpoke.ext (CenterSpoke.leaf_eq_of_edge_eq hpq)
  · exact F.nodup_spokes

private theorem all_not_mem_of_chain
    {root : CenterSpoke G center} {tail : List (CenterSpoke G center)}
    (hroot : root.edge ∉ J)
    (hchain : (root :: tail).IsChain (a.FanStep J)) :
    ∀ p ∈ root :: tail, p.edge ∉ J := by
  induction tail generalizing root with
  | nil =>
      intro p hp
      simp only [List.mem_singleton] at hp
      subst p
      exact hroot
  | cons next rest ih =>
      have hparts : a.FanStep J root next ∧
          (next :: rest).IsChain (a.FanStep J) := by
        simpa [List.isChain_cons] using hchain
      intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact hroot
      · exact ih hparts.1.target_not_mem hparts.2 p
          (List.mem_cons.mpr hp)

/-- Every spoke edge of a fan path avoids the distinguished set. -/
theorem spoke_edge_not_mem (F : LinearFanPath a J center)
    {p : CenterSpoke G center} (hp : p ∈ F.spokes) : p.edge ∉ J := by
  exact all_not_mem_of_chain F.root_not_mem F.chain p hp

/-- Every edge in the underlying fan sequence avoids the distinguished set. -/
theorem edge_not_mem (F : LinearFanPath a J center)
    {e : G.edgeSet} (he : e ∈ F.edges) : e ∉ J := by
  rcases List.mem_map.mp he with ⟨p, hp, rfl⟩
  exact F.spoke_edge_not_mem hp

@[simp]
theorem terminal_edge_not_mem (F : LinearFanPath a J center) :
    F.terminal.edge ∉ J :=
  F.spoke_edge_not_mem F.terminal_mem_spokes

/-- Mapping a fan path to its leaf vertices gives a chain in the abstract
center-dependency relation. -/
theorem leaf_chain (F : LinearFanPath a J center) :
    (F.spokes.map CenterSpoke.leaf).IsChain
      (a.CenterDependency J center) := by
  apply List.isChain_map_of_isChain CenterSpoke.leaf
      (fun _ _ h ↦ FanStep.centerDependency h)
  exact F.chain

/-- The terminal leaf of a fan path is center-reachable from its root leaf. -/
theorem centerReachable_terminal (F : LinearFanPath a J center) :
    a.CenterReachable J center F.root.leaf F.terminal.leaf := by
  have hreach := List.relationReflTransGen_of_exists_isChain
    (F.spokes.map CenterSpoke.leaf) F.leaf_chain (by simp)
  change Relation.ReflTransGen (a.CenterDependency J center)
    F.root.leaf F.terminal.leaf
  simpa [terminal] using hreach

end LinearFanPath

/-- Vertices admitting a simple linear fan path from a specified root spoke.
This is the concrete fan-generated subset of the abstract dependency-reachable
set. -/
def linearFanReachableSet (a : PartialEdgeAssignment G C)
    (J : Set G.edgeSet) (root : CenterSpoke G center) : Set V :=
  {target | ∃ F : LinearFanPath a J center,
    F.root = root ∧ F.terminal.leaf = target}

theorem linearFanReachableSet_subset_centerReachableSet
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (root : CenterSpoke G center) :
    a.linearFanReachableSet J root ⊆
      a.centerReachableSet J center root.leaf := by
  intro target htarget
  rcases htarget with ⟨F, hroot, hterminal⟩
  subst hroot
  simpa [hterminal] using F.centerReachable_terminal

/-- The load-bearing one-step legality theorem.  At the source leaf the donor
color is absent by the fan-step hypothesis.  At the common center it is absent
from every edge other than the donor by validity. -/
theorem donorAvailableAtHoleExcept_of_fanStep
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {p q : CenterSpoke G center} (hvalid : a.Valid)
    (hstep : a.FanStep J p q) :
    a.DonorAvailableAtHoleExcept p.edge q.edge := by
  rcases hstep with ⟨c, -, hqcolor, hmissing⟩
  intro d hdcolor f hpf hfq
  have hcd : c = d := Option.some.inj (hqcolor.symm.trans hdcolor)
  subst d
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hpf with
    ⟨-, v, hvp, hvf⟩
  rcases p.incident_iff.mp hvp with hvcenter | hvleaf
  · have hqf : G.lineGraph.Adj q.edge f := by
      apply SimpleGraph.lineGraph_adj_iff_exists.mpr
      exact ⟨Ne.symm hfq, center, q.center_incident, by simpa [hvcenter] using hvf⟩
    exact hvalid q.edge f c hqf hqcolor
  · exact hmissing f (by simpa [hvleaf] using hvf)

/-- A legal fan step relocates a unique hole while preserving validity and
the distinguished-edge rainbow invariant. -/
theorem valid_oneHoleAt_rainbowOn_moveHole_of_fanStep
    [DecidableEq G.edgeSet]
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {p q : CenterSpoke G center}
    (hvalid : a.Valid) (hhole : a.OneHoleAt p.edge)
    (hrainbow : a.RainbowOn J) (hpJ : p.edge ∉ J)
    (hstep : a.FanStep J p q) :
    (a.moveHole p.edge q.edge).Valid ∧
      (a.moveHole p.edge q.edge).OneHoleAt q.edge ∧
      (a.moveHole p.edge q.edge).RainbowOn J := by
  have hpq : q.edge ≠ p.edge :=
    CenterSpoke.ne_iff_edge_ne.mp hstep.ne |>.symm
  exact valid_oneHoleAt_rainbowOn_moveHole hvalid hhole hrainbow hpq
    (donorAvailableAtHoleExcept_of_fanStep hvalid hstep)
    hpJ hstep.target_not_mem

end PartialEdgeAssignment

end TotalColoring
