import TotalColoring.OrderedFan
import TotalColoring.SimpleReachability

/-!
# Exact correspondence between fan paths and center reachability

Abstract center reachability records a witnessing colored center edge for
every nonreflexive step.  This module orients each such witness as a
`CenterSpoke` and converts a loop-erased vertex path into a simple linear fan
path.  The prescribed root spoke supplies the reflexive starting point; its
edge must explicitly avoid the distinguished set.

No validity, one-hole, noncolorability, maximality, or capacity hypothesis is
used here.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {center : V}

/-- Turn a dependency chain beginning at a prescribed spoke leaf into a
spoke chain.  Every target spoke is built from the edge and endpoint equality
carried by its dependency step. -/
private theorem exists_spoke_tail_of_dependency_chain
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    {root : CenterSpoke G center} {vertices : List V}
    (hchain : (root.leaf :: vertices).IsChain
      (a.CenterDependency J center)) :
    ∃ tail : List (CenterSpoke G center),
      (root :: tail).IsChain (a.FanStep J) ∧
        (root :: tail).map CenterSpoke.leaf = root.leaf :: vertices := by
  induction vertices generalizing root with
  | nil =>
      exact ⟨[], List.IsChain.singleton root, rfl⟩
  | cons target rest ih =>
      have hparts :
          a.CenterDependency J center root.leaf target ∧
            (target :: rest).IsChain (a.CenterDependency J center) := by
        simpa [List.isChain_cons] using hchain
      rcases hparts.1 with ⟨e, c, hends, heJ, hcolor, hmissing⟩
      let next : CenterSpoke G center :=
        { leaf := target, edge := e, endpoints := hends }
      have hnextChain : (next.leaf :: rest).IsChain
          (a.CenterDependency J center) := by
        simpa [next] using hparts.2
      rcases ih hnextChain with ⟨tail, htailChain, htailLeaves⟩
      have hstep : a.FanStep J root next := by
        exact ⟨c, heJ, hcolor, hmissing⟩
      refine ⟨next :: tail, ?_, ?_⟩
      · simpa [List.isChain_cons] using And.intro hstep htailChain
      · simp [next, htailLeaves]

/-- Every abstractly reachable target has a simple linear fan path beginning
at the prescribed root spoke, provided that root edge is outside `J`. -/
theorem exists_linearFanPath_of_centerReachable [DecidableEq V]
    {a : PartialEdgeAssignment G C} {J : Set G.edgeSet}
    (root : CenterSpoke G center) (hrootJ : root.edge ∉ J)
    {target : V}
    (hreach : a.CenterReachable J center root.leaf target) :
    ∃ F : LinearFanPath a J center,
      F.root = root ∧ F.terminal.leaf = target := by
  rcases a.exists_simple_centerDependency_path hreach with
    ⟨vertices, hvertices, hchain, hnodup, hhead, hlast⟩
  cases vertices with
  | nil => exact (hvertices rfl).elim
  | cons first rest =>
      have hfirst : first = root.leaf := by
        simpa using hhead
      subst first
      rcases exists_spoke_tail_of_dependency_chain hchain with
        ⟨tail, hfanChain, hleaves⟩
      have hspokeNodup : (root :: tail).Nodup := by
        apply List.Nodup.of_map CenterSpoke.leaf
        rw [hleaves]
        exact hnodup
      let F : LinearFanPath a J center :=
        { root := root
          tail := tail
          root_not_mem := hrootJ
          chain := hfanChain
          nodup_spokes := hspokeNodup }
      have hterminal :
          ((root :: tail).getLast (by simp)).leaf = target := by
        have hmappedLast :
            ((root :: tail).map CenterSpoke.leaf).getLast? =
              some target := by
          rw [hleaves, List.getLast?_eq_some_getLast (by simp), hlast]
        rw [List.getLast?_map,
          List.getLast?_eq_some_getLast (by simp)] at hmappedLast
        exact Option.some.inj hmappedLast
      refine ⟨F, rfl, ?_⟩
      simpa [F, LinearFanPath.terminal, LinearFanPath.spokes] using hterminal

/-- Under the necessary root-edge condition, the concrete fan-generated set
is exactly the abstract center-dependency reachable set. -/
theorem linearFanReachableSet_eq_centerReachableSet [DecidableEq V]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (root : CenterSpoke G center) (hrootJ : root.edge ∉ J) :
    a.linearFanReachableSet J root =
      a.centerReachableSet J center root.leaf := by
  apply Set.Subset.antisymm
  · exact a.linearFanReachableSet_subset_centerReachableSet J root
  · intro target htarget
    exact exists_linearFanPath_of_centerReachable root hrootJ htarget

end PartialEdgeAssignment

end TotalColoring
