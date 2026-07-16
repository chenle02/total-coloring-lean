import TotalColoring.FanPrefixRepair
import TotalColoring.TwoColorEndpointCapacity

/-!
# Tiny Wave 4 regression fixtures

These finite examples exercise semantic edge cases in the component and fan
prefix interfaces.  They are kernel-reduced smoke tests, not census evidence
or instances of the critical theorem.
-/

namespace TotalColoring.Wave4Examples

/-- The complete graph on two vertices, which has exactly one edge. -/
abbrev K2 : SimpleGraph (Fin 2) := ⊤

/-- The unique edge of `K2`. -/
def k2Edge : K2.edgeSet :=
  ⟨s(0, 1), by simp [K2]⟩

/-- The unique edge colored with color zero. -/
def alphaAssignment : PartialEdgeAssignment K2 (Fin 3) where
  color _ := some 0

/-- The unique edge colored with a third, unsupported color. -/
def thirdColorAssignment : PartialEdgeAssignment K2 (Fin 3) where
  color _ := some 2

/-- The unique edge left uncolored. -/
def holeAssignment : PartialEdgeAssignment K2 (Fin 3) where
  color _ := none

theorem alphaAssignment_supported :
    alphaAssignment.TwoColorSupported 0 1 k2Edge := by
  exact Or.inl rfl

theorem alphaAssignment_valid : alphaAssignment.Valid := by
  have nonDiag_eq :
      ∀ z : Sym2 (Fin 2), ¬z.IsDiag → z = s(0, 1) := by
    intro z
    induction z using Sym2.inductionOn with
    | _ i j =>
        intro hnonDiag
        fin_cases i <;> fin_cases j <;> simp at hnonDiag ⊢
  have edge_eq (e : K2.edgeSet) : e = k2Edge := by
    apply Subtype.ext
    exact nonDiag_eq e.1 (K2.not_isDiag_of_mem_edgeSet e.2)
  intro e f c hef hec
  exact (hef.ne ((edge_eq e).trans (edge_eq f).symm)).elim

theorem color_one_missing_at_zero : alphaAssignment.MissingAt 0 1 := by
  intro e he
  simp [alphaAssignment]

theorem color_one_missing_at_one : alphaAssignment.MissingAt 1 1 := by
  intro e he
  simp [alphaAssignment]

noncomputable local instance alphaComponentMembership :
    DecidablePred
      (· ∈ alphaAssignment.TwoColorReachabilityClass 0 1 k2Edge) :=
  Classical.decPred _

theorem alphaComponent_meets_zero :
    EdgeSetMeetsVertex
      (alphaAssignment.TwoColorReachabilityClass 0 1 k2Edge) 0 := by
  refine ⟨k2Edge,
    alphaAssignment.root_mem_twoColorReachabilityClass 0 1 k2Edge, ?_⟩
  change (0 : Fin 2) ∈ (k2Edge : Sym2 (Fin 2))
  simp [k2Edge]

theorem alphaComponent_meets_one :
    EdgeSetMeetsVertex
      (alphaAssignment.TwoColorReachabilityClass 0 1 k2Edge) 1 := by
  refine ⟨k2Edge,
    alphaAssignment.root_mem_twoColorReachabilityClass 0 1 k2Edge, ?_⟩
  change (1 : Fin 2) ∈ (k2Edge : Sym2 (Fin 2))
  simp [k2Edge]

/-- The one-edge component has both ambient vertices as endpoints. -/
theorem one_edge_component_named_endpoints :
    EdgeSetIsEndpoint
        (alphaAssignment.TwoColorReachabilityClass 0 1 k2Edge) 0 ∧
      EdgeSetIsEndpoint
        (alphaAssignment.TwoColorReachabilityClass 0 1 k2Edge) 1 := by
  let hK :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      alphaAssignment 0 1 k2Edge alphaAssignment_supported
  exact ⟨
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
      alphaAssignment_valid hK color_one_missing_at_zero
        alphaComponent_meets_zero,
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
      alphaAssignment_valid hK color_one_missing_at_one
        alphaComponent_meets_one⟩

/-- The global endpoint theorem is sharp on the one-edge component. -/
theorem one_edge_component_endpoint_capacity :
    ({v : Fin 2 | EdgeSetIsEndpoint
      (alphaAssignment.TwoColorReachabilityClass 0 1 k2Edge) v} :
      Set (Fin 2)).ncard ≤ 2 := by
  exact PartialEdgeAssignment.edgeSetIsEndpoint_ncard_le_two_of_component
    alphaAssignment_valid
    (PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      alphaAssignment 0 1 k2Edge alphaAssignment_supported)

/-- A one-edge physical component exchanges the missing endpoint label. -/
theorem one_edge_component_swap_flips_missing_label :
    (alphaAssignment.swapOn 0 1
      (alphaAssignment.TwoColorReachabilityClass 0 1 k2Edge)).MissingAt 0 0 := by
  classical
  apply PartialEdgeAssignment.missingAt_left_swapOn_of_missing_right_of_component_meets
    alphaAssignment
    (PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      alphaAssignment 0 1 k2Edge alphaAssignment_supported)
    (by decide) color_one_missing_at_zero alphaComponent_meets_zero

/-- Reflexive raw reachability still contains an unsupported third-colored
root. -/
theorem third_color_raw_class_contains_root :
    k2Edge ∈ thirdColorAssignment.TwoColorReachabilityClass 0 1 k2Edge :=
  thirdColorAssignment.root_mem_twoColorReachabilityClass 0 1 k2Edge

/-- The same unsupported root does not define a genuine physical component.
This guards the deliberate raw-class/genuine-component distinction. -/
theorem third_color_raw_class_not_genuine :
    ¬thirdColorAssignment.IsTwoColorKempeComponent 0 1
      (thirdColorAssignment.TwoColorReachabilityClass 0 1 k2Edge) := by
  rintro ⟨root, hroot, hclass⟩
  rcases hroot with hzero | hone
  · simp [thirdColorAssignment] at hzero
  · simp [thirdColorAssignment] at hone

/-- An uncolored raw root is likewise not a genuine component. -/
theorem uncolored_raw_class_not_genuine :
    ¬holeAssignment.IsTwoColorKempeComponent 0 1
      (holeAssignment.TwoColorReachabilityClass 0 1 k2Edge) := by
  rintro ⟨root, hroot, hclass⟩
  rcases hroot with hzero | hone
  · simp [holeAssignment] at hzero
  · simp [holeAssignment] at hone

/-- The unique edge oriented away from vertex zero. -/
def rootSpoke : CenterSpoke K2 (0 : Fin 2) where
  leaf := 1
  edge := k2Edge
  endpoints := rfl

/-- The singleton/root-only fan path. -/
def rootOnlyFan :
    PartialEdgeAssignment.LinearFanPath holeAssignment ∅ (0 : Fin 2) where
  root := rootSpoke
  tail := []
  root_not_mem := by simp
  chain := by simp
  nodup_spokes := by simp

/-- Prefix extraction treats the length-zero fan as a literal singleton path.
-/
theorem root_only_prefix_fixture :
    ∃ Q : PartialEdgeAssignment.LinearFanPath holeAssignment ∅ (0 : Fin 2),
      Q.root = rootOnlyFan.root ∧ Q.spokes <+: rootOnlyFan.spokes ∧
        Q.terminal = rootSpoke := by
  apply rootOnlyFan.exists_prefix_to_pred (b := holeAssignment)
    (fun p ↦ p = rootSpoke)
  · rfl
  · intro p q hstep
    rcases hstep with ⟨c, hqJ, hqcolor, hmissing⟩
    simp [holeAssignment] at hqcolor

end TotalColoring.Wave4Examples
