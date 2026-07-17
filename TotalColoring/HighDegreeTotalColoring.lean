import TotalColoring.AuxiliaryTransfer
import TotalColoring.ComplementMatchingWitness
import TotalColoring.EmptyAssignment
import TotalColoring.HighDegreeComplementMatching
import TotalColoring.MatchingExact

/-!
# Total coloring in the high-degree regime

This module closes the pair/singleton reduction for finite graphs satisfying
`|V| ≤ 2 * G.maxDegree`.  It first trims the complement matching supplied by
`HighDegreeComplementMatching` to the exact size
`|V| - (G.maxDegree + 1)`.  The matching then induces a pair/singleton witness
with exactly `G.maxDegree + 1` distinguished edges, so the general auxiliary
transfer theorem returns a valid assignment in `ExtensionPalette
(G.maxDegree + 1)`.

The nonempty proof and the empty-vertex proof are kept separate until the
final theorem.  No parity hypothesis is used.
-/

namespace TotalColoring

universe u

variable {V : Type u}

namespace MatchingLowerBound

/-- A finite nonempty graph in the high-degree regime has a complement
matching with exactly `|V| - (G.maxDegree + 1)` edges. -/
theorem exists_complement_matchingGraph_edgeFinset_card_eq [Fintype V]
    [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ M : SimpleGraph V, ∃ _ : DecidableRel M.Adj,
      M ≤ Gᶜ ∧ IsMatchingGraph M ∧
        M.edgeFinset.card = Fintype.card V - (G.maxDegree + 1) := by
  obtain ⟨M, instM, hMG, hM, hcard⟩ :=
    exists_complement_matchingGraph_edgeFinset_card_ge G hdense
  letI : DecidableRel M.Adj := instM
  obtain ⟨N, instN, hNM, hN, hNcard⟩ :=
    hM.exists_subgraph_edgeFinset_card_eq hcard
  letI : DecidableRel N.Adj := instN
  exact ⟨N, instN, hNM.trans hMG, hN, hNcard⟩

end MatchingLowerBound

namespace Auxiliary

/-- In the high-degree regime, a complement matching induces a
pair/singleton witness with exactly `G.maxDegree + 1` distinguished edges. -/
theorem exists_pairSingletonWitness_of_highDegree [Fintype V] [Nonempty V]
    [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ P : PairSingletonWitness G,
      P.distinguished.card = G.maxDegree + 1 := by
  obtain ⟨H, instH, hHG, hmatching, hcard⟩ :=
    MatchingLowerBound.exists_complement_matchingGraph_edgeFinset_card_eq
      G hdense
  letI : DecidableRel H.Adj := instH
  let P := PairSingletonWitness.ofComplementMatching H hHG hmatching
  refine ⟨P, ?_⟩
  have hDle : G.maxDegree + 1 ≤ Fintype.card V := by
    have hmax := G.maxDegree_lt_card_verts
    omega
  exact PairSingletonWitness.ofComplementMatching_distinguished_card
    hHG hmatching hDle hcard

/-- Nonempty finite graphs in the high-degree regime have a valid total
coloring assignment in `ExtensionPalette (G.maxDegree + 1)`. -/
theorem exists_valid_assignment_of_highDegree_nonempty [Fintype V]
    [Nonempty V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ assignment : Assignment G (ExtensionPalette (G.maxDegree + 1)),
      assignment.Valid := by
  classical
  obtain ⟨P, hclasses⟩ :=
    exists_pairSingletonWitness_of_highDegree G hdense
  letI : DecidableRel P.auxiliaryGraph.Adj := Classical.decRel _
  apply Extension.exists_valid_decode_of_inAuxiliaryClass
    (G.maxDegree + 1) P.extension P.distinguished
  · intro v
    exact P.classEdge_mem_distinguishedEdgeSet v
  · exact ⟨none, P.matchingPart,
      P.isAuxiliaryClassMember_of_highDegree hclasses hdense⟩

end Auxiliary

/-- Every finite graph in the high-degree regime has a valid total
coloring assignment in `ExtensionPalette (G.maxDegree + 1)`, including the
empty graph. -/
theorem exists_valid_assignment_of_highDegree [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ assignment : Assignment G (ExtensionPalette (G.maxDegree + 1)),
      assignment.Valid := by
  rcases isEmpty_or_nonempty V with hV | hV
  · letI : IsEmpty V := hV
    exact exists_valid_assignment_of_isEmpty G
      (ExtensionPalette (G.maxDegree + 1))
  · letI : Nonempty V := hV
    exact Auxiliary.exists_valid_assignment_of_highDegree_nonempty G hdense

end TotalColoring
