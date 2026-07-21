import TotalColoring.MinSixCageModel

namespace TotalColoring.MinSixCage

/-- Double-count the selected descriptor--core-vertex eligibility incidences. -/
theorem sum_columnCount_eq_sum_eligible_card (X : Finset Descriptor) :
    ∑ v : CoreVertex, columnCount X v =
      ∑ d ∈ X, d.eligible.card := by
  calc
    ∑ v : CoreVertex, columnCount X v =
        ∑ v : CoreVertex, ∑ d ∈ X, if v ∈ d.eligible then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro v _
      simp [columnCount]
    _ = ∑ d ∈ X, ∑ v : CoreVertex, if v ∈ d.eligible then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ X, d.eligible.card := by
      apply Finset.sum_congr rfl
      intro d _
      simp

/-- A six-column mask demands three incidences per column plus one for each
set bit. -/
theorem Mask.sum_requiredColumn (B : Mask) :
    ∑ v : CoreVertex, B.requiredColumn v = 18 + B.popcount := by
  calc
    ∑ v : CoreVertex, B.requiredColumn v =
        ∑ v : CoreVertex, (3 + if B.bit v then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      simp only [Mask.requiredColumn]
      split_ifs <;> omega
    _ = 18 + B.popcount := by
      simp [Finset.sum_add_distrib, Mask.popcount, Finset.sum_boole]

/-- The ambient-incidence lower bound forces at least two degree-four
columns. -/
theorem Blocker.admissible {B : Mask} {X : Finset Descriptor}
    (h : Blocker B X) : B.Admissible := by
  unfold Mask.Admissible
  have hDemand : 20 ≤ ∑ v : CoreVertex, B.requiredColumn v := by
    calc
      20 ≤ ∑ v : CoreVertex, columnCount X v := h.ambientIncidence
      _ = ∑ v : CoreVertex, B.requiredColumn v := by
        apply Finset.sum_congr rfl
        intro v _
        exact h.columns v
  rw [B.sum_requiredColumn] at hDemand
  omega

/-- The fifteen genuine unordered edges of the six-vertex core. -/
def allCoreEdges : Finset CoreEdge :=
  Finset.univ.powersetCard 2

@[simp] theorem mem_allCoreEdges_iff (e : CoreEdge) :
    e ∈ allCoreEdges ↔ e.card = 2 := by
  simp [allCoreEdges]

@[simp] theorem card_allCoreEdges : allCoreEdges.card = 15 := by
  simp [allCoreEdges, Finset.card_powersetCard]

/-- A pairwise edge-packed family of valid nonempty core matchings has at most
fifteen members.  This is the semantic upper bound behind the exact selected-
count partition: choose at least one physical core edge from every descriptor;
pairwise packing makes the resulting edge resources disjoint. -/
theorem card_le_fifteen_of_valid_edgePacked
    {X : Finset Descriptor}
    (hvalid : ∀ d ∈ X, d.Valid)
    (hpacked : EdgePacked X) :
    X.card ≤ 15 := by
  have hpairwise : (X : Set Descriptor).PairwiseDisjoint Descriptor.matching := by
    intro d₁ hd₁ d₂ hd₂ hne
    exact hpacked d₁ hd₁ d₂ hd₂ hne
  have hnonempty : ∀ d ∈ X, d.matching.Nonempty := by
    intro d hd
    exact (hvalid d hd).1.1
  calc
    X.card ≤ (X.biUnion Descriptor.matching).card :=
      Finset.card_le_card_biUnion hpairwise hnonempty
    _ ≤ allCoreEdges.card := by
      apply Finset.card_le_card
      intro e he
      rw [Finset.mem_biUnion] at he
      obtain ⟨d, hdX, hed⟩ := he
      rw [mem_allCoreEdges_iff]
      exact (hvalid d hdX).1.2.1 e hed
    _ = 15 := card_allCoreEdges

/-- Every semantic blocker lies in exactly one of the selected-count leaves
`6, ..., 15`.  This proves the mathematical cardinality coverage of that
partition; it does not yet identify a serialized CNF or prove its threshold
encoder sound. -/
theorem Blocker.selectedCount_mem_Icc
    {B : Mask} {X : Finset Descriptor} (h : Blocker B X) :
    X.card ∈ Finset.Icc 6 15 := by
  exact Finset.mem_Icc.mpr
    ⟨h.atLeastSix, card_le_fifteen_of_valid_edgePacked h.valid h.edgePacked⟩

/-- Existential form used when selecting the unique exact-count branch. -/
theorem Blocker.exists_selectedCount
    {B : Mask} {X : Finset Descriptor} (h : Blocker B X) :
    ∃ k ∈ Finset.Icc 6 15, X.card = k := by
  exact ⟨X.card, h.selectedCount_mem_Icc, rfl⟩

end TotalColoring.MinSixCage
