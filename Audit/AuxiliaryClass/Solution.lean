/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.CriticalAllDClosure

/-!
# Comparator solution: rainbow edge coloring of the auxiliary class

Same statement as `Audit/AuxiliaryClass/Challenge.lean`, from
`TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass`:
the hypotheses are the fields of `IsAuxiliaryClassMember D H x J M`, and
`HasValidRainbowColoring D H J` is a valid edge assignment into
`ExtensionPalette D = Fin (D + 2)` that is rainbow on the edges of `J`.
-/

namespace TotalColoringAudit.AuxiliaryClass

theorem exists_rainbow_edge_coloring_of_auxiliaryClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (J : Finset (Sym2 V)) (x : V) (M : Finset (Sym2 V))
    (distinguished_edges : ∀ ⦃e⦄, e ∈ J → e ∈ H.edgeSet)
    (matching : ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f)
    (matching_off_center : ∀ ⦃e⦄, e ∈ M → x ∉ e)
    (matching_avoids_center_neighbors : ∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H.Adj x v)
    (decomposition : J = M ∪ H.incidenceFinset x)
    (exact_coverage : ∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e)
    (card_distinguished : J.card = D)
    (maxDegree_bound : H.maxDegree ≤ D)
    (center_degree : 2 ≤ H.degree x ∧ H.degree x ≤ D) :
    ∃ color : H.edgeSet → Fin (D + 2),
      (∀ e f, H.lineGraph.Adj e f → color e ≠ color f) ∧
      (∀ e f : H.edgeSet, (e : Sym2 V) ∈ J → (f : Sym2 V) ∈ J → e ≠ f →
        color e ≠ color f) := by
  obtain ⟨a, hvalid, hrainbow⟩ :=
    TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass D H J
      ⟨x, M, ⟨distinguished_edges, matching, matching_off_center,
        matching_avoids_center_neighbors, decomposition, exact_coverage,
        card_distinguished, maxDegree_bound, center_degree⟩⟩
  exact ⟨a.color, hvalid, fun e f he hf hne => hrainbow he hf hne⟩

end TotalColoringAudit.AuxiliaryClass
