/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.HighDegreeTotalColoring

/-!
# Comparator solution: total coloring of high-degree graphs

Same statement as `Audit/HighDegree/Challenge.lean`, from
`TotalColoring.exists_valid_assignment_of_highDegree`: an `Assignment G C` is a
vertex coloring and an edge coloring, `ExtensionPalette (Δ + 1)` is
`Fin (Δ + 1 + 2)`, and `Assignment.Valid` is the three conditions.
-/

namespace TotalColoringAudit.HighDegree

theorem exists_total_coloring_of_card_le_two_mul_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ (vertexColor : V → Fin (G.maxDegree + 1 + 2))
      (edgeColor : G.edgeSet → Fin (G.maxDegree + 1 + 2)),
      (∀ v w, G.Adj v w → vertexColor v ≠ vertexColor w) ∧
      (∀ e f, G.lineGraph.Adj e f → edgeColor e ≠ edgeColor f) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) → vertexColor v ≠ edgeColor e) := by
  obtain ⟨a, hvalid⟩ := TotalColoring.exists_valid_assignment_of_highDegree G hdense
  exact ⟨a.vertexColor, a.edgeColor, hvalid⟩

end TotalColoringAudit.HighDegree
