/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib

/-!
# Comparator challenge: total coloring of high-degree graphs

Statement only, in Mathlib's vocabulary. A total coloring with `Δ + 3` colors is
a vertex coloring and an edge coloring into `Fin (G.maxDegree + 1 + 2)` that are
proper on adjacent vertices, proper on adjacent edges (Mathlib's line graph), and
give every vertex a color different from each edge incident with it.

Claim: every finite graph whose order is at most twice its maximum degree has
such a coloring. No parity hypothesis.
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
  sorry

end TotalColoringAudit.HighDegree
