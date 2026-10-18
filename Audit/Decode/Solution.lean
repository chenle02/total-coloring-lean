/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.Auxiliary

/-!
# Comparator solution: decoding an auxiliary edge coloring

Same statement as `Audit/Decode/Challenge.lean`, from
`TotalColoring.Auxiliary.Extension.decode_valid`: an `Extension G H` is the
two maps and the three conflict facts, an `EdgeAssignment` is a color function,
`Rainbow` is distinct colors on distinct class edges, `decode` colors a vertex
by its class edge and an edge by its copy, and `Assignment.Valid` is the three
conditions.

`Fidelity.not_weaker` derives the library theorem back from the Challenge
statement, so the two statements are equivalent.
-/

namespace TotalColoringAudit.Decode

theorem decode_valid
    {V : Type*} {W : Type*} {C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (classEdge : V → H.edgeSet) (originalEdge : G.edgeSet → H.edgeSet)
    (classEdge_ne_of_adj : ∀ {v w : V}, G.Adj v w → classEdge v ≠ classEdge w)
    (originalEdge_adj : ∀ {e f : G.edgeSet}, G.lineGraph.Adj e f →
      H.lineGraph.Adj (originalEdge e) (originalEdge f))
    (classEdge_adj_original : ∀ {v : V} {e : G.edgeSet}, v ∈ (e : Sym2 V) →
      H.lineGraph.Adj (classEdge v) (originalEdge e))
    (color : H.edgeSet → C)
    (hvalid : ∀ e f, H.lineGraph.Adj e f → color e ≠ color f)
    (hrainbow : ∀ v w, classEdge v ≠ classEdge w →
      color (classEdge v) ≠ color (classEdge w)) :
    (∀ v w, G.Adj v w → color (classEdge v) ≠ color (classEdge w)) ∧
      (∀ e f, G.lineGraph.Adj e f → color (originalEdge e) ≠ color (originalEdge f)) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) →
        color (classEdge v) ≠ color (originalEdge e)) :=
  TotalColoring.Auxiliary.Extension.decode_valid
    ⟨classEdge, originalEdge, classEdge_ne_of_adj, originalEdge_adj, classEdge_adj_original⟩
    ⟨color⟩ hvalid hrainbow

namespace Fidelity

universe u v w

/-- The Challenge statement implies the library statement. -/
theorem not_weaker (h : type_of% @decode_valid.{u, v, w}) :
    type_of% @TotalColoring.Auxiliary.Extension.decode_valid.{u, v, w} := by
  intro V W G H C X a ha hr
  exact h X.classEdge X.originalEdge X.classEdge_ne_of_adj X.originalEdge_adj
    X.classEdge_adj_original a.color ha hr

end Fidelity

end TotalColoringAudit.Decode
