/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib

/-!
# Comparator challenge: decoding an auxiliary edge coloring

Statement only, in Mathlib's vocabulary. The data of an auxiliary extension of
`G` into `H` are a class edge `classEdge v` of `H` for each vertex `v` of `G`
and a copy `originalEdge e` in `H` of each edge `e` of `G`, such that adjacent
vertices get different class edges, adjacent edges of `G` have adjacent copies
(in Mathlib's line graph), and the class edge of a vertex is adjacent to the copy
of every edge incident with it.

Claim: an edge coloring `color` of `H` that is proper (on Mathlib's line graph)
and gives distinct colors to distinct class edges decodes to a total coloring of
`G`: color each vertex by its class edge and each edge by its copy; then
adjacent vertices, adjacent edges, and a vertex and an edge incident with it all
get different colors.
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
        color (classEdge v) ≠ color (originalEdge e)) := by
  sorry

end TotalColoringAudit.Decode
