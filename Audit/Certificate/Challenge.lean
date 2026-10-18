/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib

/-!
# Comparator challenge: soundness of the auxiliary certificate checker

Statement only, in Mathlib's vocabulary. The extension data `classEdge`,
`originalEdge` and their three conflict facts are as in
`Audit/Decode/Challenge.lean`. The certificate is an edge coloring `color` of
`H`, and the checker is the Boolean `decide p && decide q` (Mathlib's
decidability instances on finite types), where `p` says that two distinct edges
of `H` sharing an endpoint (Mathlib's line-graph adjacency, written out) get
different colors, and `q` says that distinct class edges get different colors.

Claim: if the checker returns `true`, the decoded coloring (each vertex colored
by its class edge, each edge by its copy) is a total coloring of `G`.
-/

namespace TotalColoringAudit.Certificate

theorem checkExtension_sound
    {V : Type*} {W : Type*} {C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (classEdge : V → H.edgeSet) (originalEdge : G.edgeSet → H.edgeSet)
    (classEdge_ne_of_adj : ∀ {v w : V}, G.Adj v w → classEdge v ≠ classEdge w)
    (originalEdge_adj : ∀ {e f : G.edgeSet}, G.lineGraph.Adj e f →
      H.lineGraph.Adj (originalEdge e) (originalEdge f))
    (classEdge_adj_original : ∀ {v : V} {e : G.edgeSet}, v ∈ (e : Sym2 V) →
      H.lineGraph.Adj (classEdge v) (originalEdge e))
    (color : H.edgeSet → C)
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableRel H.Adj] [DecidableEq C]
    (h : (decide (∀ e f : H.edgeSet,
            (e ≠ f ∧ ∃ x : W, x ∈ (e : Sym2 W) ∧ x ∈ (f : Sym2 W)) → color e ≠ color f) &&
          decide (∀ v w : V, classEdge v ≠ classEdge w →
            color (classEdge v) ≠ color (classEdge w))) = true) :
    (∀ v w, G.Adj v w → color (classEdge v) ≠ color (classEdge w)) ∧
      (∀ e f, G.lineGraph.Adj e f → color (originalEdge e) ≠ color (originalEdge f)) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) →
        color (classEdge v) ≠ color (originalEdge e)) := by
  sorry

end TotalColoringAudit.Certificate
