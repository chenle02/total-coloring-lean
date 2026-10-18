/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib
import TotalColoring.Certificate

/-!
# Comparator solution: soundness of the auxiliary certificate checker

Same statement as `Audit/Certificate/Challenge.lean`, from
`TotalColoring.Certificate.checkExtension_sound`. The library checker is
`checkEdge a && checkRainbow a X.classEdge`, each a `decide` of the same
proposition as the Challenge's (`checkExtension_eq_true_iff`), and a `decide`
is `true` exactly when its proposition holds, whatever the instance.

`Fidelity.not_weaker` derives the library theorem back from the Challenge
statement, so the two statements are equivalent.
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
  have hchecked :
      TotalColoring.Certificate.checkExtension
        (⟨classEdge, originalEdge, classEdge_ne_of_adj, originalEdge_adj,
          classEdge_adj_original⟩ : TotalColoring.Auxiliary.Extension G H)
        (⟨color⟩ : TotalColoring.EdgeAssignment H C) = true := by
    rw [TotalColoring.Certificate.checkExtension_eq_true_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    refine ⟨fun e f hef => h.1 e f ?_, h.2⟩
    exact (SimpleGraph.lineGraph_adj_iff_exists).1 hef
  exact TotalColoring.Certificate.checkExtension_sound _ _ hchecked

namespace Fidelity

universe u v w

/-- The Challenge statement implies the library statement. -/
theorem not_weaker (h : type_of% @checkExtension_sound.{u, v, w}) :
    type_of% @TotalColoring.Certificate.checkExtension_sound.{u, v, w} := by
  intro V W C G H X a _ _ _ _ _ hcheck
  rw [TotalColoring.Certificate.checkExtension_eq_true_iff] at hcheck
  refine h X.classEdge X.originalEdge X.classEdge_ne_of_adj X.originalEdge_adj
    X.classEdge_adj_original a.color ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨fun e f hef => hcheck.1 e f ?_, hcheck.2⟩
  exact (SimpleGraph.lineGraph_adj_iff_exists).2 hef

end Fidelity

end TotalColoringAudit.Certificate
