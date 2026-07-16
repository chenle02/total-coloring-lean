import TotalColoring.OrderedFan

/-!
# Prefixes of ordered fan paths

The all-leaf repair argument follows an old fan sequence until either every
step survives a recoloring or the first failed step exposes a repair color at
its source leaf.  This module isolates that finite-list argument.  Its main
theorem constructs an actual `LinearFanPath` for the surviving prefix, so the
root-only case is represented by the singleton path rather than by a prose
exception.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment
namespace LinearFanPath

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {a b : PartialEdgeAssignment G C} {J : Set G.edgeSet} {center : V}

private theorem exists_prefix_chain_to_pred
    {X : Type*} {R S : X → X → Prop} {P : X → Prop}
    (x : X) (xs : List X)
    (hchain : (x :: xs).IsChain R)
    (hterminal : P ((x :: xs).getLast (by simp)))
    (hstep : ∀ ⦃p q⦄, R p q → S p q ∨ P p) :
    ∃ y ys, (y :: ys) <+: (x :: xs) ∧
      (y :: ys).IsChain S ∧ P ((y :: ys).getLast (by simp)) := by
  induction xs generalizing x with
  | nil =>
      refine ⟨x, [], by simp, by simp, ?_⟩
      simpa using hterminal
  | cons y ys ih =>
      have hparts : R x y ∧ (y :: ys).IsChain R := by
        simpa [List.isChain_cons] using hchain
      rcases hstep hparts.1 with hxy | hPx
      · have hterminalTail : P ((y :: ys).getLast (by simp)) := by
          simpa using hterminal
        rcases ih y hparts.2 hterminalTail with
          ⟨z, zs, hzprefix, hzchain, hzP⟩
        obtain ⟨hzEq, htailPrefix⟩ := List.cons_prefix_cons.mp hzprefix
        subst z
        refine ⟨x, y :: zs, ?_, ?_, ?_⟩
        · exact List.cons_prefix_cons.mpr ⟨rfl,
            List.cons_prefix_cons.mpr ⟨rfl, htailPrefix⟩⟩
        · exact List.isChain_cons_cons.mpr ⟨hxy, hzchain⟩
        · simpa using hzP
      · refine ⟨x, [], by simp, by simp, ?_⟩
        simpa using hPx

/-- If every old fan step either survives in `b` or exposes predicate `P` at
its source, and `P` holds at the old terminal, then some nonempty prefix is a
fan path for `b` ending at a `P`-spoke.  The returned path has the same root,
and its spoke list is literally a prefix of the original list. -/
theorem exists_prefix_to_pred
    (F : LinearFanPath a J center) (P : CenterSpoke G center → Prop)
    (hterminal : P F.terminal)
    (hstep : ∀ ⦃p q⦄, a.FanStep J p q → b.FanStep J p q ∨ P p) :
    ∃ Q : LinearFanPath b J center,
      Q.root = F.root ∧ Q.spokes <+: F.spokes ∧ P Q.terminal := by
  rcases exists_prefix_chain_to_pred F.root F.tail F.chain
      (by simpa [LinearFanPath.terminal, LinearFanPath.spokes] using hterminal)
      hstep with ⟨y, ys, hyprefix, hychain, hyP⟩
  obtain ⟨hyroot, htailPrefix⟩ := List.cons_prefix_cons.mp hyprefix
  subst y
  let Q : LinearFanPath b J center :=
    { root := F.root
      tail := ys
      root_not_mem := F.root_not_mem
      chain := hychain
      nodup_spokes := hyprefix.nodup F.nodup_spokes }
  refine ⟨Q, rfl, ?_, ?_⟩
  · exact hyprefix
  · simpa [Q, LinearFanPath.terminal, LinearFanPath.spokes] using hyP

end LinearFanPath
end PartialEdgeAssignment

end TotalColoring
