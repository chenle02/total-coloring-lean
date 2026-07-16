import TotalColoring.FanPrefix
import TotalColoring.TwoColorGeometry

/-!
# Repairing a fan prefix after a center-avoiding component swap

Fix a fan path whose center misses `alpha` and whose terminal leaf misses
`beta`.  Let `K` be a genuine physical `alpha`-`beta` component meeting that
terminal leaf but avoiding the center.  After swapping `K`, the terminal leaf
misses `alpha`.  An old fan step either remains a fan step, or the swap has
introduced its donor color at the source leaf.  Full component closure then
shows that the donor was `beta`, so that source leaf now misses `alpha`.

The finite prefix theorem in `FanPrefix` therefore returns a surviving prefix
whose terminal leaf misses `alpha`.  This is a purely structural recoloring
lemma: it assumes neither criticality nor fan maximality and makes no claim
that the component swap is distinguished-rainbow safe.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {center : V}

section Swap

variable [DecidableEq C]

/-- Local repair dichotomy for one fan step.  If the step does not survive a
full physical component swap avoiding the center, its source leaf misses the
old center-hole color after the swap. -/
theorem fanStep_swapOn_or_missingAt_left
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {alpha beta : C} {K : Set G.edgeSet} [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (havoid : EdgeSetAvoidsVertex K center)
    (hcenter : a.MissingAt center alpha)
    {p q : CenterSpoke G center} (hstep : a.FanStep J p q) :
    (a.swapOn alpha beta K).FanStep J p q ∨
      (a.swapOn alpha beta K).MissingAt p.leaf alpha := by
  rcases hstep with ⟨c, hqJ, hqcolor, hmissing⟩
  have hqK : q.edge ∉ K := fun hmem ↦ havoid hmem q.center_incident
  have hqcolorSwap : (a.swapOn alpha beta K).color q.edge = some c := by
    simpa using PartialEdgeAssignment.swapOn_color_of_not_mem
      a alpha beta K hqK ▸ hqcolor
  by_cases hmissingSwap : (a.swapOn alpha beta K).MissingAt p.leaf c
  · exact Or.inl ⟨c, hqJ, hqcolorSwap, hmissingSwap⟩
  · have hexists : ∃ f, Incident p.leaf f ∧
        (a.swapOn alpha beta K).color f = some c := by
      by_contra hno
      apply hmissingSwap
      intro f hf hfc
      exact hno ⟨f, hf, hfc⟩
    rcases hexists with ⟨f, hf, hfcolorSwap⟩
    have hfK : f ∈ K := by
      by_contra hfK
      rw [PartialEdgeAssignment.swapOn_color_of_not_mem
        a alpha beta K hfK] at hfcolorSwap
      exact hmissing f hf hfcolorSwap
    have hfsupported := twoColorSupported_of_mem_component a hK hfK
    rcases hfsupported with hfalpha | hfbeta
    · have hsome : some beta = some c := by
        calc
          some beta = (a.swapOn alpha beta K).color f := by
            rw [PartialEdgeAssignment.swapOn_color_of_mem
              a alpha beta K hfK, hfalpha]
            simp
          _ = some c := hfcolorSwap
      have hcbeta : c = beta := (Option.some.inj hsome).symm
      subst c
      exact Or.inr <|
        missingAt_left_swapOn_of_missing_right_of_component_meets
          a hK halphabeta hmissing ⟨f, hfK, hf⟩
    · have hsome : some alpha = some c := by
        calc
          some alpha = (a.swapOn alpha beta K).color f := by
            rw [PartialEdgeAssignment.swapOn_color_of_mem
              a alpha beta K hfK, hfbeta]
            simp
          _ = some c := hfcolorSwap
      have hcalpha : c = alpha := (Option.some.inj hsome).symm
      subst c
      exact (hcenter q.edge q.center_incident hqcolor).elim

/-- Prefix repair for a center-avoiding physical component.  The returned fan
path is a literal prefix of the old path, has the same root, and ends at a
leaf missing `alpha` after the swap. -/
theorem exists_prefix_after_component_swap
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {alpha beta : C} {K : Set G.edgeSet} [DecidablePred (· ∈ K)]
    (F : LinearFanPath a J center)
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (havoid : EdgeSetAvoidsVertex K center)
    (hcenter : a.MissingAt center alpha)
    (hterminal : a.MissingAt F.terminal.leaf beta)
    (hmeetsTerminal : EdgeSetMeetsVertex K F.terminal.leaf) :
    ∃ Q : LinearFanPath (a.swapOn alpha beta K) J center,
      Q.root = F.root ∧ Q.spokes <+: F.spokes ∧
        (a.swapOn alpha beta K).MissingAt Q.terminal.leaf alpha := by
  have hterminalSwap :
      (a.swapOn alpha beta K).MissingAt F.terminal.leaf alpha :=
    missingAt_left_swapOn_of_missing_right_of_component_meets
      a hK halphabeta hterminal hmeetsTerminal
  exact F.exists_prefix_to_pred
    (b := a.swapOn alpha beta K)
    (fun p ↦ (a.swapOn alpha beta K).MissingAt p.leaf alpha)
    hterminalSwap
    (fun {p q} hstep ↦ fanStep_swapOn_or_missingAt_left
      (center := center) (K := K) (alpha := alpha) (beta := beta)
      a J hK halphabeta havoid hcenter (p := p) (q := q) hstep)

end Swap

end PartialEdgeAssignment

end TotalColoring
