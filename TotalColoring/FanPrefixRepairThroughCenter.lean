import TotalColoring.FanPrefixRepair

/-!
# Repairing a fan prefix after a through-center component swap

This module is the companion to `FanPrefixRepair`.  There the swapped
two-color component meets the old terminal and avoids the fan center.  Here it
meets the center and avoids the old terminal.

If the center misses `alpha`, then a genuine `alpha`-`beta` component meeting
the center leaves `beta` missing there after the swap.  For each old fan step,
either the step survives or its source leaf also misses `beta`.  The finite
prefix theorem therefore returns a surviving prefix whose terminal misses
`beta`.  This is structural: it uses neither criticality nor fan maximality
and makes no distinguished-rainbow safety claim.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {center : V}

section Swap

variable [DecidableEq C]

/-- Local repair dichotomy for a fan step after swapping a genuine component
which meets the center.  If the old step does not survive, its source leaf
misses the new center-hole color. -/
theorem fanStep_swapOn_or_missingAt_right_of_meets_center
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {alpha beta : C} {K : Set G.edgeSet} [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hmeetsCenter : EdgeSetMeetsVertex K center)
    (hcenter : a.MissingAt center alpha)
    {p q : CenterSpoke G center} (hstep : a.FanStep J p q) :
    (a.swapOn alpha beta K).FanStep J p q ∨
      (a.swapOn alpha beta K).MissingAt p.leaf beta := by
  rcases hstep with ⟨c, hqJ, hqcolor, hmissing⟩
  by_cases hqK : q.edge ∈ K
  · have hcbeta : c = beta := by
      rcases twoColorSupported_of_mem_component a hK hqK with
        hqalpha | hqbeta
      · exact (hcenter q.edge q.center_incident hqalpha).elim
      · exact Option.some.inj (hqcolor.symm.trans hqbeta)
    subst c
    have hqcolorSwap :
        (a.swapOn alpha beta K).color q.edge = some alpha := by
      rw [PartialEdgeAssignment.swapOn_color_of_mem
        a alpha beta K hqK, hqcolor]
      simp
    by_cases hmeetsSource : EdgeSetMeetsVertex K p.leaf
    · exact Or.inl ⟨alpha, hqJ, hqcolorSwap,
        missingAt_left_swapOn_of_missing_right_of_component_meets
          a hK halphabeta hmissing hmeetsSource⟩
    · exact Or.inr <|
        (missingAt_swapOn_iff_of_avoidsVertex
          a alpha beta K (edgeSetAvoidsVertex_iff_not_meets.mpr hmeetsSource)
            beta).2 hmissing
  · have hqcolorSwap :
        (a.swapOn alpha beta K).color q.edge = some c := by
      rw [PartialEdgeAssignment.swapOn_color_of_not_mem
        a alpha beta K hqK]
      exact hqcolor
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
      rcases twoColorSupported_of_mem_component a hK hfK with
        hfalpha | hfbeta
      · have hcbeta : c = beta := by
          apply Option.some.inj
          calc
            some c = (a.swapOn alpha beta K).color f := hfcolorSwap.symm
            _ = some beta := by
              rw [PartialEdgeAssignment.swapOn_color_of_mem
                a alpha beta K hfK, hfalpha]
              simp
        subst c
        have hqMem : q.edge ∈ K :=
          mem_component_of_mem_of_incident_supported a hK
            hmeetsCenter.choose_spec.1 hmeetsCenter.choose_spec.2
            q.center_incident (Or.inr hqcolor)
        exact (hqK hqMem).elim
      · have hcalpha : c = alpha := by
          apply Option.some.inj
          calc
            some c = (a.swapOn alpha beta K).color f := hfcolorSwap.symm
            _ = some alpha := by
              rw [PartialEdgeAssignment.swapOn_color_of_mem
                a alpha beta K hfK, hfbeta]
              simp
        subst c
        exact (hcenter q.edge q.center_incident hqcolor).elim

/-- Prefix repair for a physical component which meets the center and avoids
the old terminal.  The returned fan path is a literal prefix of the old path,
has the same root, and ends at a leaf missing `beta` after the swap. -/
theorem exists_prefix_after_component_swap_of_meets_center
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {alpha beta : C} {K : Set G.edgeSet} [DecidablePred (· ∈ K)]
    (F : LinearFanPath a J center)
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hmeetsCenter : EdgeSetMeetsVertex K center)
    (havoidTerminal : EdgeSetAvoidsVertex K F.terminal.leaf)
    (hcenter : a.MissingAt center alpha)
    (hterminal : a.MissingAt F.terminal.leaf beta) :
    ∃ Q : LinearFanPath (a.swapOn alpha beta K) J center,
      Q.root = F.root ∧ Q.spokes <+: F.spokes ∧
        (a.swapOn alpha beta K).MissingAt Q.terminal.leaf beta := by
  have hterminalSwap :
      (a.swapOn alpha beta K).MissingAt F.terminal.leaf beta :=
    (missingAt_swapOn_iff_of_avoidsVertex
      a alpha beta K havoidTerminal beta).2 hterminal
  exact F.exists_prefix_to_pred
    (b := a.swapOn alpha beta K)
    (fun p ↦ (a.swapOn alpha beta K).MissingAt p.leaf beta)
    hterminalSwap
    (fun {p q} hstep ↦ fanStep_swapOn_or_missingAt_right_of_meets_center
      (center := center) (K := K) (alpha := alpha) (beta := beta)
      a J hK halphabeta hmeetsCenter hcenter (p := p) (q := q) hstep)

end Swap

end PartialEdgeAssignment

end TotalColoring
