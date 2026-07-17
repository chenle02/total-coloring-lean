import TotalColoring.CriticalThroughCenter
import TotalColoring.FanLeaves

/-!
# Full survival of a fixed fan sequence

The earlier through-center repair theorem returns some surviving prefix after
a component swap.  That existential result does not preserve a designated
full sequence.  This module proves the stronger witness-sensitive statement.

Locally, a fan step either survives a swap through the center or its source
avoids the component while already missing the new center-hole color.  In a
supplied critical state, exact through-center closure rules out the latter
alternative at every source in the chosen path.  The post-swap fan can
therefore be rebuilt with literally the same root and tail.

No terminal-hole, carrier, fan-maximality, or fan-capacity hypothesis is used.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {center : V}

section Swap

variable [DecidableEq C]

/-- Exact local failure mode for a fan step under a through-center component
swap.  If the old step does not survive, its source avoids the component and
already misses the right-hand component color. -/
theorem fanStep_swapOn_or_avoids_source_of_meets_center
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {alpha beta : C} {K : Set G.edgeSet} [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hmeetsCenter : EdgeSetMeetsVertex K center)
    (hcenter : a.MissingAt center alpha)
    {p q : CenterSpoke G center} (hstep : a.FanStep J p q) :
    (a.swapOn alpha beta K).FanStep J p q ∨
      (EdgeSetAvoidsVertex K p.leaf ∧ a.MissingAt p.leaf beta) := by
  rcases hstep with ⟨c, hqJ, hqcolor, hmissing⟩
  by_cases hqK : q.edge ∈ K
  · have hcbeta : c = beta := by
      rcases twoColorSupported_of_mem_component a hK hqK with
        hqalpha | hqbeta
      · exact (hcenter q.edge q.center_incident hqalpha).elim
      · exact Option.some.inj (hqcolor.symm.trans hqbeta)
    subst c
    by_cases hmeetsSource : EdgeSetMeetsVertex K p.leaf
    · left
      refine ⟨alpha, hqJ, ?_, ?_⟩
      · rw [PartialEdgeAssignment.swapOn_color_of_mem
          a alpha beta K hqK, hqcolor]
        simp
      · exact missingAt_left_swapOn_of_missing_right_of_component_meets
          a hK halphabeta hmissing hmeetsSource
    · exact Or.inr
        ⟨edgeSetAvoidsVertex_iff_not_meets.mpr hmeetsSource, hmissing⟩
  · have hcalpha : c ≠ alpha := by
      intro hca
      apply hcenter q.edge q.center_incident
      simpa [hca] using hqcolor
    have hcbeta : c ≠ beta := by
      intro hcb
      apply hqK
      apply mem_component_of_mem_of_incident_supported a hK
        hmeetsCenter.choose_spec.1 hmeetsCenter.choose_spec.2
        q.center_incident
      exact Or.inr (by simpa [hcb] using hqcolor)
    left
    refine ⟨c, hqJ, ?_, ?_⟩
    · rw [PartialEdgeAssignment.swapOn_color_of_not_mem
        a alpha beta K hqK]
      exact hqcolor
    · exact (missingAt_other_swapOn_iff
        a K hcalpha hcbeta).2 hmissing

end Swap

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A safe genuine component through the center preserves the designated fan
sequence literally: the post-swap fan has exactly the old root and tail, not
merely an existentially surviving prefix. -/
theorem exists_same_linearFanPath_after_swap_of_meets_center
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    {alpha beta : ExtensionPalette D} {K : Set H.edgeSet}
    [DecidablePred (· ∈ K)]
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (halphabeta : alpha ≠ beta)
    (hcenter : a.MissingAt center alpha)
    (hmeetsCenter : EdgeSetMeetsVertex K center)
    (hcompatible :
      a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha beta K) :
    ∃ F' : PartialEdgeAssignment.LinearFanPath
        (a.swapOn alpha beta K) (distinguishedEdgeSet H J) center,
      F'.root = F.root ∧ F'.tail = F.tail := by
  have hchain :
      F.spokes.IsChain
        ((a.swapOn alpha beta K).FanStep (distinguishedEdgeSet H J)) := by
    apply F.chain.imp_of_mem_imp
    intro p q hp _hq hstep
    rcases PartialEdgeAssignment.fanStep_swapOn_or_avoids_source_of_meets_center
        (center := center) (K := K) (alpha := alpha) (beta := beta)
        a (distinguishedEdgeSet H J) hK halphabeta hmeetsCenter hcenter
        hstep with hsurvives | ⟨havoidSource, hmissingSource⟩
    · exact hsurvives
    · have hmeetsSource :=
        h.component_meets_centerReachable_missing_right_of_swapCompatible
          F.root F.root_not_mem hvalid hhole hrainbow hK halphabeta
          hcenter hmeetsCenter hcompatible
          (F.centerReachable_of_mem_spokes hp) hmissingSource
      exact (edgeSetAvoidsVertex_iff_not_meets.mp havoidSource
        hmeetsSource).elim
  let F' : PartialEdgeAssignment.LinearFanPath
      (a.swapOn alpha beta K) (distinguishedEdgeSet H J) center :=
    { root := F.root
      tail := F.tail
      root_not_mem := F.root_not_mem
      chain := by simpa [PartialEdgeAssignment.LinearFanPath.spokes] using hchain
      nodup_spokes := F.nodup_spokes }
  exact ⟨F', rfl, rfl⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
