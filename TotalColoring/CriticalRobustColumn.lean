import TotalColoring.CriticalRecenteredCapacity
import TotalColoring.CriticalRobustExpansion

/-!
# Elimination of a robust exact-triple column

Suppose a globally reach-card-maximal critical state has a direct center
target `q` carrying a color `gamma` which is missing at exactly three
reachable vertices.  A spare color `alpha` can be chosen distinct from
`gamma`, since exactly two palette colors are unused on the distinguished
set.  Recentered location makes `alpha` present at every reachable vertex,
and the global spare-center exclusion makes it present at the center.

The three `gamma`-holes therefore supply an `alpha`--`gamma` component which
avoids the center.  Its selected endpoint meets the component, so the robust
expansion theorem rules out robustness of the incoming `gamma` column against
two entry deletions.

This module only eliminates the robust branch for a supplied direct exact
triple.  It does not produce that target, classify the remaining dominator
cases, or prove the all-orders coloring theorem.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V}
variable {J M : Finset (Sym2 V)} [DecidableRel H.Adj]

/-- At a global reachable maximum, a direct color column supported by an
exact triple of reachable holes cannot be robust against deletion of two
incoming sources. -/
theorem not_colorColumnEntryRobust_two_of_exactTriple
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    (state : OrientedOneHoleState D H J)
    (hmaximal : state.IsGloballyReachCardMaximal)
    {q : V} {gamma : ExtensionPalette D}
    (hgammaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center q gamma)
    (htriple : (state.missingSourceFinset gamma).card = 3) :
    ¬state.ColorColumnEntryRobust q gamma 2 := by
  classical
  let U := state.assignment.colorUnusedOnFinset
    (distinguishedEdgeSet H J)
  have hUcard : U.card = 2 := by
    simpa [U] using h.card_colorUnusedOnFinset_eq_two state.rainbow
  have hUlarge : 1 < U.card := by omega
  rcases Finset.one_lt_card.mp hUlarge with
    ⟨alpha₀, halpha₀U, alpha₁, halpha₁U, halpha₀alpha₁⟩
  obtain ⟨alpha, halphaU, halphaGamma⟩ :
      ∃ alpha : ExtensionPalette D, alpha ∈ U ∧ alpha ≠ gamma := by
    by_cases halpha₀Gamma : alpha₀ ≠ gamma
    · exact ⟨alpha₀, halpha₀U, halpha₀Gamma⟩
    · refine ⟨alpha₁, halpha₁U, ?_⟩
      intro halpha₁Gamma
      apply halpha₀alpha₁
      exact (of_not_not halpha₀Gamma).trans halpha₁Gamma.symm
  have halphaUnused : state.assignment.ColorUnusedOn
      (distinguishedEdgeSet H J) alpha :=
    by
      change alpha ∈ state.assignment.colorUnusedOnFinset
        (distinguishedEdgeSet H J) at halphaU
      exact (PartialEdgeAssignment.mem_colorUnusedOnFinset_iff
        state.assignment (distinguishedEdgeSet H J) alpha).mp halphaU
  have halphaPresent : ∀ ⦃vertex : V⦄,
      state.assignment.CenterReachable (distinguishedEdgeSet H J)
          state.center state.root.leaf vertex →
        ¬state.assignment.MissingAt vertex alpha := by
    intro vertex hreach
    exact h.not_missingAt_centerReachable_of_unused hstructure
      state.root state.rootOutside state.valid state.oneHole state.rainbow
      halphaUnused hreach
  have halphaCenter : ¬state.assignment.MissingAt state.center alpha :=
    h.not_missingAt_center_of_unused state.root state.rootOutside
      state.valid state.oneHole state.rainbow halphaUnused
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      state.assignment halphaCenter with
    ⟨alphaEdge, halphaEdgeCenter, halphaEdgeColor⟩
  have halphaEdgeOutside : alphaEdge ∉ distinguishedEdgeSet H J := by
    intro halphaEdgeJ
    exact halphaUnused halphaEdgeJ halphaEdgeColor
  rcases Sym2.mem_iff_exists.mp halphaEdgeCenter with
    ⟨alphaTarget, halphaEdgeEnds⟩
  have halphaTarget : state.assignment.IsCenterColorTarget
      (distinguishedEdgeSet H J) state.center alphaTarget alpha :=
    ⟨alphaEdge, halphaEdgeEnds, halphaEdgeOutside, halphaEdgeColor⟩

  let T : Set V := ↑(state.missingSourceFinset gamma)
  have hTthree : 3 ≤ T.ncard := by
    have hTcard : T.ncard = 3 := by
      simpa [T] using htriple
    omega
  have hTgamma : ∀ ⦃vertex : V⦄, vertex ∈ T →
      state.assignment.MissingAt vertex gamma := by
    intro vertex hvertex
    exact ((state.mem_missingSourceFinset_iff gamma vertex).1
      (by simpa [T] using hvertex)).2
  have hTalpha : ∀ ⦃vertex : V⦄, vertex ∈ T →
      ¬state.assignment.MissingAt vertex alpha := by
    intro vertex hvertex
    have hsource := (state.mem_missingSourceFinset_iff gamma vertex).1
      (by simpa [T] using hvertex)
    exact halphaPresent hsource.1
  rcases
      PartialEdgeAssignment.exists_component_avoiding_vertex_of_three_missing
        state.valid hTthree hTgamma hTalpha halphaCenter with
    ⟨source, K, hsourceT, hK, hsourceEndpoint, hcenterAvoid⟩
  have hsourceData := (state.mem_missingSourceFinset_iff gamma source).1
    (by simpa [T] using hsourceT)
  have hsourceMeets : EdgeSetMeetsVertex K source :=
    ⟨hsourceEndpoint.choose, hsourceEndpoint.choose_spec.1,
      hsourceEndpoint.choose_spec.2.1⟩
  exact state.not_colorColumnEntryRobust_two_of_externalTokenComponent
    hmaximal (alpha := alpha) (gamma := gamma) halphaGamma
      (gammaTarget := q) (alphaTarget := alphaTarget) (source := source)
      hgammaTarget halphaTarget halphaUnused halphaPresent (K := K) hK
      hcenterAvoid hsourceData.1 hsourceData.2 hsourceMeets

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
