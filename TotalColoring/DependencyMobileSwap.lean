import TotalColoring.DependencySwap

/-!
# Exact dependency transport through an off-center component swap

This module isolates the local dependency update used by robust-token
expansion.  Suppose a genuine `alpha`--`gamma` component avoids the fan
center, `alpha` is present at an old dependency source, and `q` is the
non-distinguished center target carrying `gamma`.  An old dependency survives
the component swap exactly unless all three exceptional conditions hold:

* the source misses `gamma`;
* the component meets the source; and
* the old dependency targets `q`.

Validity is needed only to identify every center edge carrying `gamma` with
the supplied edge to `q`.  The second result records the compensating update:
an exceptional source becomes `alpha`-missing and therefore acquires an
incoming dependency to any supplied center target carrying `alpha`.

These are local transport statements.  They assert no maximality, robustness,
or coloring-existence conclusion.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- A swap set which avoids the center leaves every specified colored center
target literally unchanged. -/
theorem isCenterColorTarget_swapOn_iff_of_avoids_center
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center target : V}
    {color alpha beta : C} (havoid : EdgeSetAvoidsVertex K center) :
    (a.swapOn alpha beta K).IsCenterColorTarget
        J center target color ↔
      a.IsCenterColorTarget J center target color := by
  constructor
  · rintro ⟨edge, hends, hedgeJ, hedgeColor⟩
    have hedgeCenter : Incident center edge := by
      change center ∈ (edge : Sym2 V)
      rw [hends]
      exact Sym2.mem_mk_left center target
    have hedgeK : edge ∉ K := fun hmem ↦ havoid hmem hedgeCenter
    refine ⟨edge, hends, hedgeJ, ?_⟩
    exact (swapOn_color_of_not_mem a alpha beta K hedgeK).symm.trans
      hedgeColor
  · rintro ⟨edge, hends, hedgeJ, hedgeColor⟩
    have hedgeCenter : Incident center edge := by
      change center ∈ (edge : Sym2 V)
      rw [hends]
      exact Sym2.mem_mk_left center target
    have hedgeK : edge ∉ K := fun hmem ↦ havoid hmem hedgeCenter
    refine ⟨edge, hends, hedgeJ, ?_⟩
    exact (swapOn_color_of_not_mem a alpha beta K hedgeK).trans hedgeColor

/-- Exact survival criterion for one old dependency under an off-center
`alpha`--`gamma` component swap.  The only deleted dependency is the supplied
`gamma` column at a source which is an affected component endpoint. -/
theorem centerDependency_swapOn_iff_not_gamma_exception
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center source target q : V}
    {alpha gamma : C}
    (hvalid : a.Valid)
    (hK : a.IsTwoColorKempeComponent alpha gamma K)
    (halphaGamma : alpha ≠ gamma)
    (hcenterAvoid : EdgeSetAvoidsVertex K center)
    (hsourceAlpha : ¬a.MissingAt source alpha)
    (htargetGamma : a.IsCenterColorTarget J center q gamma)
    (hdependency : a.CenterDependency J center source target) :
    (a.swapOn alpha gamma K).CenterDependency
        J center source target ↔
      ¬(a.MissingAt source gamma ∧
        EdgeSetMeetsVertex K source ∧ target = q) := by
  have htargetGammaSwap :
      (a.swapOn alpha gamma K).IsCenterColorTarget J center q gamma :=
    (isCenterColorTarget_swapOn_iff_of_avoids_center
      a J K hcenterAvoid).2 htargetGamma
  constructor
  · intro hnew hexception
    rcases hexception with ⟨_hsourceGamma, hmeets, htarget⟩
    subst target
    have hnewGamma :
        (a.swapOn alpha gamma K).MissingAt source gamma :=
      (htargetGammaSwap.centerDependency_iff_missingAt source).1 hnew
    have holdAlpha : a.MissingAt source alpha :=
      (missingAt_right_swapOn_iff_of_component_meets
        a hK halphaGamma hmeets).1 hnewGamma
    exact hsourceAlpha holdAlpha
  · intro hnotException
    by_cases hsourceGamma : a.MissingAt source gamma
    · by_cases hmeets : EdgeSetMeetsVertex K source
      · have htargetNeQ : target ≠ q := by
          intro htarget
          exact hnotException ⟨hsourceGamma, hmeets, htarget⟩
        rcases hdependency with
          ⟨edge, color, hends, hedgeJ, hedgeColor, hmissing⟩
        have hedgeCenter : Incident center edge := by
          change center ∈ (edge : Sym2 V)
          rw [hends]
          exact Sym2.mem_mk_left center target
        have hedgeK : edge ∉ K :=
          fun hmem ↦ hcenterAvoid hmem hedgeCenter
        have hcolorAlpha : color ≠ alpha := by
          intro hEq
          subst color
          exact hsourceAlpha hmissing
        have hcolorGamma : color ≠ gamma := by
          intro hEq
          subst color
          rcases htargetGamma with
            ⟨gammaEdge, hgammaEnds, _hgammaJ, hgammaColor⟩
          have hgammaCenter : Incident center gammaEdge := by
            change center ∈ (gammaEdge : Sym2 V)
            rw [hgammaEnds]
            exact Sym2.mem_mk_left center q
          have hedgeEq : edge = gammaEdge :=
            edge_eq_of_incident_of_color_eq hvalid hedgeCenter hgammaCenter
              hedgeColor hgammaColor
          have htargetEq : target = q := by
            apply Sym2.congr_right.mp
            calc
              s(center, target) = (edge : Sym2 V) := hends.symm
              _ = (gammaEdge : Sym2 V) := by rw [hedgeEq]
              _ = s(center, q) := hgammaEnds
          exact htargetNeQ htargetEq
        refine ⟨edge, color, hends, hedgeJ, ?_, ?_⟩
        · exact (swapOn_color_of_not_mem
            a alpha gamma K hedgeK).trans hedgeColor
        · exact (missingAt_other_swapOn_iff
            a K hcolorAlpha hcolorGamma).2 hmissing
      · have hsourceAvoid : EdgeSetAvoidsVertex K source :=
          edgeSetAvoidsVertex_iff_not_meets.mpr hmeets
        rcases hdependency with
          ⟨edge, color, hends, hedgeJ, hedgeColor, hmissing⟩
        have hedgeCenter : Incident center edge := by
          change center ∈ (edge : Sym2 V)
          rw [hends]
          exact Sym2.mem_mk_left center target
        have hedgeK : edge ∉ K :=
          fun hmem ↦ hcenterAvoid hmem hedgeCenter
        refine ⟨edge, color, hends, hedgeJ, ?_, ?_⟩
        · exact (swapOn_color_of_not_mem
            a alpha gamma K hedgeK).trans hedgeColor
        · exact (missingAt_swapOn_iff_of_avoidsVertex
            a alpha gamma K hsourceAvoid color).2 hmissing
    · exact centerDependency_swapOn_of_source_present
        a J K hdependency hsourceAlpha hsourceGamma

/-- An affected `gamma`-missing source becomes `alpha`-missing after swapping
its full `alpha`--`gamma` component. -/
theorem missingAt_alpha_swapOn_of_gamma_endpoint
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {source : V} {alpha gamma : C}
    (hK : a.IsTwoColorKempeComponent alpha gamma K)
    (halphaGamma : alpha ≠ gamma)
    (hsourceGamma : a.MissingAt source gamma)
    (hmeets : EdgeSetMeetsVertex K source) :
    (a.swapOn alpha gamma K).MissingAt source alpha :=
  (missingAt_left_swapOn_iff_of_component_meets
    a hK halphaGamma hmeets).2 hsourceGamma

/-- The dependency deleted from the `gamma` column is redirected to every
supplied center target carrying `alpha`: avoiding the center preserves that
target, while endpoint label transport makes `alpha` missing at the source. -/
theorem centerDependency_to_alphaTarget_swapOn_of_gamma_endpoint
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {center source alphaTarget : V}
    {alpha gamma : C}
    (hK : a.IsTwoColorKempeComponent alpha gamma K)
    (halphaGamma : alpha ≠ gamma)
    (hcenterAvoid : EdgeSetAvoidsVertex K center)
    (hsourceGamma : a.MissingAt source gamma)
    (hmeets : EdgeSetMeetsVertex K source)
    (htargetAlpha : a.IsCenterColorTarget
      J center alphaTarget alpha) :
    (a.swapOn alpha gamma K).CenterDependency
      J center source alphaTarget := by
  have htargetAlphaSwap :
      (a.swapOn alpha gamma K).IsCenterColorTarget
        J center alphaTarget alpha :=
    (isCenterColorTarget_swapOn_iff_of_avoids_center
      a J K hcenterAvoid).2 htargetAlpha
  exact (htargetAlphaSwap.centerDependency_iff_missingAt source).2
    (missingAt_alpha_swapOn_of_gamma_endpoint
      a K hK halphaGamma hsourceGamma hmeets)

end PartialEdgeAssignment

end TotalColoring
