import TotalColoring.CriticalComponentClosure
import TotalColoring.FanCount
import TotalColoring.FanLeaves
import TotalColoring.MissingGeneralCount

/-!
# Used-color multiplicity on critical reachable leaves

For every palette color, at most three dependency-reachable fan leaves can
miss that color.  This removes the ``unused on `J`'' hypothesis from the
earlier spare-color result at the level justified by the exact two-carrier
geometry.

The proof fixes a different color missing at the center and follows its
two-color component through the center.  A safe center component would contain
every relevant leaf, contradicting endpoint capacity.  Hence both colors have
unique distinguished carriers on opposite sides of that component.  Every
other relevant component is unsafe and contains the carrier outside the
center component.  The center component contributes at most one leaf endpoint
and the other component at most two.

No fan maximality, matching-carrier location, or recentering theorem is used.
-/

namespace TotalColoring

universe u

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- General numerical multiplicity bound on the whole dependency-reachable
leaf set.  Unlike the spare-color theorem, `gamma` may occur on `J`. -/
theorem ncard_missingAt_centerReachable_le_three
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (gamma : ExtensionPalette D) :
    ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard ≤ 3 := by
  classical
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf ∧
      a.MissingAt leaf gamma}
  change S.ncard ≤ 3
  by_contra hnot
  have hfour : 3 < S.ncard := Nat.lt_of_not_ge hnot
  rcases (Set.three_lt_ncard (s := S)).mp hfour with
    ⟨w₀, hw₀, w₁, hw₁, w₂, hw₂, w₃, hw₃,
      hw₀w₁, hw₀w₂, hw₀w₃, hw₁w₂, hw₁w₃, hw₂w₃⟩
  rcases h.member with ⟨x, M, hstructure⟩
  have htwo : 2 ≤ (a.missingColorsAt Finset.univ center).card :=
    PartialEdgeAssignment.two_le_missingColorsAt_card_of_palette_card_eq_of_degree_le
      a Finset.univ center D (by simp [ExtensionPalette])
        (hstructure.degree_le_parameter center)
  have hone : 1 < (a.missingColorsAt Finset.univ center).card := by
    omega
  rcases Finset.one_lt_card.mp hone with ⟨c, hc, d, hd, hcd⟩
  obtain ⟨alpha, halphaMissing, halphagamma⟩ :
      ∃ alpha : ExtensionPalette D,
        a.MissingAt center alpha ∧ alpha ≠ gamma := by
    by_cases hcgamma : c = gamma
    · refine ⟨d, (PartialEdgeAssignment.mem_missingColorsAt.mp hd).2, ?_⟩
      intro hdgamma
      exact hcd (hcgamma.trans hdgamma.symm)
    · exact ⟨c, (PartialEdgeAssignment.mem_missingColorsAt.mp hc).2,
        hcgamma⟩
  have hnotGammaCenter : ¬a.MissingAt center gamma := by
    intro hcenterGamma
    exact h.center_reachable_elementary root hrootJ hvalid hhole
      hrainbow hw₀.1 gamma ⟨hcenterGamma, hw₀.2⟩
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      a hnotGammaCenter with ⟨centerEdge, hcenterIncident, hcenterColor⟩
  let K := a.TwoColorReachabilityClass alpha gamma centerEdge
  have hcenterSupported : a.TwoColorSupported alpha gamma centerEdge :=
    Or.inr hcenterColor
  have hK : a.IsTwoColorKempeComponent alpha gamma K :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      a alpha gamma centerEdge hcenterSupported
  have hcenterEdgeK : centerEdge ∈ K :=
    a.root_mem_twoColorReachabilityClass alpha gamma centerEdge
  have hKcenter : EdgeSetMeetsVertex K center :=
    ⟨centerEdge, hcenterEdgeK, hcenterIncident⟩
  have hcenterEnd : EdgeSetIsEndpoint K center :=
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_left_of_component_meets
      hvalid hK halphaMissing hKcenter
  have hreachableNeCenter {w : V}
      (hw : a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf w) : w ≠ center :=
    PartialEdgeAssignment.centerReachable_ne_center a
      (distinguishedEdgeSet H J) root.leaf_ne_center hw
  have hKnotCompatible :
      ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha gamma K := by
    intro hcompatible
    have hmeet₀ :=
      h.component_meets_centerReachable_missing_right_of_swapCompatible
        root hrootJ hvalid hhole hrainbow hK halphagamma halphaMissing
        hKcenter hcompatible hw₀.1 hw₀.2
    have hmeet₁ :=
      h.component_meets_centerReachable_missing_right_of_swapCompatible
        root hrootJ hvalid hhole hrainbow hK halphagamma halphaMissing
        hKcenter hcompatible hw₁.1 hw₁.2
    have hend₀ :=
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK hw₀.2 hmeet₀
    have hend₁ :=
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK hw₁.2 hmeet₁
    rcases PartialEdgeAssignment.endpoint_triple_has_repetition_of_component
        hvalid hK hcenterEnd hend₀ hend₁ with hcw₀ | hcw₁ | hw
    · exact (hreachableNeCenter hw₀.1) hcw₀.symm
    · exact (hreachableNeCenter hw₁.1) hcw₁.symm
    · exact hw₀w₁ hw
  have hAlphaUsed :
      ¬a.ColorUnusedOn (distinguishedEdgeSet H J) alpha := by
    intro hunused
    exact hKnotCompatible
      (PartialEdgeAssignment.swapCompatibleOn_of_unused_left
        a (distinguishedEdgeSet H J) K hunused)
  have hGammaUsed :
      ¬a.ColorUnusedOn (distinguishedEdgeSet H J) gamma := by
    intro hunused
    exact hKnotCompatible
      (PartialEdgeAssignment.swapCompatibleOn_of_unused_right
        a (distinguishedEdgeSet H J) K hunused)
  rcases PartialEdgeAssignment.exists_uniqueColorOn_of_not_colorUnusedOn
      a (distinguishedEdgeSet H J) hrainbow hAlphaUsed with
    ⟨eAlpha, hAlpha⟩
  rcases PartialEdgeAssignment.exists_uniqueColorOn_of_not_colorUnusedOn
      a (distinguishedEdgeSet H J) hrainbow hGammaUsed with
    ⟨eGamma, hGamma⟩
  have hKopposite : ¬(eAlpha ∈ K ↔ eGamma ∈ K) := by
    intro hsame
    exact hKnotCompatible
      ((PartialEdgeAssignment.swapCompatibleOn_iff_of_uniqueColorOn
        a (distinguishedEdgeSet H J) K hAlpha hGamma).2 hsame)
  have hKsplit :
      (eAlpha ∈ K ∧ eGamma ∉ K) ∨
        (eAlpha ∉ K ∧ eGamma ∈ K) := by
    tauto
  have hbound_of_outside_carrier
      (eOut : H.edgeSet)
      (heOutK : eOut ∉ K)
      (heOutSupported : a.TwoColorSupported alpha gamma eOut)
      (hother : ∀ {Q : Set H.edgeSet},
        a.IsTwoColorKempeComponent alpha gamma Q →
        Q ≠ K →
        ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha gamma Q →
        eOut ∈ Q) : S.ncard ≤ 3 := by
    let L := a.TwoColorReachabilityClass alpha gamma eOut
    have hL : a.IsTwoColorKempeComponent alpha gamma L :=
      PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
        a alpha gamma eOut heOutSupported
    have heOutL : eOut ∈ L :=
      a.root_mem_twoColorReachabilityClass alpha gamma eOut
    let A : Set V := {w | EdgeSetIsEndpoint K w ∧ w ≠ center}
    let B : Set V := {w | EdgeSetIsEndpoint L w}
    have hA : A.ncard ≤ 1 := by
      apply Set.ncard_le_one_iff_subsingleton.mpr
      intro p hp q hq
      rcases PartialEdgeAssignment.endpoint_triple_has_repetition_of_component
          hvalid hK hcenterEnd hp.1 hq.1 with hcp | hcq | hpq
      · exact (hp.2 hcp.symm).elim
      · exact (hq.2 hcq.symm).elim
      · exact hpq
    have hB : B.ncard ≤ 2 :=
      PartialEdgeAssignment.edgeSetIsEndpoint_ncard_le_two_of_component
        hvalid hL
    have hsubset : S ⊆ A ∪ B := by
      intro w hw
      rcases h.exists_centerReachable_component_dichotomy
          root hrootJ hvalid hhole hrainbow halphagamma halphaMissing
          hw.1 hw.2 with ⟨Q, hQ, hwEnd, hQdichotomy⟩
      by_cases hQK : Q = K
      · left
        exact ⟨hQK ▸ hwEnd, hreachableNeCenter hw.1⟩
      · have hQnotCompatible :
            ¬a.SwapCompatibleOn (distinguishedEdgeSet H J)
              alpha gamma Q := by
          rcases hQdichotomy with hQcenter | hQunsafe
          · exfalso
            apply hQK
            exact PartialEdgeAssignment.components_eq_of_meet_vertex_missing_left
              hvalid hQ hK halphaMissing hQcenter hKcenter
          · exact hQunsafe
        have heOutQ := hother hQ hQK hQnotCompatible
        have hQL : Q = L :=
          PartialEdgeAssignment.isTwoColorKempeComponent_eq_of_common_member
            a hQ hL heOutQ heOutL
        right
        change EdgeSetIsEndpoint L w
        exact hQL ▸ hwEnd
    calc
      S.ncard ≤ (A ∪ B).ncard := Set.ncard_le_ncard hsubset
      _ ≤ A.ncard + B.ncard := Set.ncard_union_le A B
      _ ≤ 1 + 2 := Nat.add_le_add hA hB
      _ = 3 := rfl
  rcases hKsplit with hsplit | hsplit
  · apply (Nat.not_lt_of_ge ?_) hfour
    apply hbound_of_outside_carrier eGamma hsplit.2
      (Or.inr hGamma.2.1)
    intro Q hQ hQK hQunsafe
    have heAlphaQ : eAlpha ∉ Q := by
      intro heAlphaQ
      apply hQK
      exact PartialEdgeAssignment.isTwoColorKempeComponent_eq_of_common_member
        a hQ hK heAlphaQ hsplit.1
    have hQopposite : ¬(eAlpha ∈ Q ↔ eGamma ∈ Q) := by
      intro hsame
      exact hQunsafe
        ((PartialEdgeAssignment.swapCompatibleOn_iff_of_uniqueColorOn
          a (distinguishedEdgeSet H J) Q hAlpha hGamma).2 hsame)
    tauto
  · apply (Nat.not_lt_of_ge ?_) hfour
    apply hbound_of_outside_carrier eAlpha hsplit.1
      (Or.inl hAlpha.2.1)
    intro Q hQ hQK hQunsafe
    have heGammaQ : eGamma ∉ Q := by
      intro heGammaQ
      apply hQK
      exact PartialEdgeAssignment.isTwoColorKempeComponent_eq_of_common_member
        a hQ hK heGammaQ hsplit.2
    have hQopposite : ¬(eAlpha ∈ Q ↔ eGamma ∈ Q) := by
      intro hsame
      exact hQunsafe
        ((PartialEdgeAssignment.swapCompatibleOn_iff_of_uniqueColorOn
          a (distinguishedEdgeSet H J) Q hAlpha hGamma).2 hsame)
    tauto

/-- Finite selected-fan corollary of the whole reachable-set theorem. -/
theorem colorMultiplicity_leafFinset_le_three
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (gamma : ExtensionPalette D) :
    FanCount.colorMultiplicity F.leafFinset a.MissingAt gamma ≤ 3 := by
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center F.root.leaf leaf ∧
      a.MissingAt leaf gamma}
  have hsubset :
      (↑(F.leafFinset.filter fun leaf ↦ a.MissingAt leaf gamma) : Set V) ⊆
        S := by
    intro leaf hleaf
    have hparts := (Finset.mem_filter.mp hleaf)
    exact ⟨F.centerReachable_of_mem_leafFinset hparts.1, hparts.2⟩
  have hmono := Set.ncard_le_ncard hsubset
  have hbound : S.ncard ≤ 3 :=
    h.ncard_missingAt_centerReachable_le_three F.root F.root_not_mem
      hvalid hhole hrainbow gamma
  change (F.leafFinset.filter fun leaf ↦ a.MissingAt leaf gamma).card ≤ 3
  rw [← Set.ncard_coe_finset]
  exact hmono.trans hbound

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
