import TotalColoring.CriticalUsedColorMultiplicity
import TotalColoring.ResidualDegree

/-!
# Matching location of saturated critical carriers

The auxiliary distinguished set is a matching plus the star of a special
vertex.  This module first isolates the structural carrier-location fact: if
two distinct two-color components split the two unique distinguished
carriers, and both components already have two distinct endpoints away from
the special vertex, then neither carrier can lie in the star.  Hence both lie
in the matching.

The critical three-leaf wrapper is proved below this structural seam.  This is
the local matching-carrier theorem; it is not the later uniform endpoint or
recentered reachable-location result.
-/

namespace TotalColoring

universe u v

namespace IsAuxiliaryClassMember

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- In an auxiliary-class member, a distinguished edge belongs to the
matching exactly when it is not incident with the special star center. -/
theorem mem_matching_iff_mem_distinguishedEdgeSet_and_not_incident_center
    (h : IsAuxiliaryClassMember D H x J M) (e : H.edgeSet) :
    (e : Sym2 V) ∈ M ↔
      e ∈ distinguishedEdgeSet H J ∧ ¬Incident x e := by
  constructor
  · intro heM
    refine ⟨?_, ?_⟩
    · change (e : Sym2 V) ∈ J
      rw [h.decomposition]
      exact Finset.mem_union_left _ heM
    · exact fun hxe ↦ h.matching_off_center heM hxe
  · rintro ⟨heJ, hnotIncident⟩
    change (e : Sym2 V) ∈ J at heJ
    rw [h.decomposition] at heJ
    rcases Finset.mem_union.mp heJ with heM | heStar
    · exact heM
    · exact (hnotIncident ((H.mem_incidenceFinset x (e : Sym2 V)).1
        heStar).2).elim

/-- The fan center and every dependency-reachable leaf differ from the
auxiliary star center when the root spoke is outside `J`. -/
theorem fan_center_and_centerReachable_leaf_ne_auxiliary_center
    (h : IsAuxiliaryClassMember D H x J M)
    {C : Type v} {a : PartialEdgeAssignment H C} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    {leaf : V}
    (hreach : a.CenterReachable (distinguishedEdgeSet H J)
      center root.leaf leaf) :
    center ≠ x ∧ leaf ≠ x := by
  have hrootJ' : (root.edge : Sym2 V) ∉ J := hrootJ
  have hrootEnds := h.outside_edge_endpoints_ne_center
    root.edge hrootJ' root.endpoints
  refine ⟨hrootEnds.1, ?_⟩
  rcases PartialEdgeAssignment.centerReachable_eq_root_or_isCenterTarget
      hreach with hleaf | htarget
  · subst leaf
    exact hrootEnds.2
  · rcases htarget with ⟨e, c, hends, heJ, hcolor⟩
    have heJ' : (e : Sym2 V) ∉ J := heJ
    exact (h.outside_edge_endpoints_ne_center e heJ' hends).2

end IsAuxiliaryClassMember

namespace PartialEdgeAssignment

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- If two distinct components split the two distinguished carriers and each
is saturated by two endpoints away from the auxiliary center, both carriers
belong to the matching part of `J`. -/
theorem carriers_mem_matching_of_split_saturated_components
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {C : Type v} {a : PartialEdgeAssignment H C}
    (hvalid : a.Valid)
    {alpha gamma : C}
    {eAlpha eGamma : H.edgeSet}
    (hAlpha : a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha eAlpha)
    (hGamma : a.IsUniqueColorOn (distinguishedEdgeSet H J) gamma eGamma)
    {K L : Set H.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha gamma K)
    (hL : a.IsTwoColorKempeComponent alpha gamma L)
    (hKL : K ≠ L)
    (hsplit :
      (eAlpha ∈ K ∧ eGamma ∈ L) ∨
      (eGamma ∈ K ∧ eAlpha ∈ L))
    (hKsat : ∃ p q : V, p ≠ q ∧ p ≠ x ∧ q ≠ x ∧
      EdgeSetIsEndpoint K p ∧ EdgeSetIsEndpoint K q)
    (hLsat : ∃ p q : V, p ≠ q ∧ p ≠ x ∧ q ≠ x ∧
      EdgeSetIsEndpoint L p ∧ EdgeSetIsEndpoint L q) :
    (eAlpha : Sym2 V) ∈ M ∧ (eGamma : Sym2 V) ∈ M := by
  have hbothStarImpossible
      (hxa : Incident x eAlpha) (hxg : Incident x eGamma) : False := by
    rcases hsplit with hsplit | hsplit
    · have heGammaK : eGamma ∈ K :=
        a.mem_component_of_mem_of_incident_supported hK hsplit.1 hxa hxg
          (Or.inr hGamma.2.1)
      exact hKL (a.isTwoColorKempeComponent_eq_of_common_member
        hK hL heGammaK hsplit.2)
    · have heAlphaK : eAlpha ∈ K :=
        a.mem_component_of_mem_of_incident_supported hK hsplit.1 hxg hxa
          (Or.inl hAlpha.2.1)
      exact hKL (a.isTwoColorKempeComponent_eq_of_common_member
        hK hL heAlphaK hsplit.2)
  have hmissingGammaAtX (hxg : ¬Incident x eGamma) :
      a.MissingAt x gamma := by
    intro f hxf hfgamma
    have hfJ : f ∈ distinguishedEdgeSet H J :=
      hstructure.center_incident_mem_distinguishedEdgeSet f hxf
    have hfeq : f = eGamma := hGamma.2.2 hfJ hfgamma
    exact hxg (hfeq ▸ hxf)
  have hmissingAlphaAtX (hxa : ¬Incident x eAlpha) :
      a.MissingAt x alpha := by
    intro f hxf hfalpha
    have hfJ : f ∈ distinguishedEdgeSet H J :=
      hstructure.center_incident_mem_distinguishedEdgeSet f hxf
    have hfeq : f = eAlpha := hAlpha.2.2 hfJ hfalpha
    exact hxa (hfeq ▸ hxf)
  have hsaturated_contra
      {S : Set H.edgeSet}
      (hS : a.IsTwoColorKempeComponent alpha gamma S)
      (hsat : ∃ p q : V, p ≠ q ∧ p ≠ x ∧ q ≠ x ∧
        EdgeSetIsEndpoint S p ∧ EdgeSetIsEndpoint S q)
      (hxend : EdgeSetIsEndpoint S x) : False := by
    rcases hsat with ⟨p, q, hpq, hpx, hqx, hpEnd, hqEnd⟩
    rcases endpoint_triple_has_repetition_of_component hvalid hS
        hxend hpEnd hqEnd with hxp | hxq | hpq'
    · exact hpx hxp.symm
    · exact hqx hxq.symm
    · exact hpq hpq'
  have hnotAlphaStar : ¬Incident x eAlpha := by
    intro hxa
    by_cases hxg : Incident x eGamma
    · exact hbothStarImpossible hxa hxg
    · rcases hsplit with hsplit | hsplit
      · have hxMeets : EdgeSetMeetsVertex K x := ⟨eAlpha, hsplit.1, hxa⟩
        have hxEnd := edgeSetIsEndpoint_of_missing_right_of_component_meets
          hvalid hK (hmissingGammaAtX hxg) hxMeets
        exact hsaturated_contra hK hKsat hxEnd
      · have hxMeets : EdgeSetMeetsVertex L x := ⟨eAlpha, hsplit.2, hxa⟩
        have hxEnd := edgeSetIsEndpoint_of_missing_right_of_component_meets
          hvalid hL (hmissingGammaAtX hxg) hxMeets
        exact hsaturated_contra hL hLsat hxEnd
  have hnotGammaStar : ¬Incident x eGamma := by
    intro hxg
    rcases hsplit with hsplit | hsplit
    · have hxMeets : EdgeSetMeetsVertex L x := ⟨eGamma, hsplit.2, hxg⟩
      have hxEnd := edgeSetIsEndpoint_of_missing_left_of_component_meets
        hvalid hL (hmissingAlphaAtX hnotAlphaStar) hxMeets
      exact hsaturated_contra hL hLsat hxEnd
    · have hxMeets : EdgeSetMeetsVertex K x := ⟨eGamma, hsplit.1, hxg⟩
      have hxEnd := edgeSetIsEndpoint_of_missing_left_of_component_meets
        hvalid hK (hmissingAlphaAtX hnotAlphaStar) hxMeets
      exact hsaturated_contra hK hKsat hxEnd
  exact ⟨
    (hstructure.mem_matching_iff_mem_distinguishedEdgeSet_and_not_incident_center
      eAlpha).2 ⟨hAlpha.1, hnotAlphaStar⟩,
    (hstructure.mem_matching_iff_mem_distinguishedEdgeSet_and_not_incident_center
      eGamma).2 ⟨hGamma.1, hnotGammaStar⟩⟩

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {x : V} {J M : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Local three-leaf carrier theorem.  If `alpha` is missing at the fan center
and `gamma` is missing at at least three dependency-reachable leaves, then the
two unique distinguished carriers both lie in the matching part of the fixed
auxiliary-class presentation.

This is the saturated exact-two-component residual used early in the proof
program.  It is not the later uniform endpoint or recentered reachable
matching-location theorem. -/
theorem exists_matching_carriers_of_three_missing_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    (hstructure : IsAuxiliaryClassMember D H x J M)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha gamma : ExtensionPalette D} (halphagamma : alpha ≠ gamma)
    (hcenter : a.MissingAt center alpha)
    (hthree : 3 ≤ ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf gamma} : Set V).ncard) :
    ∃ eAlpha eGamma : H.edgeSet,
      a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha eAlpha ∧
      a.IsUniqueColorOn (distinguishedEdgeSet H J) gamma eGamma ∧
      (eAlpha : Sym2 V) ∈ M ∧ (eGamma : Sym2 V) ∈ M := by
  classical
  let S : Set V := {leaf : V |
    a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf ∧
      a.MissingAt leaf gamma}
  have hthree' : 2 < S.ncard := by
    change 3 ≤ S.ncard at hthree
    omega
  rcases (Set.two_lt_ncard_iff (s := S)).mp hthree' with
    ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, hw₀w₁, hw₀w₂, hw₁w₂⟩
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
      hvalid hK hcenter hKcenter
  have hreachableNeCenter {w : V}
      (hw : a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf w) : w ≠ center :=
    PartialEdgeAssignment.centerReachable_ne_center a
      (distinguishedEdgeSet H J) root.leaf_ne_center hw
  have hleafNeX {w : V}
      (hw : a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf w) : w ≠ x :=
    (hstructure.fan_center_and_centerReachable_leaf_ne_auxiliary_center
      root hrootJ hw).2
  have hcenterNeX : center ≠ x :=
    (hstructure.fan_center_and_centerReachable_leaf_ne_auxiliary_center
      root hrootJ hw₀.1).1
  have hKnotCompatible :
      ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha gamma K := by
    intro hcompatible
    have hmeet₀ :=
      h.component_meets_centerReachable_missing_right_of_swapCompatible
        root hrootJ hvalid hhole hrainbow hK halphagamma hcenter
        hKcenter hcompatible hw₀.1 hw₀.2
    have hmeet₁ :=
      h.component_meets_centerReachable_missing_right_of_swapCompatible
        root hrootJ hvalid hhole hrainbow hK halphagamma hcenter
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
  have hpairK : ∀ {p q : V}, p ∈ S → q ∈ S →
      EdgeSetMeetsVertex K p → EdgeSetMeetsVertex K q → p = q := by
    intro p q hp hq hpK hqK
    have hpEnd : EdgeSetIsEndpoint K p :=
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK hp.2 hpK
    have hqEnd : EdgeSetIsEndpoint K q :=
      PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
        hvalid hK hq.2 hqK
    rcases PartialEdgeAssignment.endpoint_triple_has_repetition_of_component
        hvalid hK hcenterEnd hpEnd hqEnd with hcp | hcq | hpq
    · exact (hreachableNeCenter hp.1 hcp.symm).elim
    · exact (hreachableNeCenter hq.1 hcq.symm).elim
    · exact hpq
  have hfinish
      (eOut : H.edgeSet)
      (heOutK : eOut ∉ K)
      (heOutSupported : a.TwoColorSupported alpha gamma eOut)
      (hsplitKL : ∀ {L : Set H.edgeSet}, eOut ∈ L →
        (eAlpha ∈ K ∧ eGamma ∈ L) ∨
          (eGamma ∈ K ∧ eAlpha ∈ L))
      (hother : ∀ {Q : Set H.edgeSet},
        a.IsTwoColorKempeComponent alpha gamma Q →
        Q ≠ K →
        ¬a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha gamma Q →
        eOut ∈ Q) :
      (eAlpha : Sym2 V) ∈ M ∧ (eGamma : Sym2 V) ∈ M := by
    let L := a.TwoColorReachabilityClass alpha gamma eOut
    have hL : a.IsTwoColorKempeComponent alpha gamma L :=
      PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
        a alpha gamma eOut heOutSupported
    have heOutL : eOut ∈ L :=
      a.root_mem_twoColorReachabilityClass alpha gamma eOut
    have hLK : L ≠ K := by
      intro hEq
      exact heOutK (hEq ▸ heOutL)
    have houtsideEnd : ∀ {w : V}, w ∈ S →
        ¬EdgeSetMeetsVertex K w → EdgeSetIsEndpoint L w := by
      intro w hw hwK
      rcases h.exists_centerReachable_component_dichotomy
          root hrootJ hvalid hhole hrainbow halphagamma hcenter
          hw.1 hw.2 with ⟨Q, hQ, hwEnd, hQdichotomy⟩
      have hQK : Q ≠ K := by
        intro hEq
        apply hwK
        subst Q
        exact ⟨hwEnd.choose, hwEnd.choose_spec.1,
          hwEnd.choose_spec.2.1⟩
      have hQnotCompatible :
          ¬a.SwapCompatibleOn (distinguishedEdgeSet H J)
            alpha gamma Q := by
        rcases hQdichotomy with hQcenter | hQunsafe
        · exfalso
          apply hQK
          exact PartialEdgeAssignment.components_eq_of_meet_vertex_missing_left
            hvalid hQ hK hcenter hQcenter hKcenter
        · exact hQunsafe
      have heOutQ := hother hQ hQK hQnotCompatible
      have hQL : Q = L :=
        PartialEdgeAssignment.isTwoColorKempeComponent_eq_of_common_member
          a hQ hL heOutQ heOutL
      exact hQL ▸ hwEnd
    have hsomeK :
        EdgeSetMeetsVertex K w₀ ∨ EdgeSetMeetsVertex K w₁ ∨
          EdgeSetMeetsVertex K w₂ := by
      by_contra hnone
      push Not at hnone
      have hend₀ := houtsideEnd hw₀ hnone.1
      have hend₁ := houtsideEnd hw₁ hnone.2.1
      have hend₂ := houtsideEnd hw₂ hnone.2.2
      rcases PartialEdgeAssignment.endpoint_triple_has_repetition_of_component
          hvalid hL hend₀ hend₁ hend₂ with hw | hw | hw
      · exact hw₀w₁ hw
      · exact hw₀w₂ hw
      · exact hw₁w₂ hw
    have hsaturated :
        (∃ p q : V, p ≠ q ∧ p ≠ x ∧ q ≠ x ∧
          EdgeSetIsEndpoint K p ∧ EdgeSetIsEndpoint K q) ∧
        (∃ p q : V, p ≠ q ∧ p ≠ x ∧ q ≠ x ∧
          EdgeSetIsEndpoint L p ∧ EdgeSetIsEndpoint L q) := by
      rcases hsomeK with hKw₀ | hKw₁ | hKw₂
      · have hKw₁ : ¬EdgeSetMeetsVertex K w₁ := by
          intro hmeet
          exact hw₀w₁ (hpairK hw₀ hw₁ hKw₀ hmeet)
        have hKw₂ : ¬EdgeSetMeetsVertex K w₂ := by
          intro hmeet
          exact hw₀w₂ (hpairK hw₀ hw₂ hKw₀ hmeet)
        refine ⟨⟨center, w₀, (hreachableNeCenter hw₀.1).symm,
          hcenterNeX, hleafNeX hw₀.1, hcenterEnd, ?_⟩,
          ⟨w₁, w₂, hw₁w₂, hleafNeX hw₁.1, hleafNeX hw₂.1,
            houtsideEnd hw₁ hKw₁, houtsideEnd hw₂ hKw₂⟩⟩
        exact PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
          hvalid hK hw₀.2 hKw₀
      · have hKw₀ : ¬EdgeSetMeetsVertex K w₀ := by
          intro hmeet
          exact hw₀w₁ (hpairK hw₀ hw₁ hmeet hKw₁)
        have hKw₂ : ¬EdgeSetMeetsVertex K w₂ := by
          intro hmeet
          exact hw₁w₂ (hpairK hw₁ hw₂ hKw₁ hmeet)
        refine ⟨⟨center, w₁, (hreachableNeCenter hw₁.1).symm,
          hcenterNeX, hleafNeX hw₁.1, hcenterEnd, ?_⟩,
          ⟨w₀, w₂, hw₀w₂, hleafNeX hw₀.1, hleafNeX hw₂.1,
            houtsideEnd hw₀ hKw₀, houtsideEnd hw₂ hKw₂⟩⟩
        exact PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
          hvalid hK hw₁.2 hKw₁
      · have hKw₀ : ¬EdgeSetMeetsVertex K w₀ := by
          intro hmeet
          exact hw₀w₂ (hpairK hw₀ hw₂ hmeet hKw₂)
        have hKw₁ : ¬EdgeSetMeetsVertex K w₁ := by
          intro hmeet
          exact hw₁w₂ (hpairK hw₁ hw₂ hmeet hKw₂)
        refine ⟨⟨center, w₂, (hreachableNeCenter hw₂.1).symm,
          hcenterNeX, hleafNeX hw₂.1, hcenterEnd, ?_⟩,
          ⟨w₀, w₁, hw₀w₁, hleafNeX hw₀.1, hleafNeX hw₁.1,
            houtsideEnd hw₀ hKw₀, houtsideEnd hw₁ hKw₁⟩⟩
        exact PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
          hvalid hK hw₂.2 hKw₂
    exact PartialEdgeAssignment.carriers_mem_matching_of_split_saturated_components
      hstructure hvalid hAlpha hGamma hK hL (Ne.symm hLK)
        (hsplitKL heOutL) hsaturated.1 hsaturated.2
  refine ⟨eAlpha, eGamma, hAlpha, hGamma, ?_⟩
  rcases hKsplit with hsplit | hsplit
  · apply hfinish eGamma hsplit.2 (Or.inr hGamma.2.1)
    · intro L heGammaL
      exact Or.inl ⟨hsplit.1, heGammaL⟩
    · intro Q hQ hQK hQunsafe
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
  · apply hfinish eAlpha hsplit.1 (Or.inl hAlpha.2.1)
    · intro L heAlphaL
      exact Or.inr ⟨hsplit.2, heAlphaL⟩
    · intro Q hQ hQK hQunsafe
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

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
