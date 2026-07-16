import TotalColoring.TwoColorEndpointCapacity
import TotalColoring.CriticalAllLeaf
import TotalColoring.MissingGeneralCount
import TotalColoring.FanLeaves
import TotalColoring.FanCount

/-!
# Spare-color multiplicity on critical fan leaves

In a supplied minimal noncolorable state, let `delta` be unused on the
distinguished edge set.  Exact all-leaf closure forces every relevant
two-color component through the fan center.  Two such components share the
unique `delta`-colored center edge and are therefore the same component.
Global two-endpoint capacity then forbids `delta` from being missing at two
distinct dependency-reachable fan leaves.

The result is a multiplicity-one theorem for colors unused on `J`.  It is not
the general fan multiplicity-two statement.
-/

namespace TotalColoring

universe u

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type*}

/-- A color which is not missing at a vertex is witnessed by an incident edge
of that actual color. -/
theorem exists_incident_colored_edge_of_not_missing
    (a : PartialEdgeAssignment G C) {v : V} {c : C}
    (hnot : ¬a.MissingAt v c) :
    ∃ e : G.edgeSet, Incident v e ∧ a.color e = some c := by
  classical
  rw [MissingAt] at hnot
  push Not at hnot
  exact hnot

/-- Two genuine components for the same ordered color pair which both meet a
vertex missing the first color are equal.  Validity makes their incident
second-color edges equal, supplying the common member. -/
theorem components_eq_of_meet_vertex_missing_left
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K L : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (hL : a.IsTwoColorKempeComponent alpha beta L)
    {v : V} (hmissing : a.MissingAt v alpha)
    (hKv : EdgeSetMeetsVertex K v) (hLv : EdgeSetMeetsVertex L v) :
    K = L := by
  rcases hKv with ⟨e, heK, hve⟩
  rcases hLv with ⟨f, hfL, hvf⟩
  have hebeta : a.color e = some beta :=
    (twoColorSupported_of_mem_component a hK heK).resolve_left
      (hmissing e hve)
  have hfbeta : a.color f = some beta :=
    (twoColorSupported_of_mem_component a hL hfL).resolve_left
      (hmissing f hvf)
  have hef : e = f :=
    edge_eq_of_incident_of_color_eq hvalid hve hvf hebeta hfbeta
  subst f
  exact isTwoColorKempeComponent_eq_of_common_member a hK hL heK hfL

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

private theorem exists_terminal_component_meeting_center_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha delta : ExtensionPalette D} (halphadelta : alpha ≠ delta)
    (hcenter : a.MissingAt center alpha)
    (hterminal : a.MissingAt F.terminal.leaf delta)
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta) :
    ∃ K : Set H.edgeSet,
      a.IsTwoColorKempeComponent alpha delta K ∧
      EdgeSetMeetsVertex K center ∧
      EdgeSetMeetsVertex K F.terminal.leaf := by
  classical
  have hnotAlpha : ¬a.MissingAt F.terminal.leaf alpha := by
    intro hterminalAlpha
    exact h.center_terminal_elementary F hvalid hhole hrainbow alpha
      ⟨hcenter, hterminalAlpha⟩
  rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
      a hnotAlpha with ⟨root, hrootTerminal, hrootColor⟩
  let K := a.TwoColorReachabilityClass alpha delta root
  have hrootSupported : a.TwoColorSupported alpha delta root :=
    Or.inl hrootColor
  have hK : a.IsTwoColorKempeComponent alpha delta K :=
    PartialEdgeAssignment.isTwoColorKempeComponent_reachabilityClass
      a alpha delta root hrootSupported
  have hrootK : root ∈ K :=
    a.root_mem_twoColorReachabilityClass alpha delta root
  have hmeetsTerminal : EdgeSetMeetsVertex K F.terminal.leaf :=
    ⟨root, hrootK, hrootTerminal⟩
  have hmeetsCenter := h.component_meets_center_of_one_unused F
    hvalid hhole hrainbow hK halphadelta hcenter hterminal
    hmeetsTerminal (Or.inr hunused)
  exact ⟨K, hK, hmeetsCenter, hmeetsTerminal⟩

/-- A color unused on `J` cannot be missing at the two distinct terminals of
two fan paths with the same root. -/
theorem terminal_leaf_eq_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F Q : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hroot : Q.root = F.root)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha delta : ExtensionPalette D} (halphadelta : alpha ≠ delta)
    (hcenter : a.MissingAt center alpha)
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    (hFmissing : a.MissingAt F.terminal.leaf delta)
    (hQmissing : a.MissingAt Q.terminal.leaf delta) :
    F.terminal.leaf = Q.terminal.leaf := by
  classical
  have hQhole : a.OneHoleAt Q.root.edge := by
    simpa [hroot] using hhole
  rcases h.exists_terminal_component_meeting_center_of_unused F
      hvalid hhole hrainbow halphadelta hcenter hFmissing hunused with
    ⟨K, hK, hKcenter, hKF⟩
  rcases h.exists_terminal_component_meeting_center_of_unused Q
      hvalid hQhole hrainbow halphadelta hcenter hQmissing hunused with
    ⟨L, hL, hLcenter, hLQ⟩
  have hKL : K = L :=
    PartialEdgeAssignment.components_eq_of_meet_vertex_missing_left
      hvalid hK hL hcenter hKcenter hLcenter
  subst L
  have hcenterEnd : EdgeSetIsEndpoint K center :=
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_left_of_component_meets
      hvalid hK hcenter hKcenter
  have hFEnd : EdgeSetIsEndpoint K F.terminal.leaf :=
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
      hvalid hK hFmissing hKF
  have hQEnd : EdgeSetIsEndpoint K Q.terminal.leaf :=
    PartialEdgeAssignment.edgeSetIsEndpoint_of_missing_right_of_component_meets
      hvalid hK hQmissing hLQ
  rcases PartialEdgeAssignment.endpoint_triple_has_repetition_of_component
      hvalid hK hcenterEnd hFEnd hQEnd with h | h | h
  · exact (F.terminal.leaf_ne_center h.symm).elim
  · exact (Q.terminal.leaf_ne_center h.symm).elim
  · exact h

/-- For a color unused on `J`, the dependency-reachable leaves at which that
color is missing form a subsingleton. -/
theorem missingAt_centerReachable_subsingleton_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (delta : ExtensionPalette D)
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta) :
    ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf delta} : Set V).Subsingleton := by
  classical
  rcases h.member with ⟨x, M, hstructure⟩
  have htwo : 2 ≤ (a.missingColorsAt Finset.univ center).card :=
    PartialEdgeAssignment.two_le_missingColorsAt_card_of_palette_card_eq_of_degree_le
      a Finset.univ center D (by simp [ExtensionPalette])
        (hstructure.degree_le_parameter center)
  have hone : 1 < (a.missingColorsAt Finset.univ center).card := by
    omega
  rcases Finset.one_lt_card.mp hone with ⟨c, hc, d, hd, hcd⟩
  obtain ⟨alpha, halphaMissing, halphadelta⟩ :
      ∃ alpha : ExtensionPalette D,
        a.MissingAt center alpha ∧ alpha ≠ delta := by
    by_cases hcdelta : c = delta
    · refine ⟨d, (PartialEdgeAssignment.mem_missingColorsAt.mp hd).2, ?_⟩
      intro hddelta
      exact hcd (hcdelta.trans hddelta.symm)
    · exact ⟨c, (PartialEdgeAssignment.mem_missingColorsAt.mp hc).2,
        hcdelta⟩
  intro v hv w hw
  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      root hrootJ hv.1 with ⟨F, hFroot, hFterminal⟩
  rcases PartialEdgeAssignment.exists_linearFanPath_of_centerReachable
      root hrootJ hw.1 with ⟨Q, hQroot, hQterminal⟩
  have hFhole : a.OneHoleAt F.root.edge := by
    simpa [hFroot] using hhole
  have hrootEq : Q.root = F.root := hQroot.trans hFroot.symm
  have hFmissing : a.MissingAt F.terminal.leaf delta := by
    simpa [hFterminal] using hv.2
  have hQmissing : a.MissingAt Q.terminal.leaf delta := by
    simpa [hQterminal] using hw.2
  have hterminalEq := h.terminal_leaf_eq_of_unused F Q hrootEq
    hvalid hFhole hrainbow halphadelta halphaMissing hunused
    hFmissing hQmissing
  exact hFterminal.symm.trans (hterminalEq.trans hQterminal)

/-- Numerical form of spare-color multiplicity one on the whole reachable
leaf set. -/
theorem ncard_missingAt_centerReachable_le_one_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (delta : ExtensionPalette D)
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta) :
    ({leaf : V |
      a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf leaf ∧
        a.MissingAt leaf delta} : Set V).ncard ≤ 1 := by
  exact Set.ncard_le_one_iff_subsingleton.mpr
    (h.missingAt_centerReachable_subsingleton_of_unused root hrootJ
      hvalid hhole hrainbow delta hunused)

/-- A color unused on `J` has multiplicity at most one on the finite leaf set
of any selected linear fan path. -/
theorem colorMultiplicity_leafFinset_le_one_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    (delta : ExtensionPalette D)
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta) :
    FanCount.colorMultiplicity F.leafFinset a.MissingAt delta ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro v hv w hw
  simp only [Finset.mem_filter] at hv hw
  apply h.missingAt_centerReachable_subsingleton_of_unused F.root
    F.root_not_mem hvalid hhole hrainbow delta hunused
  · exact ⟨F.centerReachable_of_mem_leafFinset hv.1, hv.2⟩
  · exact ⟨F.centerReachable_of_mem_leafFinset hw.1, hw.2⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
