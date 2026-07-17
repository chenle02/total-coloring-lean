import TotalColoring.CriticalReachableCount

/-!
# State-local fan capacity

For the canonical dependency-reachable leaf set `W`, let `a` be the number
of colors missing at the fan center and let `z` count the colors unused on
the distinguished set which are missing at some vertex of `W`.  This module proves the
state-local additive capacity bound

`|W| + a <= D + z`.

The physical universe is counted exactly: it is in bijection with the colors
present at the center, giving the additive form `|L| + a = D + 2` after the
palette partition.

It also proves the separate lower bound `4 <= |W|` when a triply missing
color is explicitly mobile, meaning that it has a colored non-distinguished
center edge.  Nothing here proves that an arbitrary triply missing color is
mobile.  The proofs use neither centered rotation nor matching location nor
cross-state/global maximality of `W`.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

section UnusedColors

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Palette colors unused on a selected edge set. -/
noncomputable def colorUnusedOnFinset [Fintype C]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet) : Finset C := by
  classical
  exact Finset.univ.filter fun color ↦ a.ColorUnusedOn J color

@[simp]
theorem mem_colorUnusedOnFinset_iff [Fintype C]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet) (color : C) :
    color ∈ a.colorUnusedOnFinset J ↔ a.ColorUnusedOn J color := by
  classical
  simp [colorUnusedOnFinset]

end UnusedColors

section PhysicalFinset

variable {V : Type u} [Fintype V]
variable {G : SimpleGraph V} {C : Type v}

/-- Finite wrapper for the physical leaf universe: the root together with
the heads of colored non-distinguished center edges. -/
noncomputable def centerPhysicalFinset
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) : Finset V := by
  classical
  exact Finset.univ.filter fun vertex ↦
    vertex ∈ a.centerPhysicalSet J center root

@[simp]
theorem mem_centerPhysicalFinset_iff
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root vertex : V) :
    vertex ∈ a.centerPhysicalFinset J center root ↔
      vertex ∈ a.centerPhysicalSet J center root := by
  classical
  simp [centerPhysicalFinset]

end PhysicalFinset

section LastArc

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- The last arc of a nontrivial reachable path into a fixed physical head
has as source a reachable vertex missing the color on that head's center
edge. -/
theorem exists_reachable_missing_of_reachable_centerEdge
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {center root target : V} {color : C} {edge : G.edgeSet}
    (hreach : a.CenterReachable J center root target)
    (htargetNeRoot : target ≠ root)
    (hends : (edge : Sym2 V) = s(center, target))
    (hcolor : a.color edge = some color) :
    ∃ source : V,
      a.CenterReachable J center root source ∧ a.MissingAt source color := by
  induction hreach with
  | refl => exact (htargetNeRoot rfl).elim
  | @tail source target hsource hstep _ =>
      rcases hstep with ⟨stepEdge, stepColor, hstepEnds, -, hstepColor,
        hmissing⟩
      have hedge : stepEdge = edge :=
        centerEdge_eq_of_endpoints hstepEnds hends
      have hcolors : stepColor = color := by
        apply Option.some.inj
        calc
          some stepColor = a.color stepEdge := hstepColor.symm
          _ = a.color edge := congrArg a.color hedge
          _ = some color := hcolor
      exact ⟨source, hsource, hcolors ▸ hmissing⟩

end LastArc

section MobileTriple

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} {C : Type v}

/-- A mobile color missing at three reachable leaves forces four reachable
vertices: its non-distinguished center-edge head is the fourth one. -/
theorem four_le_card_centerReachableFinset_of_three_missing_of_mobile
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    {center root : V} {gamma : C}
    (hthree : 3 ≤ ({leaf : V |
      a.CenterReachable J center root leaf ∧ a.MissingAt leaf gamma} : Set V).ncard)
    {eGamma : G.edgeSet}
    (hcenterEdge : Incident center eGamma)
    (heGammaJ : eGamma ∉ J)
    (hcolor : a.color eGamma = some gamma) :
    4 ≤ (a.centerReachableFinset J center root).card := by
  classical
  let S : Set V := {leaf : V |
    a.CenterReachable J center root leaf ∧ a.MissingAt leaf gamma}
  have hthree' : 2 < S.ncard := by
    change 3 ≤ S.ncard at hthree
    omega
  rcases (Set.two_lt_ncard_iff (s := S)).mp hthree' with
    ⟨w₀, w₁, w₂, hw₀, hw₁, hw₂, hw₀w₁, hw₀w₂, hw₁w₂⟩
  rcases Sym2.mem_iff_exists.mp hcenterEdge with ⟨target, htargetEnds⟩
  have htargetIncident : Incident target eGamma := by
    change target ∈ (eGamma : Sym2 V)
    rw [htargetEnds]
    exact Sym2.mem_mk_right center target
  have htargetNotMissing : ¬a.MissingAt target gamma := by
    intro hmissing
    exact hmissing eGamma htargetIncident hcolor
  have htargetReach : a.CenterReachable J center root target := by
    apply centerReachable_tail hw₀.1
    exact ⟨eGamma, gamma, htargetEnds, heGammaJ, hcolor, hw₀.2⟩
  have htargetNe₀ : target ≠ w₀ := by
    intro heq
    exact htargetNotMissing (heq ▸ hw₀.2)
  have htargetNe₁ : target ≠ w₁ := by
    intro heq
    exact htargetNotMissing (heq ▸ hw₁.2)
  have htargetNe₂ : target ≠ w₂ := by
    intro heq
    exact htargetNotMissing (heq ▸ hw₂.2)
  let Q : Finset V := {w₀, w₁, w₂, target}
  have hw₂Not : w₂ ∉ ({target} : Finset V) := by
    simpa using htargetNe₂.symm
  have hw₁Not : w₁ ∉ ({w₂, target} : Finset V) := by
    simp [hw₁w₂, htargetNe₁.symm]
  have hw₀Not : w₀ ∉ ({w₁, w₂, target} : Finset V) := by
    simp [hw₀w₁, hw₀w₂, htargetNe₀.symm]
  have hQcard : Q.card = 4 := by
    rw [show Q = insert w₀ {w₁, w₂, target} by rfl,
      Finset.card_insert_of_notMem hw₀Not,
      Finset.card_insert_of_notMem hw₁Not,
      Finset.card_insert_of_notMem hw₂Not]
    simp
  have hQsub : Q ⊆ a.centerReachableFinset J center root := by
    intro w hw
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with hw | hw | hw | hw
    · subst w
      exact (mem_centerReachableFinset_iff a J center root w₀).2 hw₀.1
    · subst w
      exact (mem_centerReachableFinset_iff a J center root w₁).2 hw₁.1
    · subst w
      exact (mem_centerReachableFinset_iff a J center root w₂).2 hw₂.1
    · subst w
      exact (mem_centerReachableFinset_iff a J center root target).2 htargetReach
  rw [← hQcard]
  exact Finset.card_le_card hQsub

end MobileTriple

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A rainbow `D`-edge distinguished set in the `D+2` palette leaves exactly
two unused colors. -/
theorem card_colorUnusedOnFinset_eq_two
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    (a.colorUnusedOnFinset (distinguishedEdgeSet H J)).card = 2 := by
  classical
  let U := a.colorUnusedOnFinset (distinguishedEdgeSet H J)
  let P := (Finset.univ : Finset (ExtensionPalette D)) \ U
  rcases h.member with ⟨x, M, hstructure⟩
  let edgeColor :
      {e : H.edgeSet // e ∈ distinguishedEdgeSet H J} →
        ExtensionPalette D := fun e ↦ Classical.choose (hrainbow.1 e.1 e.2)
  have hedgeColorSpec
      (e : {e : H.edgeSet // e ∈ distinguishedEdgeSet H J}) :
      a.color e.1 = some (edgeColor e) :=
    Classical.choose_spec (hrainbow.1 e.1 e.2)
  have hedgeColorMem
      (e : {e : H.edgeSet // e ∈ distinguishedEdgeSet H J}) :
      edgeColor e ∈ P := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [PartialEdgeAssignment.mem_colorUnusedOnFinset_iff]
    intro hunused
    exact hunused e.2 (hedgeColorSpec e)
  let edgeEmbed :
      {e : H.edgeSet // e ∈ distinguishedEdgeSet H J} → {c // c ∈ P} :=
    fun e ↦ ⟨edgeColor e, hedgeColorMem e⟩
  have hedgeInjective : Function.Injective edgeEmbed := by
    intro e f hef
    apply Subtype.ext
    by_contra hne
    have hcolors : edgeColor e = edgeColor f := congrArg Subtype.val hef
    exact hrainbow.2 e.2 f.2 hne
      (by rw [hedgeColorSpec e, hedgeColorSpec f, hcolors])
  have hdistinguishedLe :
      (distinguishedEdgeSet H J).ncard ≤ P.card := by
    calc
      (distinguishedEdgeSet H J).ncard =
          Fintype.card {e : H.edgeSet // e ∈ distinguishedEdgeSet H J} := by
        exact (Set.fintypeCard_eq_ncard
          (s := distinguishedEdgeSet H J)).symm
      _ ≤ Fintype.card {c // c ∈ P} :=
        Fintype.card_le_of_injective edgeEmbed hedgeInjective
      _ = P.card := by simp
  have hpresentWitness (c : {c // c ∈ P}) :
      ∃ e : H.edgeSet,
        e ∈ distinguishedEdgeSet H J ∧ a.color e = some c.1 := by
    have hcNotU : c.1 ∉ U := (Finset.mem_sdiff.mp c.2).2
    have hcNotUnused :
        ¬a.ColorUnusedOn (distinguishedEdgeSet H J) c.1 := by
      simpa [U] using hcNotU
    rw [PartialEdgeAssignment.ColorUnusedOn] at hcNotUnused
    push Not at hcNotUnused
    exact hcNotUnused
  let presentEdge (c : {c // c ∈ P}) : H.edgeSet :=
    Classical.choose (hpresentWitness c)
  have hpresentEdgeSpec (c : {c // c ∈ P}) :
      presentEdge c ∈ distinguishedEdgeSet H J ∧
        a.color (presentEdge c) = some c.1 :=
    Classical.choose_spec (hpresentWitness c)
  let presentEmbed : {c // c ∈ P} →
      {e : H.edgeSet // e ∈ distinguishedEdgeSet H J} :=
    fun c ↦ ⟨presentEdge c, (hpresentEdgeSpec c).1⟩
  have hpresentInjective : Function.Injective presentEmbed := by
    intro c d hcd
    apply Subtype.ext
    apply Option.some.inj
    have hedge : presentEdge c = presentEdge d := congrArg Subtype.val hcd
    calc
      some c.1 = a.color (presentEdge c) := (hpresentEdgeSpec c).2.symm
      _ = a.color (presentEdge d) := congrArg a.color hedge
      _ = some d.1 := (hpresentEdgeSpec d).2
  have hpresentLe : P.card ≤ (distinguishedEdgeSet H J).ncard := by
    calc
      P.card = Fintype.card {c // c ∈ P} := by simp
      _ ≤ Fintype.card
          {e : H.edgeSet // e ∈ distinguishedEdgeSet H J} :=
        Fintype.card_le_of_injective presentEmbed hpresentInjective
      _ = (distinguishedEdgeSet H J).ncard :=
        Set.fintypeCard_eq_ncard (s := distinguishedEdgeSet H J)
  have hPcard : P.card = D := by
    have hdistinguished := hstructure.card_distinguishedEdgeSet
    omega
  have hpartition : P.card + U.card = D + 2 := by
    calc
      P.card + U.card = (Finset.univ : Finset (ExtensionPalette D)).card := by
        simpa [P] using Finset.card_sdiff_add_card_eq_card
          (show U ⊆ (Finset.univ : Finset (ExtensionPalette D)) by simp)
      _ = D + 2 := by simp [ExtensionPalette]
  change U.card = 2
  omega

/-- The physical leaf universe is in bijection with the colors present at the
center. The root represents the colored distinguished center edge, while every
other physical vertex represents its defining non-distinguished center edge. -/
theorem card_centerPhysicalFinset_eq_card_presentAt_center
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge) :
    (a.centerPhysicalFinset (distinguishedEdgeSet H J)
        center root.leaf).card =
      ((Finset.univ : Finset (ExtensionPalette D)) \
        a.missingColorsAt Finset.univ center).card := by
  classical
  let L := a.centerPhysicalFinset (distinguishedEdgeSet H J)
    center root.leaf
  let P := (Finset.univ : Finset (ExtensionPalette D)) \
    a.missingColorsAt Finset.univ center
  rcases h.member with ⟨x, M, hstructure⟩
  have hcenterNeX : center ≠ x := by
    intro hcx
    apply hrootJ
    apply hstructure.center_incident_mem_distinguishedEdgeSet root.edge
    simpa [hcx] using root.center_incident
  rcases hstructure.exact_coverage_distinguishedEdgeSet center hcenterNeX with
    ⟨jCenter, hjCenter, hjUnique⟩
  have hjColor : ∃ color : ExtensionPalette D,
      a.color jCenter = some color := by
    have hcolored := PartialEdgeAssignment.coloredOn_of_oneHoleAt_not_mem
      hhole hrootJ
    exact hcolored jCenter hjCenter.1
  have hdatum (vertex : {vertex // vertex ∈ L}) :
      ∃ (edge : H.edgeSet) (color : ExtensionPalette D),
        Incident center edge ∧ a.color edge = some color ∧
          ((vertex.1 = root.leaf ∧ edge = jCenter) ∨
            (vertex.1 ≠ root.leaf ∧
              edge ∉ distinguishedEdgeSet H J ∧
              (edge : Sym2 V) = s(center, vertex.1))) := by
    by_cases hroot : vertex.1 = root.leaf
    · rcases hjColor with ⟨color, hcolor⟩
      exact ⟨jCenter, color, hjCenter.2, hcolor, Or.inl ⟨hroot, rfl⟩⟩
    · have hphysical : vertex.1 ∈
          a.centerPhysicalSet (distinguishedEdgeSet H J)
            center root.leaf := by
        have hvL := vertex.2
        change vertex.1 ∈
          a.centerPhysicalFinset (distinguishedEdgeSet H J)
            center root.leaf at hvL
        exact (PartialEdgeAssignment.mem_centerPhysicalFinset_iff
          a (distinguishedEdgeSet H J) center root.leaf vertex.1).mp hvL
      have htarget : a.IsCenterTarget (distinguishedEdgeSet H J)
          center vertex.1 := by
        rcases hphysical with hroot' | htarget
        · exact (hroot (Set.mem_singleton_iff.mp hroot')).elim
        · exact htarget
      rcases htarget with ⟨edge, color, hends, heJ, hcolor⟩
      have hincident : Incident center edge := by
        change center ∈ (edge : Sym2 V)
        rw [hends]
        exact Sym2.mem_mk_left center vertex.1
      exact ⟨edge, color, hincident, hcolor,
        Or.inr ⟨hroot, heJ, hends⟩⟩
  let edge (vertex : {vertex // vertex ∈ L}) : H.edgeSet :=
    Classical.choose (hdatum vertex)
  let color (vertex : {vertex // vertex ∈ L}) : ExtensionPalette D :=
    Classical.choose (Classical.choose_spec (hdatum vertex))
  have hdatumSpec (vertex : {vertex // vertex ∈ L}) :
      Incident center (edge vertex) ∧
        a.color (edge vertex) = some (color vertex) ∧
          ((vertex.1 = root.leaf ∧ edge vertex = jCenter) ∨
            (vertex.1 ≠ root.leaf ∧
              edge vertex ∉ distinguishedEdgeSet H J ∧
              ((edge vertex : H.edgeSet) : Sym2 V) = s(center, vertex.1))) :=
    Classical.choose_spec (Classical.choose_spec (hdatum vertex))
  have hcolorMem (vertex : {vertex // vertex ∈ L}) : color vertex ∈ P := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hmissing
    have hmissing' :=
      (PartialEdgeAssignment.mem_missingColorsAt.mp hmissing).2
    exact hmissing' (edge vertex) (hdatumSpec vertex).1
      (hdatumSpec vertex).2.1
  let embed : {vertex // vertex ∈ L} → {color // color ∈ P} :=
    fun vertex ↦ ⟨color vertex, hcolorMem vertex⟩
  have hedgeEq {vertex vertex' : {vertex // vertex ∈ L}}
      (hcolors : color vertex = color vertex') :
      edge vertex = edge vertex' := by
    by_contra hne
    have hadj : H.lineGraph.Adj (edge vertex) (edge vertex') :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr
        ⟨hne, center, (hdatumSpec vertex).1, (hdatumSpec vertex').1⟩
    have hnot := hvalid (edge vertex) (edge vertex') (color vertex)
      hadj (hdatumSpec vertex).2.1
    exact hnot (by rw [(hdatumSpec vertex').2.1, hcolors])
  have hinjective : Function.Injective embed := by
    intro vertex vertex' heq
    apply Subtype.ext
    have hcolors : color vertex = color vertex' :=
      congrArg Subtype.val heq
    have hedges : edge vertex = edge vertex' := hedgeEq hcolors
    rcases (hdatumSpec vertex).2.2 with hroot | htarget
    · rcases (hdatumSpec vertex').2.2 with hroot' | htarget'
      · exact hroot.1.trans hroot'.1.symm
      · exfalso
        apply htarget'.2.1
        rw [← hedges, hroot.2]
        exact hjCenter.1
    · rcases (hdatumSpec vertex').2.2 with hroot' | htarget'
      · exfalso
        apply htarget.2.1
        rw [hedges, hroot'.2]
        exact hjCenter.1
      · apply Sym2.congr_right.mp
        calc
          s(center, vertex.1) = (edge vertex : Sym2 V) := htarget.2.2.symm
          _ = (edge vertex' : Sym2 V) := congrArg Subtype.val hedges
          _ = s(center, vertex'.1) := htarget'.2.2
  have hrootL : root.leaf ∈ L := by
    apply (PartialEdgeAssignment.mem_centerPhysicalFinset_iff
      a (distinguishedEdgeSet H J) center root.leaf root.leaf).2
    exact Set.mem_union_left _ (Set.mem_singleton root.leaf)
  have hsurjective : Function.Surjective embed := by
    intro present
    have hnotMissing : ¬a.MissingAt center present.1 := by
      intro hmissing
      have hpresentMissing : present.1 ∈
          a.missingColorsAt Finset.univ center :=
        PartialEdgeAssignment.mem_missingColorsAt.mpr
          ⟨Finset.mem_univ _, hmissing⟩
      exact (Finset.mem_sdiff.mp present.2).2 hpresentMissing
    rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
        a hnotMissing with ⟨carrier, hcarrierIncident, hcarrierColor⟩
    by_cases hcarrierJ : carrier ∈ distinguishedEdgeSet H J
    · have hcarrierEq : carrier = jCenter :=
        hjUnique carrier ⟨hcarrierJ, hcarrierIncident⟩
      let rootVertex : {vertex // vertex ∈ L} := ⟨root.leaf, hrootL⟩
      refine ⟨rootVertex, ?_⟩
      apply Subtype.ext
      rcases (hdatumSpec rootVertex).2.2 with hroot | htarget
      · apply Option.some.inj
        calc
          some (color rootVertex) = a.color (edge rootVertex) :=
            (hdatumSpec rootVertex).2.1.symm
          _ = a.color jCenter := by rw [hroot.2]
          _ = a.color carrier := by rw [hcarrierEq]
          _ = some present.1 := hcarrierColor
      · exact (htarget.1 rfl).elim
    · rcases Sym2.mem_iff_exists.mp hcarrierIncident with
        ⟨target, htargetEnds⟩
      have htargetNeRoot : target ≠ root.leaf := by
        intro htarget
        subst target
        have hcarrierRoot : carrier = root.edge :=
          PartialEdgeAssignment.centerEdge_eq_of_endpoints
            htargetEnds root.endpoints
        have hrootNone : a.color root.edge = none :=
          (hhole root.edge).2 rfl
        rw [hcarrierRoot, hrootNone] at hcarrierColor
        simp at hcarrierColor
      have htargetL : target ∈ L := by
        apply (PartialEdgeAssignment.mem_centerPhysicalFinset_iff
          a (distinguishedEdgeSet H J) center root.leaf target).2
        exact Set.mem_union_right _
          ⟨carrier, present.1, htargetEnds, hcarrierJ, hcarrierColor⟩
      let targetVertex : {vertex // vertex ∈ L} := ⟨target, htargetL⟩
      refine ⟨targetVertex, ?_⟩
      apply Subtype.ext
      rcases (hdatumSpec targetVertex).2.2 with hroot | htarget
      · exact (htargetNeRoot hroot.1).elim
      · have hedgeEq : edge targetVertex = carrier :=
          PartialEdgeAssignment.centerEdge_eq_of_endpoints
            htarget.2.2 htargetEnds
        apply Option.some.inj
        calc
          some (color targetVertex) = a.color (edge targetVertex) :=
            (hdatumSpec targetVertex).2.1.symm
          _ = a.color carrier := congrArg a.color hedgeEq
          _ = some present.1 := hcarrierColor
  change L.card = P.card
  calc
    L.card = Fintype.card {vertex // vertex ∈ L} := by simp
    _ = Fintype.card {color // color ∈ P} :=
      Fintype.card_congr
        (Equiv.ofBijective embed ⟨hinjective, hsurjective⟩)
    _ = P.card := by simp

/-- Inequality-facing compatibility wrapper for the exact physical-universe
count. -/
theorem card_centerPhysicalFinset_le_card_presentAt_center
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge) :
    (a.centerPhysicalFinset (distinguishedEdgeSet H J)
        center root.leaf).card ≤
      ((Finset.univ : Finset (ExtensionPalette D)) \
        a.missingColorsAt Finset.univ center).card :=
  (h.card_centerPhysicalFinset_eq_card_presentAt_center
    root hrootJ hvalid hhole).le

/-- Every unused color missing at no reachable vertex supplies a distinct
physical head outside the reachable set. -/
theorem card_zeroHoleUnusedColors_le_card_centerPhysical_sdiff_reachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    let W := a.centerReachableFinset (distinguishedEdgeSet H J)
      center root.leaf
    let U := a.colorUnusedOnFinset (distinguishedEdgeSet H J)
    let R := FanCount.occurringColors W U a.MissingAt
    let L := a.centerPhysicalFinset (distinguishedEdgeSet H J)
      center root.leaf
    (U \ R).card ≤ (L \ W).card := by
  classical
  dsimp only
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  let L := a.centerPhysicalFinset (distinguishedEdgeSet H J)
    center root.leaf
  let U := a.colorUnusedOnFinset (distinguishedEdgeSet H J)
  let R := FanCount.occurringColors W U a.MissingAt
  let Z := U \ R
  have hdatum (color : {color // color ∈ Z}) :
      ∃ (edge : H.edgeSet) (target : V),
        (edge : Sym2 V) = s(center, target) ∧
          a.color edge = some color.1 ∧ target ∈ L \ W := by
    have hparts := Finset.mem_sdiff.mp color.2
    have hunused :
        a.ColorUnusedOn (distinguishedEdgeSet H J) color.1 := by
      apply (PartialEdgeAssignment.mem_colorUnusedOnFinset_iff
        a (distinguishedEdgeSet H J) color.1).mp
      simpa only [U] using hparts.1
    have hnotCenter : ¬a.MissingAt center color.1 :=
      h.not_missingAt_center_of_unused root hrootJ hvalid hhole
        hrainbow hunused
    rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
        a hnotCenter with ⟨edge, hcenterEdge, hcolor⟩
    have hedgeJ : edge ∉ distinguishedEdgeSet H J := by
      intro hedgeJ
      exact hunused hedgeJ hcolor
    rcases Sym2.mem_iff_exists.mp hcenterEdge with ⟨target, htargetEnds⟩
    have htargetNeRoot : target ≠ root.leaf := by
      intro htarget
      subst target
      have hedgeRoot : edge = root.edge :=
        PartialEdgeAssignment.centerEdge_eq_of_endpoints
          htargetEnds root.endpoints
      have hrootNone : a.color root.edge = none :=
        (hhole root.edge).2 rfl
      rw [hedgeRoot, hrootNone] at hcolor
      simp at hcolor
    have htargetL : target ∈ L := by
      apply (PartialEdgeAssignment.mem_centerPhysicalFinset_iff
        a (distinguishedEdgeSet H J) center root.leaf target).2
      exact Set.mem_union_right _
        ⟨edge, color.1, htargetEnds, hedgeJ, hcolor⟩
    have htargetW : target ∉ W := by
      intro htargetW
      have hreach : a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf target := by
        simpa [W] using htargetW
      rcases PartialEdgeAssignment.exists_reachable_missing_of_reachable_centerEdge
          a (distinguishedEdgeSet H J) hreach htargetNeRoot
          htargetEnds hcolor with ⟨source, hsourceReach, hsourceMissing⟩
      have hsourceW : source ∈ W := by
        simpa [W] using hsourceReach
      have hpositive :
          0 < FanCount.colorMultiplicity W a.MissingAt color.1 := by
        rw [FanCount.colorMultiplicity, Finset.card_pos]
        exact ⟨source, Finset.mem_filter.mpr
          ⟨hsourceW, hsourceMissing⟩⟩
      have hcolorR : color.1 ∈ R :=
        (FanCount.mem_occurringColors_iff
          W U a.MissingAt color.1).2 ⟨hparts.1, hpositive⟩
      exact hparts.2 hcolorR
    exact ⟨edge, target, htargetEnds, hcolor,
      Finset.mem_sdiff.mpr ⟨htargetL, htargetW⟩⟩
  let edge (color : {color // color ∈ Z}) : H.edgeSet :=
    Classical.choose (hdatum color)
  let target (color : {color // color ∈ Z}) : V :=
    Classical.choose (Classical.choose_spec (hdatum color))
  have hdatumSpec (color : {color // color ∈ Z}) :
      ((edge color : H.edgeSet) : Sym2 V) = s(center, target color) ∧
        a.color (edge color) = some color.1 ∧ target color ∈ L \ W :=
    Classical.choose_spec (Classical.choose_spec (hdatum color))
  let embed : {color // color ∈ Z} → {vertex // vertex ∈ L \ W} :=
    fun color ↦ ⟨target color, (hdatumSpec color).2.2⟩
  have hinjective : Function.Injective embed := by
    intro color color' heq
    apply Subtype.ext
    have htargets : target color = target color' :=
      congrArg Subtype.val heq
    have hedges : edge color = edge color' :=
      PartialEdgeAssignment.centerEdge_eq_of_endpoints
        (hdatumSpec color).1
        (by simpa [htargets] using (hdatumSpec color').1)
    apply Option.some.inj
    calc
      some color.1 = a.color (edge color) := (hdatumSpec color).2.1.symm
      _ = a.color (edge color') := congrArg a.color hedges
      _ = some color'.1 := (hdatumSpec color').2.1
  change Z.card ≤ (L \ W).card
  calc
    Z.card = Fintype.card {color // color ∈ Z} := by simp
    _ ≤ Fintype.card {vertex // vertex ∈ L \ W} :=
      Fintype.card_le_of_injective embed hinjective
    _ = (L \ W).card := Fintype.card_coe (L \ W)

/-- State-local fan capacity.  The final term counts the colors unused on
the distinguished set which are missing at at least one vertex of the
canonical reachable set.  The additive form avoids truncated-subtraction
bookkeeping. -/
theorem card_centerReachable_add_centerMissing_le_parameter_add_occurringUnused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    (a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf).card +
        (a.missingColorsAt Finset.univ center).card ≤
      D +
        (FanCount.occurringColors
          (a.centerReachableFinset (distinguishedEdgeSet H J)
            center root.leaf)
          (a.colorUnusedOnFinset (distinguishedEdgeSet H J))
          a.MissingAt).card := by
  classical
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  let L := a.centerPhysicalFinset (distinguishedEdgeSet H J)
    center root.leaf
  let U := a.colorUnusedOnFinset (distinguishedEdgeSet H J)
  let R := FanCount.occurringColors W U a.MissingAt
  let Z := U \ R
  let P := (Finset.univ : Finset (ExtensionPalette D)) \
    a.missingColorsAt Finset.univ center
  have hRsubU : R ⊆ U := by
    intro color hcolor
    exact (FanCount.mem_occurringColors_iff
      W U a.MissingAt color).mp hcolor |>.1
  have hZle : Z.card ≤ (L \ W).card := by
    simpa [W, L, U, R, Z] using
      h.card_zeroHoleUnusedColors_le_card_centerPhysical_sdiff_reachable
        root hrootJ hvalid hhole hrainbow
  have hWsubL : W ⊆ L := by
    intro vertex hvertex
    have hreach : a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf vertex := by
      simpa [W] using hvertex
    apply (PartialEdgeAssignment.mem_centerPhysicalFinset_iff
      a (distinguishedEdgeSet H J) center root.leaf vertex).2
    exact PartialEdgeAssignment.centerReachable_mem_centerPhysicalSet hreach
  have hWL : W.card + (L \ W).card = L.card := by
    have hpartition := Finset.card_sdiff_add_card_eq_card hWsubL
    omega
  have hWZleL : W.card + Z.card ≤ L.card := by omega
  have hLleP : L.card ≤ P.card := by
    simpa [L, P] using
      h.card_centerPhysicalFinset_le_card_presentAt_center
        root hrootJ hvalid hhole
  have hWZleP : W.card + Z.card ≤ P.card := hWZleL.trans hLleP
  have hUcard : U.card = 2 := by
    simpa [U] using h.card_colorUnusedOnFinset_eq_two hrainbow
  have hZR : Z.card + R.card = 2 := by
    have hpartition := Finset.card_sdiff_add_card_eq_card hRsubU
    change (U \ R).card + R.card = 2
    omega
  have hPcenter :
      P.card + (a.missingColorsAt Finset.univ center).card = D + 2 := by
    calc
      P.card + (a.missingColorsAt Finset.univ center).card =
          (Finset.univ : Finset (ExtensionPalette D)).card := by
        simpa [P] using Finset.card_sdiff_add_card_eq_card
          (PartialEdgeAssignment.missingColorsAt_subset
            a Finset.univ center)
      _ = D + 2 := by simp [ExtensionPalette]
  change W.card + (a.missingColorsAt Finset.univ center).card ≤
    D + R.card
  omega

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
