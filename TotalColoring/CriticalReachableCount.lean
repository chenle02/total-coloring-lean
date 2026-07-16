import TotalColoring.CriticalFanCount
import TotalColoring.CriticalSpareCenter
import TotalColoring.CriticalUsedColorMultiplicity

/-!
# Missing-color counting on the full reachable fan

For a root edge outside the distinguished set, the canonical center-dependency
reachable set is the union of the terminals of all simple linear fan paths
from the root.  This module packages that set as a finset and proves its two
complementary counting bounds in a supplied critical one-hole state:

* the leaves have at least `2 * |W| + 1` missing-color incidences; and
* the colors occurring among those incidences inject into `W`.

Consequently some color is missing at three reachable leaves.  Combining
that triple with the earlier conditional theorem excludes every color unused
on the distinguished set from the fan center.

This is a local closure-and-counting argument.  It does not use a single
linear path as though it enumerated a branching fan, and it assumes neither
cross-state maximality of the reachable set nor survival of a fixed selected
fan sequence.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- The finite form of the canonical center-dependency reachable set. -/
noncomputable def centerReachableFinset [Fintype V]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) : Finset V := by
  classical
  exact Finset.univ.filter fun target ↦ a.CenterReachable J center root target

@[simp]
theorem mem_centerReachableFinset_iff [Fintype V]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root target : V) :
    target ∈ a.centerReachableFinset J center root ↔
      a.CenterReachable J center root target := by
  classical
  simp [centerReachableFinset]

@[simp]
theorem root_mem_centerReachableFinset [Fintype V]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) :
    root ∈ a.centerReachableFinset J center root := by
  simp

/-- The finite wrapper has exactly the canonical reachable set as its
coercion. -/
theorem coe_centerReachableFinset [Fintype V]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) :
    (↑(a.centerReachableFinset J center root) : Set V) =
      a.centerReachableSet J center root := by
  ext target
  simp

/-- Cardinality bridge from the finite wrapper to the canonical set. -/
theorem card_centerReachableFinset [Fintype V]
    (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (center root : V) :
    (a.centerReachableFinset J center root).card =
      (a.centerReachableSet J center root).ncard := by
  rw [← Set.ncard_coe_finset, coe_centerReachableFinset]

theorem colorMultiplicity_centerReachableFinset_eq_ncard
    [Fintype V] [DecidableEq V]
    (a : PartialEdgeAssignment G C) [DecidableRel a.MissingAt]
    (J : Set G.edgeSet) (center root : V) (color : C) :
    FanCount.colorMultiplicity (a.centerReachableFinset J center root)
        a.MissingAt color =
      ({leaf : V |
        a.CenterReachable J center root leaf ∧
          a.MissingAt leaf color} : Set V).ncard := by
  classical
  change
    ((a.centerReachableFinset J center root).filter
      fun leaf ↦ a.MissingAt leaf color).card = _
  rw [← Set.ncard_coe_finset]
  congr 1
  ext leaf
  simp

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- Every vertex of the full reachable fan has at least two missing colors,
and the root has one additional missing color from the unique hole. -/
theorem two_mul_card_centerReachableFinset_add_one_le_sum_missingColorsAt
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hhole : a.OneHoleAt root.edge) :
    2 * (a.centerReachableFinset (distinguishedEdgeSet H J)
          center root.leaf).card + 1 ≤
      ∑ leaf ∈ (a.centerReachableFinset (distinguishedEdgeSet H J)
          center root.leaf),
        (a.missingColorsAt Finset.univ leaf).card := by
  classical
  rcases h.member with ⟨x, M, hstructure⟩
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  have hPalette :
      (Finset.univ : Finset (ExtensionPalette D)).card = D + 2 := by
    simp [ExtensionPalette]
  have htwo (leaf : V) :
      2 ≤ (a.missingColorsAt Finset.univ leaf).card :=
    PartialEdgeAssignment.two_le_missingColorsAt_card_of_palette_card_eq_of_degree_le
      a Finset.univ leaf D hPalette (hstructure.degree_le_parameter leaf)
  have hrootCount :=
    PartialEdgeAssignment.D_add_three_sub_degree_le_missingColorsAt_card
      (a := a) (palette := Finset.univ) hhole root.leaf_incident hPalette
  have hrootThree :
      3 ≤ (a.missingColorsAt Finset.univ root.leaf).card := by
    have hdegree := hstructure.degree_le_parameter root.leaf
    have hthreeSub : 3 ≤ D + 3 - H.degree root.leaf :=
      Nat.le_sub_of_add_le (by omega)
    exact hthreeSub.trans hrootCount
  let weight : V → ℕ := fun leaf ↦
    if leaf = root.leaf then 3 else 2
  have hpoint (leaf : V) (hleaf : leaf ∈ W) :
      weight leaf ≤ (a.missingColorsAt Finset.univ leaf).card := by
    by_cases hroot : leaf = root.leaf
    · subst leaf
      simpa [weight] using hrootThree
    · simpa [weight, hroot] using htwo leaf
  have hsum :
      (∑ leaf ∈ W, weight leaf) ≤
        ∑ leaf ∈ W, (a.missingColorsAt Finset.univ leaf).card :=
    Finset.sum_le_sum hpoint
  have hrootMem : root.leaf ∈ W := by
    simp [W]
  have hweight :
      (∑ leaf ∈ W, weight leaf) = 2 * W.card + 1 := by
    rw [← Finset.sum_erase_add W weight hrootMem]
    have herase :
        (∑ leaf ∈ W.erase root.leaf, weight leaf) =
          2 * (W.erase root.leaf).card := by
      calc
        _ = ∑ _leaf ∈ W.erase root.leaf, 2 := by
          apply Finset.sum_congr rfl
          intro leaf hleaf
          have hne : leaf ≠ root.leaf := (Finset.mem_erase.mp hleaf).1
          simp [weight, hne]
        _ = 2 * (W.erase root.leaf).card := by
          simp [Nat.mul_comm]
    rw [herase, Finset.card_erase_of_mem hrootMem]
    simp [weight]
    have hcardPos : 0 < W.card :=
      Finset.card_pos.mpr ⟨root.leaf, hrootMem⟩
    omega
  change 2 * W.card + 1 ≤ _
  rw [← hweight]
  exact hsum

/-- The colors missing on the full dependency-reachable fan inject into its
vertices.  A non-distinguished center carrier maps to its reachable head; the
unique distinguished carrier at the center maps to the root. -/
theorem card_occurringColors_centerReachableFinset_le_card
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)}
    [DecidableRel a.MissingAt] {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    (FanCount.occurringColors
        (a.centerReachableFinset (distinguishedEdgeSet H J)
          center root.leaf)
        Finset.univ a.MissingAt).card ≤
      (a.centerReachableFinset (distinguishedEdgeSet H J)
        center root.leaf).card := by
  classical
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  let R := FanCount.occurringColors W Finset.univ a.MissingAt
  rcases h.member with ⟨x, M, hstructure⟩
  have hcenterNeX : center ≠ x := by
    intro hcx
    apply hrootJ
    apply hstructure.center_incident_mem_distinguishedEdgeSet root.edge
    simpa [hcx] using root.center_incident
  rcases hstructure.exact_coverage_distinguishedEdgeSet center hcenterNeX with
    ⟨jCenter, hjCenter, hjUnique⟩
  have hdatum (color : ExtensionPalette D) (hcolor : color ∈ R) :
      ∃ leaf : V, ∃ carrier : H.edgeSet, ∃ target : V,
        leaf ∈ W ∧ a.MissingAt leaf color ∧
        Incident center carrier ∧ a.color carrier = some color ∧
        (carrier : Sym2 V) = s(center, target) := by
    have hocc := (FanCount.mem_occurringColors_iff
      W Finset.univ a.MissingAt color).mp hcolor
    have hpositive : 0 < (W.filter fun leaf ↦ a.MissingAt leaf color).card :=
      hocc.2
    rcases Finset.card_pos.mp hpositive with ⟨leaf, hleaf⟩
    have hleafParts := Finset.mem_filter.mp hleaf
    have hreach : a.CenterReachable (distinguishedEdgeSet H J)
        center root.leaf leaf := by
      simpa [W] using hleafParts.1
    have hnotMissing : ¬a.MissingAt center color := by
      intro hcenter
      exact h.center_reachable_elementary root hrootJ hvalid hhole
        hrainbow hreach color ⟨hcenter, hleafParts.2⟩
    rcases PartialEdgeAssignment.exists_incident_colored_edge_of_not_missing
        a hnotMissing with ⟨carrier, hcenterCarrier, hcarrierColor⟩
    rcases Sym2.mem_iff_exists.mp hcenterCarrier with ⟨target, htarget⟩
    exact ⟨leaf, carrier, target, hleafParts.1, hleafParts.2,
      hcenterCarrier, hcarrierColor, htarget⟩
  let leaf (color : {color // color ∈ R}) : V :=
    Classical.choose (hdatum color.1 color.2)
  let carrier (color : {color // color ∈ R}) : H.edgeSet :=
    Classical.choose (Classical.choose_spec (hdatum color.1 color.2))
  let target (color : {color // color ∈ R}) : V :=
    Classical.choose (Classical.choose_spec
      (Classical.choose_spec (hdatum color.1 color.2)))
  have hdatumSpec (color : {color // color ∈ R}) :
      leaf color ∈ W ∧ a.MissingAt (leaf color) color.1 ∧
      Incident center (carrier color) ∧
      a.color (carrier color) = some color.1 ∧
      ((carrier color : H.edgeSet) : Sym2 V) = s(center, target color) := by
    exact Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec (hdatum color.1 color.2)))
  let imageVertex (color : {color // color ∈ R}) : V :=
    if carrier color ∈ distinguishedEdgeSet H J then root.leaf
    else target color
  have himageMem (color : {color // color ∈ R}) :
      imageVertex color ∈ W := by
    by_cases hcarrierJ : carrier color ∈ distinguishedEdgeSet H J
    · simp [imageVertex, hcarrierJ, W]
    · have hdep : a.CenterDependency (distinguishedEdgeSet H J)
          center (leaf color) (target color) :=
        ⟨carrier color, color.1, (hdatumSpec color).2.2.2.2,
          hcarrierJ, (hdatumSpec color).2.2.2.1,
          (hdatumSpec color).2.1⟩
      have hsource : a.CenterReachable (distinguishedEdgeSet H J)
          center root.leaf (leaf color) := by
        simpa [W] using (hdatumSpec color).1
      have htargetReach := PartialEdgeAssignment.centerReachable_tail hsource hdep
      simpa [imageVertex, hcarrierJ, W] using htargetReach
  let embed : {color // color ∈ R} → {vertex // vertex ∈ W} :=
    fun color ↦ ⟨imageVertex color, himageMem color⟩
  have hinjective : Function.Injective embed := by
    intro color color' heq
    apply Subtype.ext
    have hvertex : imageVertex color = imageVertex color' :=
      congrArg Subtype.val heq
    by_cases hcJ : carrier color ∈ distinguishedEdgeSet H J
    · by_cases hcJ' : carrier color' ∈ distinguishedEdgeSet H J
      · have hcEq : carrier color = jCenter :=
          hjUnique (carrier color) ⟨hcJ, (hdatumSpec color).2.2.1⟩
        have hcEq' : carrier color' = jCenter :=
          hjUnique (carrier color') ⟨hcJ', (hdatumSpec color').2.2.1⟩
        apply Option.some.inj
        calc
          some color.1 = a.color (carrier color) :=
            (hdatumSpec color).2.2.2.1.symm
          _ = a.color (carrier color') := by rw [hcEq, hcEq']
          _ = some color'.1 := (hdatumSpec color').2.2.2.1
      · have htargetRoot : target color' = root.leaf := by
          simpa [imageVertex, hcJ, hcJ'] using hvertex.symm
        have hdep : a.CenterDependency (distinguishedEdgeSet H J)
            center (leaf color') (target color') :=
          ⟨carrier color', color'.1, (hdatumSpec color').2.2.2.2,
            hcJ', (hdatumSpec color').2.2.2.1,
            (hdatumSpec color').2.1⟩
        rw [htargetRoot] at hdep
        exact (PartialEdgeAssignment.centerDependency_target_ne_root_of_oneHoleAt
          root.endpoints hhole hdep).elim
    · by_cases hcJ' : carrier color' ∈ distinguishedEdgeSet H J
      · have htargetRoot : target color = root.leaf := by
          simpa [imageVertex, hcJ, hcJ'] using hvertex
        have hdep : a.CenterDependency (distinguishedEdgeSet H J)
            center (leaf color) (target color) :=
          ⟨carrier color, color.1, (hdatumSpec color).2.2.2.2,
            hcJ, (hdatumSpec color).2.2.2.1,
            (hdatumSpec color).2.1⟩
        rw [htargetRoot] at hdep
        exact (PartialEdgeAssignment.centerDependency_target_ne_root_of_oneHoleAt
          root.endpoints hhole hdep).elim
      · have htargetEq : target color = target color' := by
          simpa [imageVertex, hcJ, hcJ'] using hvertex
        have hcarrierEq : carrier color = carrier color' :=
          PartialEdgeAssignment.centerEdge_eq_of_endpoints
            (hdatumSpec color).2.2.2.2
            (by simpa [htargetEq] using (hdatumSpec color').2.2.2.2)
        apply Option.some.inj
        calc
          some color.1 = a.color (carrier color) :=
            (hdatumSpec color).2.2.2.1.symm
          _ = a.color (carrier color') := by rw [hcarrierEq]
          _ = some color'.1 := (hdatumSpec color').2.2.2.1
  change R.card ≤ W.card
  simpa using Fintype.card_le_of_injective embed hinjective

/-- The full dependency-reachable fan contains a color missing at at least
three leaves. -/
theorem exists_three_missing_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    ∃ gamma : ExtensionPalette D,
      3 ≤ ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf gamma} : Set V).ncard := by
  classical
  let W := a.centerReachableFinset (distinguishedEdgeSet H J)
    center root.leaf
  let R := FanCount.occurringColors W Finset.univ a.MissingAt
  by_contra hno
  push Not at hno
  have hmultiplicity : ∀ color ∈ R,
      FanCount.colorMultiplicity W a.MissingAt color ≤ 2 := by
    intro color hcolor
    have hltThree :
        FanCount.colorMultiplicity W a.MissingAt color < 3 := by
      rw [
        PartialEdgeAssignment.colorMultiplicity_centerReachableFinset_eq_ncard]
      exact hno color
    omega
  have hincidences :
      2 * W.card + 1 ≤
        ∑ leaf ∈ W, (a.missingColorsAt Finset.univ leaf).card := by
    simpa [W] using
      h.two_mul_card_centerReachableFinset_add_one_le_sum_missingColorsAt
        root hhole
  have hlower : W.card + 1 ≤ R.card := by
    apply PartialEdgeAssignment.card_add_one_le_distinct_fanMissingColors_of_multiplicity_two
      a W Finset.univ hmultiplicity hincidences
  have hupper : R.card ≤ W.card := by
    simpa [W, R] using
      h.card_occurringColors_centerReachableFinset_le_card
        root hrootJ hvalid hhole hrainbow
  omega

/-- Combining the counting bridge with the previously checked global
multiplicity-three bound gives an exact triple. -/
theorem exists_eq_three_missing_centerReachable
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    ∃ gamma : ExtensionPalette D,
      ({leaf : V |
        a.CenterReachable (distinguishedEdgeSet H J)
            center root.leaf leaf ∧
          a.MissingAt leaf gamma} : Set V).ncard = 3 := by
  rcases h.exists_three_missing_centerReachable root hrootJ
      hvalid hhole hrainbow with ⟨gamma, hthree⟩
  have hle := h.ncard_missingAt_centerReachable_le_three
    root hrootJ hvalid hhole hrainbow gamma
  exact ⟨gamma, Nat.le_antisymm hle hthree⟩

/-- Global spare-center exclusion in every supplied critical one-hole state. -/
theorem not_missingAt_center_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {delta : ExtensionPalette D}
    (hunused : a.ColorUnusedOn (distinguishedEdgeSet H J) delta) :
    ¬a.MissingAt center delta := by
  rcases h.exists_three_missing_centerReachable root hrootJ
      hvalid hhole hrainbow with ⟨gamma, hthree⟩
  exact h.not_missingAt_center_of_unused_of_three_missing_centerReachable
    root hrootJ hvalid hhole hrainbow hunused hthree

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
