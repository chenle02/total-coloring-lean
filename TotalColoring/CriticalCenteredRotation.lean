import TotalColoring.CriticalFixedSequence
import TotalColoring.CriticalReachableCount

/-!
# Centered spare/carrier-label rotations

Let `alpha` be missing at the center of a supplied critical one-hole state and
let `delta` be unused on the distinguished edge set.  Any genuine
`alpha`-`delta` component meeting the center must contain the unique
distinguished `alpha`-carrier.  Otherwise its safe swap would leave `delta`
unused while making it missing at the center, contradicting the global
spare-center theorem in the swapped state.

Consequently the actual centered swap crosses the carrier, recolors it
`delta` as its new unique distinguished carrier, makes `alpha` unused on the
distinguished set, and preserves a designated linear fan sequence literally.
This is a carrier-label rotation; it does not locate the carrier in the
matching part of the distinguished set and uses no fan-capacity or global-
maximality hypothesis.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- If `delta` was unused on `J` and the unique `alpha`-carrier is not
swapped, then `delta` remains unused after an `alpha`-`delta` swap. -/
theorem colorUnusedOn_right_swapOn_of_unused_right_of_unique_left_not_mem
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {alpha delta : C} {carrier : G.edgeSet}
    (hAlpha : a.IsUniqueColorOn J alpha carrier)
    (hdelta : a.ColorUnusedOn J delta)
    (hcarrierK : carrier ∉ K) :
    (a.swapOn alpha delta K).ColorUnusedOn J delta := by
  intro e heJ hecolor
  by_cases heK : e ∈ K
  · rw [swapOn_color_of_mem a alpha delta K heK] at hecolor
    rw [Option.map_eq_some_iff] at hecolor
    rcases hecolor with ⟨c, hc, hswap⟩
    have hca : c = alpha := by
      rw [Equiv.swap_apply_eq_iff] at hswap
      simpa using hswap
    have healpha : a.color e = some alpha := hc.trans (congrArg some hca)
    exact hcarrierK ((hAlpha.2.2 heJ healpha) ▸ heK)
  · rw [swapOn_color_of_not_mem a alpha delta K heK] at hecolor
    exact hdelta heJ hecolor

/-- If `delta` was unused on `J` and the unique `alpha`-carrier is swapped,
then `alpha` is unused after the `alpha`-`delta` swap. -/
theorem colorUnusedOn_left_swapOn_of_unused_right_of_unique_left_mem
    [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {alpha delta : C} {carrier : G.edgeSet}
    (hAlpha : a.IsUniqueColorOn J alpha carrier)
    (hdelta : a.ColorUnusedOn J delta)
    (hcarrierK : carrier ∈ K) :
    (a.swapOn alpha delta K).ColorUnusedOn J alpha := by
  intro e heJ hecolor
  by_cases heK : e ∈ K
  · rw [swapOn_color_of_mem a alpha delta K heK] at hecolor
    rw [Option.map_eq_some_iff] at hecolor
    rcases hecolor with ⟨c, hc, hswap⟩
    have hcd : c = delta := by
      rw [Equiv.swap_apply_eq_iff] at hswap
      simpa using hswap
    exact hdelta heJ (hc.trans (congrArg some hcd))
  · rw [swapOn_color_of_not_mem a alpha delta K heK] at hecolor
    exact heK (hAlpha.2.2 heJ hecolor ▸ hcarrierK)

end PartialEdgeAssignment

namespace IsOutsideEdgeMinimalNoncolorable

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {D : ℕ} {H : SimpleGraph V} {J : Finset (Sym2 V)}
variable [DecidableRel H.Adj]

/-- A genuine `alpha`-`delta` component through the fan center contains the
unique distinguished `alpha`-carrier whenever `alpha` is missing at the
center and `delta` is unused on the distinguished set. -/
theorem uniqueCarrier_mem_component_of_missingAt_center_of_unused
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (root : CenterSpoke H center)
    (hrootJ : root.edge ∉ distinguishedEdgeSet H J)
    (hvalid : a.Valid) (hhole : a.OneHoleAt root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha delta : ExtensionPalette D} {carrier : H.edgeSet}
    (hcenter : a.MissingAt center alpha)
    (hdelta : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    (hAlpha : a.IsUniqueColorOn
      (distinguishedEdgeSet H J) alpha carrier)
    {K : Set H.edgeSet} [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha delta K)
    (hmeetsCenter : EdgeSetMeetsVertex K center) :
    carrier ∈ K := by
  have halphadelta : alpha ≠ delta := by
    intro had
    subst delta
    exact hdelta hAlpha.1 hAlpha.2.1
  by_contra hcarrierK
  have hsafe :=
    PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_of_one_unused
      a (distinguishedEdgeSet H J) K hvalid hrainbow halphadelta hK
      (Or.inr hdelta)
  have hholeSwap :
      (a.swapOn alpha delta K).OneHoleAt root.edge :=
    (PartialEdgeAssignment.swapOn_oneHoleAt_iff
      a alpha delta K root.edge).2 hhole
  have hdeltaSwap :
      (a.swapOn alpha delta K).ColorUnusedOn
        (distinguishedEdgeSet H J) delta :=
    PartialEdgeAssignment.colorUnusedOn_right_swapOn_of_unused_right_of_unique_left_not_mem
      a (distinguishedEdgeSet H J) K hAlpha hdelta hcarrierK
  have hcenterSwap :
      (a.swapOn alpha delta K).MissingAt center delta :=
    PartialEdgeAssignment.missingAt_right_swapOn_of_missing_left_of_component_meets
      a hK halphadelta hcenter hmeetsCenter
  exact (h.not_missingAt_center_of_unused root hrootJ
    hsafe.1 hholeSwap hsafe.2 hdeltaSwap) hcenterSwap

/-- Full witness-sensitive centered spare/carrier-label rotation wrapper for
a designated unique `alpha`-carrier.  That literal carrier is crossed and
becomes the unique distinguished `delta`-carrier; the swapped state is valid,
one-hole, distinguished-rainbow, misses `delta` at the center, and uses no
`alpha` on the distinguished set.  A designated linear fan path survives with
exactly the same root and tail. -/
theorem exists_centered_spare_rotation_of_component_meets_of_uniqueCarrier
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha delta : ExtensionPalette D}
    (hcenter : a.MissingAt center alpha)
    (hdelta : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    {carrier : H.edgeSet}
    (hAlpha : a.IsUniqueColorOn
      (distinguishedEdgeSet H J) alpha carrier)
    {K : Set H.edgeSet} [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha delta K)
    (hmeetsCenter : EdgeSetMeetsVertex K center) :
    ∃ F' : PartialEdgeAssignment.LinearFanPath
        (a.swapOn alpha delta K) (distinguishedEdgeSet H J) center,
      a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha carrier ∧
      carrier ∈ K ∧
      a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha delta K ∧
      (a.swapOn alpha delta K).Valid ∧
      (a.swapOn alpha delta K).OneHoleAt F.root.edge ∧
      (a.swapOn alpha delta K).RainbowOn (distinguishedEdgeSet H J) ∧
      (a.swapOn alpha delta K).MissingAt center delta ∧
      (a.swapOn alpha delta K).ColorUnusedOn
        (distinguishedEdgeSet H J) alpha ∧
      (a.swapOn alpha delta K).IsUniqueColorOn
        (distinguishedEdgeSet H J) delta carrier ∧
      (a.swapOn alpha delta K).color carrier = some delta ∧
      F'.root = F.root ∧ F'.tail = F.tail := by
  have halphadelta : alpha ≠ delta := by
    intro had
    subst delta
    exact hdelta hAlpha.1 hAlpha.2.1
  have hcarrierK :=
    h.uniqueCarrier_mem_component_of_missingAt_center_of_unused
      F.root F.root_not_mem hvalid hhole hrainbow hcenter hdelta
      hAlpha hK hmeetsCenter
  have hcompatible :
      a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha delta K :=
    PartialEdgeAssignment.swapCompatibleOn_of_unused_right
      a (distinguishedEdgeSet H J) K hdelta
  have hsafe :=
    (PartialEdgeAssignment.valid_and_rainbowOn_swapOn_of_isTwoColorKempeComponent_iff
      a (distinguishedEdgeSet H J) K hvalid hrainbow halphadelta hK).2
      hcompatible
  have hholeSwap :
      (a.swapOn alpha delta K).OneHoleAt F.root.edge :=
    (PartialEdgeAssignment.swapOn_oneHoleAt_iff
      a alpha delta K F.root.edge).2 hhole
  have hcenterSwap :
      (a.swapOn alpha delta K).MissingAt center delta :=
    PartialEdgeAssignment.missingAt_right_swapOn_of_missing_left_of_component_meets
      a hK halphadelta hcenter hmeetsCenter
  have hAlphaUnusedSwap :
      (a.swapOn alpha delta K).ColorUnusedOn
        (distinguishedEdgeSet H J) alpha :=
    PartialEdgeAssignment.colorUnusedOn_left_swapOn_of_unused_right_of_unique_left_mem
      a (distinguishedEdgeSet H J) K hAlpha hdelta hcarrierK
  have hcarrierColorSwap :
      (a.swapOn alpha delta K).color carrier = some delta := by
    rw [PartialEdgeAssignment.swapOn_color_of_mem
      a alpha delta K hcarrierK, hAlpha.2.1]
    simp
  have hDeltaCarrierSwap :
      (a.swapOn alpha delta K).IsUniqueColorOn
        (distinguishedEdgeSet H J) delta carrier :=
    PartialEdgeAssignment.isUniqueColorOn_of_rainbowOn
      (a.swapOn alpha delta K) (distinguishedEdgeSet H J)
      hsafe.2 hAlpha.1 hcarrierColorSwap
  rcases h.exists_same_linearFanPath_after_swap_of_meets_center
      F hvalid hhole hrainbow hK halphadelta hcenter hmeetsCenter
      hcompatible with ⟨F', hroot, htail⟩
  exact ⟨F', hAlpha, hcarrierK, hcompatible, hsafe.1,
    hholeSwap, hsafe.2, hcenterSwap, hAlphaUnusedSwap,
    hDeltaCarrierSwap, hcarrierColorSwap, hroot, htail⟩

/-- Existential-carrier convenience form of the witness-sensitive centered
rotation theorem.  The explicit-carrier theorem above should be used whenever
the identity of a previously designated carrier matters. -/
theorem exists_centered_spare_rotation_of_component_meets
    (h : IsOutsideEdgeMinimalNoncolorable D H J)
    {a : PartialEdgeAssignment H (ExtensionPalette D)} {center : V}
    (F : PartialEdgeAssignment.LinearFanPath a
      (distinguishedEdgeSet H J) center)
    (hvalid : a.Valid) (hhole : a.OneHoleAt F.root.edge)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J))
    {alpha delta : ExtensionPalette D}
    (hcenter : a.MissingAt center alpha)
    (hdelta : a.ColorUnusedOn (distinguishedEdgeSet H J) delta)
    {K : Set H.edgeSet} [DecidablePred (· ∈ K)]
    (hK : a.IsTwoColorKempeComponent alpha delta K)
    (hmeetsCenter : EdgeSetMeetsVertex K center) :
    ∃ (carrier : H.edgeSet)
      (F' : PartialEdgeAssignment.LinearFanPath
        (a.swapOn alpha delta K) (distinguishedEdgeSet H J) center),
      a.IsUniqueColorOn (distinguishedEdgeSet H J) alpha carrier ∧
      carrier ∈ K ∧
      a.SwapCompatibleOn (distinguishedEdgeSet H J) alpha delta K ∧
      (a.swapOn alpha delta K).Valid ∧
      (a.swapOn alpha delta K).OneHoleAt F.root.edge ∧
      (a.swapOn alpha delta K).RainbowOn (distinguishedEdgeSet H J) ∧
      (a.swapOn alpha delta K).MissingAt center delta ∧
      (a.swapOn alpha delta K).ColorUnusedOn
        (distinguishedEdgeSet H J) alpha ∧
      (a.swapOn alpha delta K).IsUniqueColorOn
        (distinguishedEdgeSet H J) delta carrier ∧
      (a.swapOn alpha delta K).color carrier = some delta ∧
      F'.root = F.root ∧ F'.tail = F.tail := by
  have hAlphaUsed :
      ¬a.ColorUnusedOn (distinguishedEdgeSet H J) alpha := by
    intro hAlphaUnused
    exact (h.not_missingAt_center_of_unused F.root F.root_not_mem
      hvalid hhole hrainbow hAlphaUnused) hcenter
  rcases PartialEdgeAssignment.exists_uniqueColorOn_of_not_colorUnusedOn
      a (distinguishedEdgeSet H J) hrainbow hAlphaUsed with
    ⟨carrier, hAlpha⟩
  rcases h.exists_centered_spare_rotation_of_component_meets_of_uniqueCarrier
      F hvalid hhole hrainbow hcenter hdelta hAlpha hK hmeetsCenter with
    ⟨F', hrotation⟩
  exact ⟨carrier, F', hrotation⟩

end IsOutsideEdgeMinimalNoncolorable

end TotalColoring
