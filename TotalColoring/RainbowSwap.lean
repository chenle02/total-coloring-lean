import TotalColoring.Total

/-!
# Rainbow-safe two-color swaps

This module separates two logically different questions about a two-color
swap.  `RainbowOn` and `SwapCompatibleOn` describe the exact condition seen by
a distinguished edge family.  `TwoColorBoundaryClosed` is the additional
graph-theoretic condition needed to preserve proper edge coloring across the
boundary of the swapped edge set.

The set `K` is only a predicate on edges.  In applications it can be the edge
set of a two-color Kempe component, but none of the rainbow-safety theorems
silently assumes that physical realization.
-/

namespace TotalColoring

universe u v

namespace EdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- The edges in `J` receive pairwise distinct colors. -/
def RainbowOn (a : EdgeAssignment G C) (J : Set G.edgeSet) : Prop :=
  ∀ {e}, e ∈ J → ∀ {f}, f ∈ J → e ≠ f → a.color e ≠ a.color f

/-- The set-based rainbow predicate agrees with the selector-based predicate
used by the auxiliary decoding interface. -/
theorem rainbowOn_range_iff {I : Type*} (a : EdgeAssignment G C)
    (distinguished : I → G.edgeSet) :
    a.RainbowOn (Set.range distinguished) ↔ a.Rainbow distinguished := by
  constructor
  · intro h v w hvw
    exact h ⟨v, rfl⟩ ⟨w, rfl⟩ hvw
  · intro h e he f hf hef
    rcases he with ⟨v, rfl⟩
    rcases hf with ⟨w, rfl⟩
    exact h v w hef

/-- A color is absent from the distinguished edge set `J`. -/
def ColorUnusedOn (a : EdgeAssignment G C) (J : Set G.edgeSet) (c : C) : Prop :=
  ∀ {e}, e ∈ J → a.color e ≠ c

/-- The edge `carrier` is the unique edge of `J` with color `c`. -/
def IsUniqueColorOn (a : EdgeAssignment G C) (J : Set G.edgeSet)
    (c : C) (carrier : G.edgeSet) : Prop :=
  carrier ∈ J ∧ a.color carrier = c ∧
    ∀ {e}, e ∈ J → a.color e = c → e = carrier

/-- On a rainbow distinguished set, any exhibited carrier of a color is its
unique carrier. -/
theorem isUniqueColorOn_of_rainbowOn (a : EdgeAssignment G C)
    (J : Set G.edgeSet) {c : C} {carrier : G.edgeSet} (hrainbow : a.RainbowOn J)
    (hcarrier : carrier ∈ J) (hcolor : a.color carrier = c) :
    a.IsUniqueColorOn J c carrier := by
  refine ⟨hcarrier, hcolor, ?_⟩
  intro e he hce
  by_contra hne
  exact (hrainbow he hcarrier hne) (hce.trans hcolor.symm)

/-- Swap `α` and `β` exactly on the selected edge set `K`. -/
def swapOn [DecidableEq C] (a : EdgeAssignment G C) (α β : C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)] : EdgeAssignment G C where
  color e := if e ∈ K then Equiv.swap α β (a.color e) else a.color e

@[simp]
theorem swapOn_color_of_mem [DecidableEq C] (a : EdgeAssignment G C) (α β : C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)] {e : G.edgeSet} (he : e ∈ K) :
    (a.swapOn α β K).color e = Equiv.swap α β (a.color e) := by
  simp [swapOn, he]

@[simp]
theorem swapOn_color_of_not_mem [DecidableEq C] (a : EdgeAssignment G C) (α β : C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)] {e : G.edgeSet} (he : e ∉ K) :
    (a.swapOn α β K).color e = a.color e := by
  simp [swapOn, he]

/-- The exact distinguished-set compatibility condition for a two-color swap:
every `α`-edge and every `β`-edge in `J` lie on the same side of `K`. -/
def SwapCompatibleOn (a : EdgeAssignment G C) (J : Set G.edgeSet)
    (α β : C) (K : Set G.edgeSet) : Prop :=
  ∀ {e}, e ∈ J → a.color e = α →
    ∀ {f}, f ∈ J → a.color f = β → (e ∈ K ↔ f ∈ K)

/-- Exact rainbow-safety criterion for a two-color swap on `J`.

The original rainbow hypothesis makes each of `α` and `β` unique on `J`
when present.  The theorem says that the swap remains rainbow exactly when
their carriers, if both exist, are either both selected or both unselected. -/
theorem rainbowOn_swapOn_iff [DecidableEq C] (a : EdgeAssignment G C)
    (J K : Set G.edgeSet) [DecidablePred (· ∈ K)] {α β : C}
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β) :
    (a.swapOn α β K).RainbowOn J ↔ a.SwapCompatibleOn J α β K := by
  constructor
  · intro hswap e he hce f hf hcf
    have hef : e ≠ f := by
      intro hef
      subst f
      exact hαβ (hce.symm.trans hcf)
    constructor
    · intro heK
      by_contra hfK
      exact (hswap he hf hef) (by
        simp [swapOn, heK, hfK, hce, hcf])
    · intro hfK
      by_contra heK
      exact (hswap he hf hef) (by
        simp [swapOn, heK, hfK, hce, hcf])
  · intro hcompatible e he f hf hef
    have hne := hrainbow he hf hef
    by_cases heK : e ∈ K
    · by_cases hfK : f ∈ K
      · have hinj : Equiv.swap α β (a.color e) ≠ Equiv.swap α β (a.color f) :=
          fun h ↦ hne ((Equiv.swap α β).injective h)
        simpa [swapOn, heK, hfK] using hinj
      · intro heq
        have hmoved : Equiv.swap α β (a.color e) ≠ a.color e := by
          intro hfixed
          apply hne
          exact hfixed.symm.trans (by simpa [swapOn, heK, hfK] using heq)
        rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hce | hce
        · have hcf : a.color f = β := by
            have : β = a.color f := by
              simpa [swapOn, heK, hfK, hce] using heq
            exact this.symm
          exact hfK ((hcompatible he hce hf hcf).mp heK)
        · have hcf : a.color f = α := by
            have : α = a.color f := by
              simpa [swapOn, heK, hfK, hce] using heq
            exact this.symm
          exact hfK ((hcompatible hf hcf he hce).mpr heK)
    · by_cases hfK : f ∈ K
      · intro heq
        have hmoved : Equiv.swap α β (a.color f) ≠ a.color f := by
          intro hfixed
          apply hne
          have hcross : a.color e = Equiv.swap α β (a.color f) := by
            simpa [swapOn, heK, hfK] using heq
          exact hcross.trans hfixed
        rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hcf | hcf
        · have hce : a.color e = β := by
            simpa [swapOn, heK, hfK, hcf] using heq
          exact heK ((hcompatible hf hcf he hce).mp hfK)
        · have hce : a.color e = α := by
            simpa [swapOn, heK, hfK, hcf] using heq
          exact heK ((hcompatible he hce hf hcf).mpr hfK)
      · simpa [swapOn, heK, hfK] using hne

/-- If `α` is unused on `J`, every `α`-`β` swap set is compatible. -/
theorem swapCompatibleOn_of_unused_left (a : EdgeAssignment G C)
    (J K : Set G.edgeSet) {α β : C} (hunused : a.ColorUnusedOn J α) :
    a.SwapCompatibleOn J α β K := by
  intro e he hce
  exact (hunused he hce).elim

/-- If `β` is unused on `J`, every `α`-`β` swap set is compatible. -/
theorem swapCompatibleOn_of_unused_right (a : EdgeAssignment G C)
    (J K : Set G.edgeSet) {α β : C} (hunused : a.ColorUnusedOn J β) :
    a.SwapCompatibleOn J α β K := by
  intro e he hce f hf hcf
  exact (hunused hf hcf).elim

/-- If both colors have unique carriers in `J` and those carriers lie on the
same side of `K`, then the exact compatibility condition holds. -/
theorem swapCompatibleOn_of_unique_same_side (a : EdgeAssignment G C)
    (J K : Set G.edgeSet) {α β : C} {eα eβ : G.edgeSet}
    (hα : a.IsUniqueColorOn J α eα) (hβ : a.IsUniqueColorOn J β eβ)
    (hsame : eα ∈ K ↔ eβ ∈ K) : a.SwapCompatibleOn J α β K := by
  rcases hα with ⟨-, -, huniqueα⟩
  rcases hβ with ⟨-, -, huniqueβ⟩
  intro e he hce f hf hcf
  rw [huniqueα he hce, huniqueβ hf hcf]
  exact hsame

/-- Rainbow safety when one swap color is unused on `J`. -/
theorem rainbowOn_swapOn_of_unused_left [DecidableEq C] (a : EdgeAssignment G C)
    (J K : Set G.edgeSet) [DecidablePred (· ∈ K)] {α β : C}
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β) (hunused : a.ColorUnusedOn J α) :
    (a.swapOn α β K).RainbowOn J :=
  (rainbowOn_swapOn_iff a J K hrainbow hαβ).2
    (swapCompatibleOn_of_unused_left a J K hunused)

/-- Symmetric rainbow safety when `β` is unused on `J`. -/
theorem rainbowOn_swapOn_of_unused_right [DecidableEq C] (a : EdgeAssignment G C)
    (J K : Set G.edgeSet) [DecidablePred (· ∈ K)] {α β : C}
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β) (hunused : a.ColorUnusedOn J β) :
    (a.swapOn α β K).RainbowOn J :=
  (rainbowOn_swapOn_iff a J K hrainbow hαβ).2
    (swapCompatibleOn_of_unused_right a J K hunused)

/-- Rainbow safety when either swap color is unused on `J`. -/
theorem rainbowOn_swapOn_of_one_unused [DecidableEq C] (a : EdgeAssignment G C)
    (J K : Set G.edgeSet) [DecidablePred (· ∈ K)] {α β : C}
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (hunused : a.ColorUnusedOn J α ∨ a.ColorUnusedOn J β) :
    (a.swapOn α β K).RainbowOn J := by
  rcases hunused with hunused | hunused
  · exact rainbowOn_swapOn_of_unused_left a J K hrainbow hαβ hunused
  · exact rainbowOn_swapOn_of_unused_right a J K hrainbow hαβ hunused

/-- Rainbow safety when both unique distinguished carriers are swapped
together or both left fixed. -/
theorem rainbowOn_swapOn_of_unique_same_side [DecidableEq C]
    (a : EdgeAssignment G C) (J K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    {α β : C} {eα eβ : G.edgeSet} (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (hα : a.IsUniqueColorOn J α eα) (hβ : a.IsUniqueColorOn J β eβ)
    (hsame : eα ∈ K ↔ eβ ∈ K) : (a.swapOn α β K).RainbowOn J :=
  (rainbowOn_swapOn_iff a J K hrainbow hαβ).2
    (swapCompatibleOn_of_unique_same_side a J K hα hβ hsame)

/-- The carrier form of the safety criterion: if both colors occur on `J`,
their carriers are automatically unique, and swapping neither or both
preserves rainbowness. -/
theorem rainbowOn_swapOn_of_carriers_same_side [DecidableEq C]
    (a : EdgeAssignment G C) (J K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    {α β : C} {eα eβ : G.edgeSet} (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (heα : eα ∈ J) (hcolorα : a.color eα = α)
    (heβ : eβ ∈ J) (hcolorβ : a.color eβ = β)
    (hsame : eα ∈ K ↔ eβ ∈ K) : (a.swapOn α β K).RainbowOn J :=
  rainbowOn_swapOn_of_unique_same_side a J K hrainbow hαβ
    (isUniqueColorOn_of_rainbowOn a J hrainbow heα hcolorα)
    (isUniqueColorOn_of_rainbowOn a J hrainbow heβ hcolorβ) hsame

/-- No adjacent `α`-edge and `β`-edge is cut by the boundary of `K`.

This is the physical hypothesis supplied when `K` is a complete two-color
Kempe component.  It is deliberately separate from distinguished-set safety. -/
def TwoColorBoundaryClosed (a : EdgeAssignment G C) (α β : C)
    (K : Set G.edgeSet) : Prop :=
  ∀ {e f}, G.lineGraph.Adj e f → a.color e = α → a.color f = β →
    (e ∈ K ↔ f ∈ K)

/-- A proper edge coloring remains proper after a two-color swap whose edge
set is closed across every adjacent `α`-`β` pair. -/
theorem valid_swapOn_of_boundaryClosed [DecidableEq C] (a : EdgeAssignment G C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)] {α β : C}
    (hvalid : a.Valid) (hclosed : a.TwoColorBoundaryClosed α β K) :
    (a.swapOn α β K).Valid := by
  intro e f hef
  have hne := hvalid e f hef
  by_cases heK : e ∈ K
  · by_cases hfK : f ∈ K
    · have hinj : Equiv.swap α β (a.color e) ≠ Equiv.swap α β (a.color f) :=
        fun h ↦ hne ((Equiv.swap α β).injective h)
      simpa [swapOn, heK, hfK] using hinj
    · intro heq
      have hmoved : Equiv.swap α β (a.color e) ≠ a.color e := by
        intro hfixed
        apply hne
        exact hfixed.symm.trans (by simpa [swapOn, heK, hfK] using heq)
      rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hce | hce
      · have hcf : a.color f = β := by
          have : β = a.color f := by simpa [swapOn, heK, hfK, hce] using heq
          exact this.symm
        exact hfK ((hclosed hef hce hcf).mp heK)
      · have hcf : a.color f = α := by
          have : α = a.color f := by simpa [swapOn, heK, hfK, hce] using heq
          exact this.symm
        exact hfK ((hclosed hef.symm hcf hce).mpr heK)
  · by_cases hfK : f ∈ K
    · intro heq
      have hmoved : Equiv.swap α β (a.color f) ≠ a.color f := by
        intro hfixed
        apply hne
        have hcross : a.color e = Equiv.swap α β (a.color f) := by
          simpa [swapOn, heK, hfK] using heq
        exact hcross.trans hfixed
      rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hcf | hcf
      · have hce : a.color e = β := by simpa [swapOn, heK, hfK, hcf] using heq
        exact heK ((hclosed hef.symm hcf hce).mp hfK)
      · have hce : a.color e = α := by simpa [swapOn, heK, hfK, hcf] using heq
        exact heK ((hclosed hef hce hcf).mpr hfK)
    · simpa [swapOn, heK, hfK] using hne

end EdgeAssignment

end TotalColoring
