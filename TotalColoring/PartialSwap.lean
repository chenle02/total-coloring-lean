import TotalColoring.Partial

/-!
# Rainbow-safe two-color swaps for partial edge colorings

This module extends the two-color swap interface to partial edge colorings.
Uncolored edges remain uncolored.  As in `TotalColoring.RainbowSwap`, the
distinguished-set safety condition and the graph-theoretic boundary-closure
condition are kept separate: the former is exact for preserving a colored
rainbow set, while the latter is sufficient for preserving partial
properness.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Swap `α` and `β` exactly on the selected edge set `K`.  The `Option.map`
definition makes the uncolored value `none` fixed by construction. -/
def swapOn [DecidableEq C] (a : PartialEdgeAssignment G C) (α β : C)
    (K : Set G.edgeSet) [DecidablePred (· ∈ K)] : PartialEdgeAssignment G C where
  color e := if e ∈ K then (a.color e).map (Equiv.swap α β) else a.color e

@[simp]
theorem swapOn_color_of_mem [DecidableEq C] (a : PartialEdgeAssignment G C)
    (α β : C) (K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    {e : G.edgeSet} (he : e ∈ K) :
    (a.swapOn α β K).color e = (a.color e).map (Equiv.swap α β) := by
  simp [swapOn, he]

@[simp]
theorem swapOn_color_of_not_mem [DecidableEq C] (a : PartialEdgeAssignment G C)
    (α β : C) (K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    {e : G.edgeSet} (he : e ∉ K) :
    (a.swapOn α β K).color e = a.color e := by
  simp [swapOn, he]

/-- A two-color swap preserves exactly which edges are uncolored. -/
@[simp]
theorem swapOn_color_eq_none_iff [DecidableEq C] (a : PartialEdgeAssignment G C)
    (α β : C) (K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    (e : G.edgeSet) :
    (a.swapOn α β K).color e = none ↔ a.color e = none := by
  by_cases he : e ∈ K <;> simp [swapOn, he]

/-- Swapping colors does not create or remove holes. -/
theorem swapOn_complete_iff [DecidableEq C] (a : PartialEdgeAssignment G C)
    (α β : C) (K : Set G.edgeSet) [DecidablePred (· ∈ K)] :
    (a.swapOn α β K).Complete ↔ a.Complete := by
  constructor
  · intro h e
    rcases h e with ⟨c, hc⟩
    have hnotnone : a.color e ≠ none := by
      intro hnone
      have : (a.swapOn α β K).color e = none :=
        (swapOn_color_eq_none_iff a α β K e).2 hnone
      exact Option.some_ne_none c (hc.symm.trans this)
    cases hcolor : a.color e with
    | none => exact (hnotnone hcolor).elim
    | some d => exact ⟨d, rfl⟩
  · intro h e
    rcases h e with ⟨c, hc⟩
    by_cases he : e ∈ K
    · exact ⟨Equiv.swap α β c, by simp [swapOn, he, hc]⟩
    · exact ⟨c, by simp [swapOn, he, hc]⟩

/-- A two-color swap preserves the location of a unique hole. -/
theorem swapOn_oneHoleAt_iff [DecidableEq C] (a : PartialEdgeAssignment G C)
    (α β : C) (K : Set G.edgeSet) [DecidablePred (· ∈ K)]
    (e : G.edgeSet) :
    (a.swapOn α β K).OneHoleAt e ↔ a.OneHoleAt e := by
  simp only [OneHoleAt, swapOn_color_eq_none_iff]

/-- A color is absent from the colored distinguished edges in `J`. -/
def ColorUnusedOn (a : PartialEdgeAssignment G C) (J : Set G.edgeSet) (c : C) : Prop :=
  ∀ {e}, e ∈ J → a.color e ≠ some c

/-- The edge `carrier` is the unique edge of `J` colored `c`. -/
def IsUniqueColorOn (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (c : C) (carrier : G.edgeSet) : Prop :=
  carrier ∈ J ∧ a.color carrier = some c ∧
    ∀ {e}, e ∈ J → a.color e = some c → e = carrier

/-- On a partial rainbow distinguished set, an exhibited carrier of a color is
its unique carrier. -/
theorem isUniqueColorOn_of_rainbowOn (a : PartialEdgeAssignment G C)
    (J : Set G.edgeSet) {c : C} {carrier : G.edgeSet}
    (hrainbow : a.RainbowOn J) (hcarrier : carrier ∈ J)
    (hcolor : a.color carrier = some c) :
    a.IsUniqueColorOn J c carrier := by
  refine ⟨hcarrier, hcolor, ?_⟩
  intro e he hce
  by_contra hne
  exact (hrainbow.2 he hcarrier hne) (hce.trans hcolor.symm)

/-- The exact distinguished-set compatibility condition for a partial
two-color swap: every `α`-edge and every `β`-edge in `J` lie on the same side
of `K`. -/
def SwapCompatibleOn (a : PartialEdgeAssignment G C) (J : Set G.edgeSet)
    (α β : C) (K : Set G.edgeSet) : Prop :=
  ∀ {e}, e ∈ J → a.color e = some α →
    ∀ {f}, f ∈ J → a.color f = some β → (e ∈ K ↔ f ∈ K)

/-- A swap preserves the fact that every distinguished edge is colored. -/
theorem coloredOn_swapOn [DecidableEq C] (a : PartialEdgeAssignment G C)
    (J K : Set G.edgeSet) [DecidablePred (· ∈ K)] {α β : C}
    (hcolored : a.ColoredOn J) : (a.swapOn α β K).ColoredOn J := by
  intro e he
  rcases hcolored e he with ⟨c, hc⟩
  by_cases heK : e ∈ K
  · exact ⟨Equiv.swap α β c, by simp [swapOn, heK, hc]⟩
  · exact ⟨c, by simp [swapOn, heK, hc]⟩

/-- Exact rainbow-safety criterion for a partial two-color swap on a colored
rainbow distinguished set. -/
theorem rainbowOn_swapOn_iff [DecidableEq C] (a : PartialEdgeAssignment G C)
    (J K : Set G.edgeSet) [DecidablePred (· ∈ K)] {α β : C}
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β) :
    (a.swapOn α β K).RainbowOn J ↔ a.SwapCompatibleOn J α β K := by
  constructor
  · intro hswap e he hce f hf hcf
    have hef : e ≠ f := by
      intro hef
      subst f
      exact hαβ (Option.some.inj (hce.symm.trans hcf))
    constructor
    · intro heK
      by_contra hfK
      exact (hswap.2 he hf hef) (by
        simp [swapOn, heK, hfK, hce, hcf])
    · intro hfK
      by_contra heK
      exact (hswap.2 he hf hef) (by
        simp [swapOn, heK, hfK, hce, hcf])
  · intro hcompatible
    refine ⟨coloredOn_swapOn a J K hrainbow.1, ?_⟩
    intro e he f hf hef
    rcases hrainbow.1 e he with ⟨ce, hce⟩
    rcases hrainbow.1 f hf with ⟨cf, hcf⟩
    have hne : ce ≠ cf := by
      intro heq
      apply hrainbow.2 he hf hef
      simp [hce, hcf, heq]
    by_cases heK : e ∈ K
    · by_cases hfK : f ∈ K
      · intro heq
        have heq' : Equiv.swap α β ce = Equiv.swap α β cf :=
          Option.some.inj (by simpa [swapOn, heK, hfK, hce, hcf] using heq)
        exact hne ((Equiv.swap α β).injective heq')
      · intro heq
        have heq' : Equiv.swap α β ce = cf :=
          Option.some.inj (by simpa [swapOn, heK, hfK, hce, hcf] using heq)
        have hmoved : Equiv.swap α β ce ≠ ce := by
          intro hfixed
          exact hne (hfixed.symm.trans heq')
        rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hceα | hceβ
        · have hcfβ : cf = β := by simpa [hceα] using heq'.symm
          exact hfK ((hcompatible he (hce.trans (congrArg some hceα))
            hf (hcf.trans (congrArg some hcfβ))).mp heK)
        · have hcfα : cf = α := by simpa [hceβ] using heq'.symm
          exact hfK ((hcompatible hf (hcf.trans (congrArg some hcfα))
            he (hce.trans (congrArg some hceβ))).mpr heK)
    · by_cases hfK : f ∈ K
      · intro heq
        have heq' : ce = Equiv.swap α β cf :=
          Option.some.inj (by simpa [swapOn, heK, hfK, hce, hcf] using heq)
        have hmoved : Equiv.swap α β cf ≠ cf := by
          intro hfixed
          exact hne (heq'.trans hfixed)
        rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hcfα | hcfβ
        · have hceβ : ce = β := by simpa [hcfα] using heq'
          exact heK ((hcompatible hf (hcf.trans (congrArg some hcfα))
            he (hce.trans (congrArg some hceβ))).mp hfK)
        · have hceα : ce = α := by simpa [hcfβ] using heq'
          exact heK ((hcompatible he (hce.trans (congrArg some hceα))
            hf (hcf.trans (congrArg some hcfβ))).mpr hfK)
      · intro heq
        exact hne (Option.some.inj (by
          simpa [swapOn, heK, hfK, hce, hcf] using heq))

/-- If `α` is unused on `J`, every partial `α`-`β` swap set is compatible. -/
theorem swapCompatibleOn_of_unused_left (a : PartialEdgeAssignment G C)
    (J K : Set G.edgeSet) {α β : C} (hunused : a.ColorUnusedOn J α) :
    a.SwapCompatibleOn J α β K := by
  intro e he hce
  exact (hunused he hce).elim

/-- If `β` is unused on `J`, every partial `α`-`β` swap set is compatible. -/
theorem swapCompatibleOn_of_unused_right (a : PartialEdgeAssignment G C)
    (J K : Set G.edgeSet) {α β : C} (hunused : a.ColorUnusedOn J β) :
    a.SwapCompatibleOn J α β K := by
  intro e he hce f hf hcf
  exact (hunused hf hcf).elim

/-- If both colors have unique carriers in `J` and those carriers lie on the
same side of `K`, then the exact compatibility condition holds. -/
theorem swapCompatibleOn_of_unique_same_side (a : PartialEdgeAssignment G C)
    (J K : Set G.edgeSet) {α β : C} {eα eβ : G.edgeSet}
    (hα : a.IsUniqueColorOn J α eα) (hβ : a.IsUniqueColorOn J β eβ)
    (hsame : eα ∈ K ↔ eβ ∈ K) : a.SwapCompatibleOn J α β K := by
  rcases hα with ⟨-, -, huniqueα⟩
  rcases hβ with ⟨-, -, huniqueβ⟩
  intro e he hce f hf hcf
  rw [huniqueα he hce, huniqueβ hf hcf]
  exact hsame

/-- Rainbow safety when one swap color is unused on `J`. -/
theorem rainbowOn_swapOn_of_unused_left [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} (hrainbow : a.RainbowOn J)
    (hαβ : α ≠ β) (hunused : a.ColorUnusedOn J α) :
    (a.swapOn α β K).RainbowOn J :=
  (rainbowOn_swapOn_iff a J K hrainbow hαβ).2
    (swapCompatibleOn_of_unused_left a J K hunused)

/-- Symmetric rainbow safety when `β` is unused on `J`. -/
theorem rainbowOn_swapOn_of_unused_right [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} (hrainbow : a.RainbowOn J)
    (hαβ : α ≠ β) (hunused : a.ColorUnusedOn J β) :
    (a.swapOn α β K).RainbowOn J :=
  (rainbowOn_swapOn_iff a J K hrainbow hαβ).2
    (swapCompatibleOn_of_unused_right a J K hunused)

/-- Rainbow safety when either swap color is unused on `J`. -/
theorem rainbowOn_swapOn_of_one_unused [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} (hrainbow : a.RainbowOn J)
    (hαβ : α ≠ β)
    (hunused : a.ColorUnusedOn J α ∨ a.ColorUnusedOn J β) :
    (a.swapOn α β K).RainbowOn J := by
  rcases hunused with hunused | hunused
  · exact rainbowOn_swapOn_of_unused_left a J K hrainbow hαβ hunused
  · exact rainbowOn_swapOn_of_unused_right a J K hrainbow hαβ hunused

/-- Rainbow safety when both unique distinguished carriers are swapped
together or both left fixed. -/
theorem rainbowOn_swapOn_of_unique_same_side [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} {eα eβ : G.edgeSet}
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (hα : a.IsUniqueColorOn J α eα) (hβ : a.IsUniqueColorOn J β eβ)
    (hsame : eα ∈ K ↔ eβ ∈ K) : (a.swapOn α β K).RainbowOn J :=
  (rainbowOn_swapOn_iff a J K hrainbow hαβ).2
    (swapCompatibleOn_of_unique_same_side a J K hα hβ hsame)

/-- The carrier form of partial rainbow safety. -/
theorem rainbowOn_swapOn_of_carriers_same_side [DecidableEq C]
    (a : PartialEdgeAssignment G C) (J K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} {eα eβ : G.edgeSet}
    (hrainbow : a.RainbowOn J) (hαβ : α ≠ β)
    (heα : eα ∈ J) (hcolorα : a.color eα = some α)
    (heβ : eβ ∈ J) (hcolorβ : a.color eβ = some β)
    (hsame : eα ∈ K ↔ eβ ∈ K) : (a.swapOn α β K).RainbowOn J :=
  rainbowOn_swapOn_of_unique_same_side a J K hrainbow hαβ
    (isUniqueColorOn_of_rainbowOn a J hrainbow heα hcolorα)
    (isUniqueColorOn_of_rainbowOn a J hrainbow heβ hcolorβ) hsame

/-- No adjacent colored `α`-edge and `β`-edge is cut by the boundary of `K`.

This is the explicit physical hypothesis supplied when `K` is the edge set of
a complete two-color Kempe component. -/
def TwoColorBoundaryClosed (a : PartialEdgeAssignment G C) (α β : C)
    (K : Set G.edgeSet) : Prop :=
  ∀ {e f}, G.lineGraph.Adj e f → a.color e = some α → a.color f = some β →
    (e ∈ K ↔ f ∈ K)

/-- Partial properness is preserved by a two-color swap whose selected edge
set is closed across every adjacent colored `α`-`β` pair. -/
theorem valid_swapOn_of_boundaryClosed [DecidableEq C]
    (a : PartialEdgeAssignment G C) (K : Set G.edgeSet)
    [DecidablePred (· ∈ K)] {α β : C} (hvalid : a.Valid)
    (hclosed : a.TwoColorBoundaryClosed α β K) :
    (a.swapOn α β K).Valid := by
  intro e f c hef hec
  cases hce : a.color e with
  | none =>
      have : (a.swapOn α β K).color e = none :=
        (swapOn_color_eq_none_iff a α β K e).2 hce
      exact (Option.some_ne_none c (hec.symm.trans this)).elim
  | some ce =>
      cases hcf : a.color f with
      | none =>
          intro hfc
          have : (a.swapOn α β K).color f = none :=
            (swapOn_color_eq_none_iff a α β K f).2 hcf
          exact Option.some_ne_none c (hfc.symm.trans this)
      | some cf =>
          have hne : ce ≠ cf := by
            intro heq
            exact hvalid e f ce hef hce (by simpa [heq] using hcf)
          have hswapne : (a.swapOn α β K).color e ≠
              (a.swapOn α β K).color f := by
            by_cases heK : e ∈ K
            · by_cases hfK : f ∈ K
              · intro heq
                have heq' : Equiv.swap α β ce = Equiv.swap α β cf :=
                  Option.some.inj (by
                    simpa [swapOn, heK, hfK, hce, hcf] using heq)
                exact hne ((Equiv.swap α β).injective heq')
              · intro heq
                have heq' : Equiv.swap α β ce = cf :=
                  Option.some.inj (by
                    simpa [swapOn, heK, hfK, hce, hcf] using heq)
                have hmoved : Equiv.swap α β ce ≠ ce := by
                  intro hfixed
                  exact hne (hfixed.symm.trans heq')
                rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hceα | hceβ
                · have hcfβ : cf = β := by simpa [hceα] using heq'.symm
                  exact hfK ((hclosed hef (hce.trans (congrArg some hceα))
                    (hcf.trans (congrArg some hcfβ))).mp heK)
                · have hcfα : cf = α := by simpa [hceβ] using heq'.symm
                  exact hfK ((hclosed hef.symm (hcf.trans (congrArg some hcfα))
                    (hce.trans (congrArg some hceβ))).mpr heK)
            · by_cases hfK : f ∈ K
              · intro heq
                have heq' : ce = Equiv.swap α β cf :=
                  Option.some.inj (by
                    simpa [swapOn, heK, hfK, hce, hcf] using heq)
                have hmoved : Equiv.swap α β cf ≠ cf := by
                  intro hfixed
                  exact hne (heq'.trans hfixed)
                rcases Equiv.eq_or_eq_of_swap_apply_ne_self hmoved with hcfα | hcfβ
                · have hceβ : ce = β := by simpa [hcfα] using heq'
                  exact heK ((hclosed hef.symm (hcf.trans (congrArg some hcfα))
                    (hce.trans (congrArg some hceβ))).mp hfK)
                · have hceα : ce = α := by simpa [hcfβ] using heq'
                  exact heK ((hclosed hef (hce.trans (congrArg some hceα))
                    (hcf.trans (congrArg some hcfβ))).mpr hfK)
              · intro heq
                exact hne (Option.some.inj (by
                  simpa [swapOn, heK, hfK, hce, hcf] using heq))
          intro hfc
          exact hswapne (hec.trans hfc.symm)

end PartialEdgeAssignment

end TotalColoring
