import Mathlib

/-!
# Three residual rook obstruction

This module isolates the finite geometry behind three mutually blocked
residual option sets.  A point is a label--tail pair.  Points in one option
set do not repeat either coordinate, while points from different option sets
block one another by sharing a label or a tail.

If the three option sets are pairwise disjoint, then either one is empty or
all three are singletons on one common label-line or one common tail-line.
The proof is uniform in the label and tail types; it contains no finite
enumeration of either type.
-/

namespace TotalColoring.ThreeResidualRook

variable {Label Tail : Type*} [DecidableEq Label] [DecidableEq Tail]

/-- Two label--tail points attack one another as rooks: they share at least
one coordinate. -/
def SharesCoordinate (p q : Label × Tail) : Prop :=
  p.1 = q.1 ∨ p.2 = q.2

/-- Inside one residual option set, neither labels nor tails repeat. -/
def CoordinateInjective (S : Finset (Label × Tail)) : Prop :=
  (∀ ⦃p q⦄, p ∈ S → q ∈ S → p.1 = q.1 → p = q) ∧
    (∀ ⦃p q⦄, p ∈ S → q ∈ S → p.2 = q.2 → p = q)

/-- Every point of the first residual set blocks every point of the second. -/
def CrossBlocked (S T : Finset (Label × Tail)) : Prop :=
  ∀ ⦃p q⦄, p ∈ S → q ∈ T → SharesCoordinate p q

/-- Different residual sets share no exact label--tail point. -/
def PairwiseDisjoint (P : Fin 3 → Finset (Label × Tail)) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → Disjoint (P i) (P j)

/-- Every two different residual sets are cross-blocked. -/
def PairwiseCrossBlocked (P : Fin 3 → Finset (Label × Tail)) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → CrossBlocked (P i) (P j)

/-- Each residual set is a singleton, and the three unique points have the
same label. -/
def CommonLabelSingletons (P : Fin 3 → Finset (Label × Tail)) : Prop :=
  ∃ p₀ p₁ p₂ : Label × Tail,
    P 0 = {p₀} ∧ P 1 = {p₁} ∧ P 2 = {p₂} ∧
      p₀.1 = p₁.1 ∧ p₀.1 = p₂.1

/-- Each residual set is a singleton, and the three unique points have the
same tail. -/
def CommonTailSingletons (P : Fin 3 → Finset (Label × Tail)) : Prop :=
  ∃ p₀ p₁ p₂ : Label × Tail,
    P 0 = {p₀} ∧ P 1 = {p₁} ∧ P 2 = {p₂} ∧
      p₀.2 = p₁.2 ∧ p₀.2 = p₂.2

omit [DecidableEq Label] [DecidableEq Tail] in
private theorem sharesCoordinate_triangle
    {a b c : Label × Tail}
    (hab : SharesCoordinate a b)
    (hac : SharesCoordinate a c)
    (hbc : SharesCoordinate b c) :
    (a.1 = b.1 ∧ a.1 = c.1) ∨ (a.2 = b.2 ∧ a.2 = c.2) := by
  rcases hab with hab | hab
  · rcases hac with hac | hac
    · exact Or.inl ⟨hab, hac⟩
    · rcases hbc with hbc | hbc
      · exact Or.inl ⟨hab, hab.trans hbc⟩
      · exact Or.inr ⟨hac.trans hbc.symm, hac⟩
  · rcases hac with hac | hac
    · rcases hbc with hbc | hbc
      · exact Or.inl ⟨hac.trans hbc.symm, hac⟩
      · exact Or.inr ⟨hab, hab.trans hbc⟩
    · exact Or.inr ⟨hab, hac⟩

omit [DecidableEq Label] [DecidableEq Tail] in
private theorem eq_of_two_crossings_same_label
    {S : Finset (Label × Tail)}
    (hS : CoordinateInjective S)
    {p anchor b c : Label × Tail}
    (hp : p ∈ S) (hanchor : anchor ∈ S)
    (hab : anchor.1 = b.1) (hac : anchor.1 = c.1)
    (hbc : b ≠ c)
    (hpb : SharesCoordinate p b) (hpc : SharesCoordinate p c) :
    p = anchor := by
  apply hS.1 hp hanchor
  rcases hpb with hpb | hpb
  · exact hpb.trans hab.symm
  · rcases hpc with hpc | hpc
    · exact hpc.trans hac.symm
    · exfalso
      apply hbc
      apply Prod.ext
      · exact hab.symm.trans hac
      · exact hpb.symm.trans hpc

omit [DecidableEq Label] [DecidableEq Tail] in
private theorem eq_of_two_crossings_same_tail
    {S : Finset (Label × Tail)}
    (hS : CoordinateInjective S)
    {p anchor b c : Label × Tail}
    (hp : p ∈ S) (hanchor : anchor ∈ S)
    (hab : anchor.2 = b.2) (hac : anchor.2 = c.2)
    (hbc : b ≠ c)
    (hpb : SharesCoordinate p b) (hpc : SharesCoordinate p c) :
    p = anchor := by
  apply hS.2 hp hanchor
  rcases hpb with hpb | hpb
  · rcases hpc with hpc | hpc
    · exfalso
      apply hbc
      apply Prod.ext
      · exact hpb.symm.trans hpc
      · exact hab.symm.trans hac
    · exact hpc.trans hac.symm
  · exact hpb.trans hab.symm

omit [DecidableEq Label] [DecidableEq Tail] in
/-- Three nonattacking residual rook sets that are pairwise disjoint and
pairwise cross-blocked have only the advertised obstruction: an empty set, or
three singleton points on one common label-line or one common tail-line. -/
theorem empty_or_common_coordinate_singletons
    (P : Fin 3 → Finset (Label × Tail))
    (hinjective : ∀ i, CoordinateInjective (P i))
    (hdisjoint : PairwiseDisjoint P)
    (hblocked : PairwiseCrossBlocked P) :
    (∃ i, P i = ∅) ∨ CommonLabelSingletons P ∨ CommonTailSingletons P := by
  by_cases h₀ : (P 0).Nonempty
  · by_cases h₁ : (P 1).Nonempty
    · by_cases h₂ : (P 2).Nonempty
      · obtain ⟨p₀, hp₀⟩ := h₀
        obtain ⟨p₁, hp₁⟩ := h₁
        obtain ⟨p₂, hp₂⟩ := h₂
        have hp₀₁ : p₀ ≠ p₁ := by
          intro hp
          subst p₁
          exact Finset.disjoint_left.mp
            (hdisjoint (i := (0 : Fin 3)) (j := 1) (by decide)) hp₀ hp₁
        have hp₀₂ : p₀ ≠ p₂ := by
          intro hp
          subst p₂
          exact Finset.disjoint_left.mp
            (hdisjoint (i := (0 : Fin 3)) (j := 2) (by decide)) hp₀ hp₂
        have hp₁₂ : p₁ ≠ p₂ := by
          intro hp
          subst p₂
          exact Finset.disjoint_left.mp
            (hdisjoint (i := (1 : Fin 3)) (j := 2) (by decide)) hp₁ hp₂
        have hp₀₁Blocked : SharesCoordinate p₀ p₁ :=
          hblocked (i := (0 : Fin 3)) (j := 1) (by decide) hp₀ hp₁
        have hp₀₂Blocked : SharesCoordinate p₀ p₂ :=
          hblocked (i := (0 : Fin 3)) (j := 2) (by decide) hp₀ hp₂
        have hp₁₂Blocked : SharesCoordinate p₁ p₂ :=
          hblocked (i := (1 : Fin 3)) (j := 2) (by decide) hp₁ hp₂
        rcases sharesCoordinate_triangle hp₀₁Blocked hp₀₂Blocked
            hp₁₂Blocked with hlabel | htail
        · right
          left
          have hP₀ : P 0 = {p₀} := by
            refine Finset.eq_singleton_iff_unique_mem.2 ⟨hp₀, ?_⟩
            intro p hp
            exact eq_of_two_crossings_same_label (hinjective 0) hp hp₀
              hlabel.1 hlabel.2 hp₁₂
              (hblocked (i := (0 : Fin 3)) (j := 1) (by decide) hp hp₁)
              (hblocked (i := (0 : Fin 3)) (j := 2) (by decide) hp hp₂)
          have hP₁ : P 1 = {p₁} := by
            refine Finset.eq_singleton_iff_unique_mem.2 ⟨hp₁, ?_⟩
            intro p hp
            exact eq_of_two_crossings_same_label (hinjective 1) hp hp₁
              hlabel.1.symm (hlabel.1.symm.trans hlabel.2) hp₀₂
              (hblocked (i := (1 : Fin 3)) (j := 0) (by decide) hp hp₀)
              (hblocked (i := (1 : Fin 3)) (j := 2) (by decide) hp hp₂)
          have hP₂ : P 2 = {p₂} := by
            refine Finset.eq_singleton_iff_unique_mem.2 ⟨hp₂, ?_⟩
            intro p hp
            exact eq_of_two_crossings_same_label (hinjective 2) hp hp₂
              hlabel.2.symm (hlabel.2.symm.trans hlabel.1) hp₀₁
              (hblocked (i := (2 : Fin 3)) (j := 0) (by decide) hp hp₀)
              (hblocked (i := (2 : Fin 3)) (j := 1) (by decide) hp hp₁)
          exact ⟨p₀, p₁, p₂, hP₀, hP₁, hP₂, hlabel.1, hlabel.2⟩
        · right
          right
          have hP₀ : P 0 = {p₀} := by
            refine Finset.eq_singleton_iff_unique_mem.2 ⟨hp₀, ?_⟩
            intro p hp
            exact eq_of_two_crossings_same_tail (hinjective 0) hp hp₀
              htail.1 htail.2 hp₁₂
              (hblocked (i := (0 : Fin 3)) (j := 1) (by decide) hp hp₁)
              (hblocked (i := (0 : Fin 3)) (j := 2) (by decide) hp hp₂)
          have hP₁ : P 1 = {p₁} := by
            refine Finset.eq_singleton_iff_unique_mem.2 ⟨hp₁, ?_⟩
            intro p hp
            exact eq_of_two_crossings_same_tail (hinjective 1) hp hp₁
              htail.1.symm (htail.1.symm.trans htail.2) hp₀₂
              (hblocked (i := (1 : Fin 3)) (j := 0) (by decide) hp hp₀)
              (hblocked (i := (1 : Fin 3)) (j := 2) (by decide) hp hp₂)
          have hP₂ : P 2 = {p₂} := by
            refine Finset.eq_singleton_iff_unique_mem.2 ⟨hp₂, ?_⟩
            intro p hp
            exact eq_of_two_crossings_same_tail (hinjective 2) hp hp₂
              htail.2.symm (htail.2.symm.trans htail.1) hp₀₁
              (hblocked (i := (2 : Fin 3)) (j := 0) (by decide) hp hp₀)
              (hblocked (i := (2 : Fin 3)) (j := 1) (by decide) hp hp₁)
          exact ⟨p₀, p₁, p₂, hP₀, hP₁, hP₂, htail.1, htail.2⟩
      · left
        exact ⟨2, Finset.not_nonempty_iff_eq_empty.mp h₂⟩
    · left
      exact ⟨1, Finset.not_nonempty_iff_eq_empty.mp h₁⟩
  · left
    exact ⟨0, Finset.not_nonempty_iff_eq_empty.mp h₀⟩

end TotalColoring.ThreeResidualRook
