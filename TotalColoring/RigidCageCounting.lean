import Mathlib

/-!
# Counting kernels for the rigid-cage branch

This module proves the finite counting kernel used to choose two inactive
donor colours in the rigid `K₆` cage.  It is deliberately phrased for an
arbitrary finite set of oriented candidate pairs.  A later graph-facing
module must prove that a simple four-regular complement supplies exactly four
times as many oriented pairs as vertices and must transport the selected pair
to an endpoint certificate.

Nothing here proves the rigid-cage structural dichotomy, an endpoint theorem,
or a total-colouring theorem.
-/

namespace TotalColoring.RigidCageCounting

variable {α β : Type*}

section BadClasses

variable [Fintype α] [DecidableEq β]

/-- Candidate pairs failing because the first tail is the second owner. -/
def firstOwnerBad
    (A : Finset (α × α)) (f owner : α → β) : Finset (α × α) :=
  A.filter fun p ↦ f p.1 = owner p.2

/-- Candidate pairs failing because the second tail is the first owner. -/
def secondOwnerBad
    (A : Finset (α × α)) (g owner : α → β) : Finset (α × α) :=
  A.filter fun p ↦ g p.2 = owner p.1

/-- Candidate pairs whose two physical tails collide. -/
def tailCollisionBad
    (A : Finset (α × α)) (f g : α → β) : Finset (α × α) :=
  A.filter fun p ↦ f p.1 = g p.2

/-- Injectivity of the owner map bounds the first owner-collision class by
the number of possible first coordinates. -/
theorem card_firstOwnerBad_le
    (A : Finset (α × α)) (f owner : α → β)
    (howner : Function.Injective owner) :
    (firstOwnerBad A f owner).card ≤ Fintype.card α := by
  classical
  refine Finset.card_le_card_of_injOn Prod.fst (by simp) ?_
  rintro ⟨d, e⟩ hp ⟨d', e'⟩ hq hfst
  change d = d' at hfst
  subst d'
  have hpbad : f d = owner e :=
    (Finset.mem_filter.mp hp).2
  have hqbad : f d = owner e' :=
    (Finset.mem_filter.mp hq).2
  have he : e = e' := howner (hpbad.symm.trans hqbad)
  simp [he]

/-- Injectivity of the owner map bounds the second owner-collision class by
the number of possible second coordinates. -/
theorem card_secondOwnerBad_le
    (A : Finset (α × α)) (g owner : α → β)
    (howner : Function.Injective owner) :
    (secondOwnerBad A g owner).card ≤ Fintype.card α := by
  classical
  refine Finset.card_le_card_of_injOn Prod.snd (by simp) ?_
  rintro ⟨d, e⟩ hp ⟨d', e'⟩ hq hsnd
  change e = e' at hsnd
  subst e'
  have hpbad : g e = owner d :=
    (Finset.mem_filter.mp hp).2
  have hqbad : g e = owner d' :=
    (Finset.mem_filter.mp hq).2
  have hd : d = d' := howner (hpbad.symm.trans hqbad)
  simp [hd]

/-- Injectivity of the second tail map bounds the tail-collision class by
the number of possible first coordinates. -/
theorem card_tailCollisionBad_le_of_injective_right
    (A : Finset (α × α)) (f g : α → β)
    (hg : Function.Injective g) :
    (tailCollisionBad A f g).card ≤ Fintype.card α := by
  classical
  refine Finset.card_le_card_of_injOn Prod.fst (by simp) ?_
  rintro ⟨d, e⟩ hp ⟨d', e'⟩ hq hfst
  change d = d' at hfst
  subst d'
  have hpbad : f d = g e :=
    (Finset.mem_filter.mp hp).2
  have hqbad : f d = g e' :=
    (Finset.mem_filter.mp hq).2
  have he : e = e' := hg (hpbad.symm.trans hqbad)
  simp [he]

/-- The symmetric tail-collision bound, using injectivity of the first map. -/
theorem card_tailCollisionBad_le_of_injective_left
    (A : Finset (α × α)) (f g : α → β)
    (hf : Function.Injective f) :
    (tailCollisionBad A f g).card ≤ Fintype.card α := by
  classical
  refine Finset.card_le_card_of_injOn Prod.snd (by simp) ?_
  rintro ⟨d, e⟩ hp ⟨d', e'⟩ hq hsnd
  change e = e' at hsnd
  subst e'
  have hpbad : f d = g e :=
    (Finset.mem_filter.mp hp).2
  have hqbad : f d' = g e :=
    (Finset.mem_filter.mp hq).2
  have hd : d = d' := hf (hpbad.trans hqbad.symm)
  simp [hd]

/-- Three injective collision classes cannot cover a candidate set larger
than three times the coordinate type.

This is the abstract pigeonhole step behind the directed four-regular
avoidance argument. -/
theorem exists_collision_free_of_three_mul_card_lt
    (A : Finset (α × α)) (f g owner : α → β)
    (hf : Function.Injective f)
    (hg : Function.Injective g)
    (howner : Function.Injective owner)
    (hlarge : 3 * Fintype.card α < A.card) :
    ∃ p ∈ A,
      f p.1 ≠ owner p.2 ∧
      g p.2 ≠ owner p.1 ∧
      f p.1 ≠ g p.2 := by
  classical
  let B₁ := firstOwnerBad A f owner
  let B₂ := secondOwnerBad A g owner
  let B₃ := tailCollisionBad A f g
  have hB₁ : B₁.card ≤ Fintype.card α := by
    simpa [B₁] using card_firstOwnerBad_le A f owner howner
  have hB₂ : B₂.card ≤ Fintype.card α := by
    simpa [B₂] using card_secondOwnerBad_le A g owner howner
  have hB₃left : B₃.card ≤ Fintype.card α := by
    simpa [B₃] using card_tailCollisionBad_le_of_injective_left A f g hf
  have hB₃right : B₃.card ≤ Fintype.card α := by
    simpa [B₃] using card_tailCollisionBad_le_of_injective_right A f g hg
  have hB₃ : B₃.card ≤ Fintype.card α := by
    exact (Nat.le_min.mpr ⟨hB₃left, hB₃right⟩).trans_eq (min_self _)
  by_contra hgood
  have hbad : ∀ p ∈ A,
      f p.1 = owner p.2 ∨
      g p.2 = owner p.1 ∨
      f p.1 = g p.2 := by
    intro p hp
    by_contra hnone
    push Not at hnone
    exact hgood ⟨p, hp, hnone.1, hnone.2.1, hnone.2.2⟩
  have hcover : A ⊆ B₁ ∪ B₂ ∪ B₃ := by
    intro p hp
    rcases hbad p hp with h₁ | h₂ | h₃
    · exact Finset.mem_union_left B₃ <|
        Finset.mem_union_left B₂ <| by simp [B₁, firstOwnerBad, hp, h₁]
    · exact Finset.mem_union_left B₃ <|
        Finset.mem_union_right B₁ <| by simp [B₂, secondOwnerBad, hp, h₂]
    · exact Finset.mem_union_right (B₁ ∪ B₂) <| by
        simp [B₃, tailCollisionBad, hp, h₃]
  have hcardCover : A.card ≤ (B₁ ∪ B₂ ∪ B₃).card :=
    Finset.card_le_card hcover
  have hcardUnion : (B₁ ∪ B₂ ∪ B₃).card ≤ B₁.card + B₂.card + B₃.card := by
    calc
      (B₁ ∪ B₂ ∪ B₃).card ≤ (B₁ ∪ B₂).card + B₃.card :=
        Finset.card_union_le _ _
      _ ≤ (B₁.card + B₂.card) + B₃.card := by
        exact Nat.add_le_add_right (Finset.card_union_le B₁ B₂) B₃.card
  omega

/-- The numerical form used for a four-regular directed edge set: `4m`
candidates leave one pair outside the three collision classes of size at most
`m` each. -/
theorem directed_four_regular_avoidance
    (A : Finset (α × α)) (f g owner : α → β)
    (hf : Function.Injective f)
    (hg : Function.Injective g)
    (howner : Function.Injective owner)
    (hnonempty : 0 < Fintype.card α)
    (hcard : A.card = 4 * Fintype.card α) :
    ∃ p ∈ A,
      f p.1 ≠ owner p.2 ∧
      g p.2 ≠ owner p.1 ∧
      f p.1 ≠ g p.2 := by
  apply exists_collision_free_of_three_mul_card_lt A f g owner hf hg howner
  omega

end BadClasses

end TotalColoring.RigidCageCounting
