/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Tactic

open scoped BigOperators

/-!
# Hall rectangle product arithmetic

This module formalizes the finite Cartesian-product arithmetic used by the
blocker-indexed Hall-rectangle cover arguments.

Fix coordinate candidate sets `C i` indexed by `Fin n`.  If every tuple in the
source box `∏ i, C i` is caught by some blocker `b`, meaning each coordinate
lies in `N b i`, then the whole source box is exactly the blocker-indexed union

`∏ i, C i = ⋃ b, ∏ i, (C i ∩ N b i)`.

From that exact cover, the module derives finite product bounds by cardinality,
including the standard “geometric-mean side size” corollary: if every source
side has size `q` and the blocker index set has size at most `t^n`, then some
blocker box has product at least `q^n / t^n`, equivalently
`q^n ≤ t^n * ∏ i |C i ∩ N(b,i)|`.

These are finite set arithmetic statements only.  They do **not** prove the
graph-theoretic neighborhood cover, the Total Coloring Conjecture, the
identification `D = Δ(G) + 1`, or any end-to-end high-degree total-coloring
theorem.
-/

namespace TotalColoring.HallRectangles

universe u v

variable {n : ℕ}
variable {α : Fin n → Type u} {β : Type v}

/-- The coordinate product of a family of finite candidate sets. -/
def sourceBox [∀ i, DecidableEq (α i)] (C : ∀ i, Finset (α i)) : Finset (∀ i, α i) :=
  Fintype.piFinset C

/-- The blocker-indexed sub-box cut out by the coordinate neighborhoods
`N b i`. -/
def blockerBox [∀ i, DecidableEq (α i)]
    (C : ∀ i, Finset (α i)) (N : β → ∀ i, Finset (α i))
    (b : β) : Finset (∀ i, α i) :=
  Fintype.piFinset fun i ↦ C i ∩ N b i

@[simp]
theorem mem_sourceBox [∀ i, DecidableEq (α i)]
    {C : ∀ i, Finset (α i)} {x : ∀ i, α i} :
    x ∈ sourceBox C ↔ ∀ i, x i ∈ C i := by
  simp [sourceBox]

@[simp]
theorem mem_blockerBox [∀ i, DecidableEq (α i)]
    {C : ∀ i, Finset (α i)} {N : β → ∀ i, Finset (α i)}
    {b : β} {x : ∀ i, α i} :
    x ∈ blockerBox C N b ↔ ∀ i, x i ∈ C i ∩ N b i := by
  simp [blockerBox]

@[simp]
theorem sourceBox_card [∀ i, DecidableEq (α i)] (C : ∀ i, Finset (α i)) :
    (sourceBox C).card = Finset.univ.prod fun i => (C i).card := by
  simp [sourceBox]

@[simp]
theorem blockerBox_card [∀ i, DecidableEq (α i)]
    (C : ∀ i, Finset (α i)) (N : β → ∀ i, Finset (α i))
    (b : β) :
    (blockerBox C N b).card = Finset.univ.prod fun i => ((C i ∩ N b i).card) := by
  simp [blockerBox]

/-- If every tuple in the source box is caught coordinatewise by some blocker,
the source box is exactly the union of the blocker boxes. -/
theorem sourceBox_eq_biUnion_blockerBox_of_cover
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (B : Finset β) (C : ∀ i, Finset (α i)) (N : β → ∀ i, Finset (α i))
    (hcover : ∀ x, x ∈ sourceBox C → ∃ b ∈ B, ∀ i, x i ∈ N b i) :
    sourceBox C = B.biUnion (fun b ↦ blockerBox C N b) := by
  ext x
  constructor
  · intro hx
    rcases hcover x hx with ⟨b, hb, hbx⟩
    refine Finset.mem_biUnion.mpr ⟨b, hb, ?_⟩
    exact (mem_blockerBox).2 fun i ↦
      Finset.mem_inter.mpr ⟨(mem_sourceBox.mp hx) i, hbx i⟩
  · intro hx
    rcases Finset.mem_biUnion.mp hx with ⟨b, _, hxb⟩
    exact (mem_sourceBox).2 fun i ↦
      (Finset.mem_inter.mp ((mem_blockerBox.mp hxb) i)).1

/-- Cardinality form of the blocker-box cover. -/
theorem sourceBox_card_le_sum_blockerBox_card_of_cover
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    (B : Finset β) (C : ∀ i, Finset (α i)) (N : β → ∀ i, Finset (α i))
    (hcover : ∀ x, x ∈ sourceBox C → ∃ b ∈ B, ∀ i, x i ∈ N b i) :
    (sourceBox C).card ≤ B.sum (fun b => (blockerBox C N b).card) := by
  calc
    (sourceBox C).card = (B.biUnion fun b ↦ blockerBox C N b).card := by
      rw [sourceBox_eq_biUnion_blockerBox_of_cover B C N hcover]
    _ ≤ B.sum (fun b => (blockerBox C N b).card) := Finset.card_biUnion_le

/-- Some blocker box has cardinality at least the average box cardinality.  The
conclusion is stated without division to keep the bound in natural numbers. -/
theorem exists_blockerBox_card_mul_ge_sourceBox_card_of_cover
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    {B : Finset β} (hB : B.Nonempty)
    (C : ∀ i, Finset (α i)) (N : β → ∀ i, Finset (α i))
    (hcover : ∀ x, x ∈ sourceBox C → ∃ b ∈ B, ∀ i, x i ∈ N b i) :
    ∃ b ∈ B, (sourceBox C).card ≤ B.card * (blockerBox C N b).card := by
  obtain ⟨b, hb, hmax⟩ := B.exists_max_image (fun b ↦ (blockerBox C N b).card) hB
  refine ⟨b, hb, ?_⟩
  calc
    (sourceBox C).card ≤ B.sum (fun b' => (blockerBox C N b').card) :=
      sourceBox_card_le_sum_blockerBox_card_of_cover B C N hcover
    _ ≤ B.sum (fun _ => (blockerBox C N b).card) := by
      refine Finset.sum_le_sum ?_
      intro b' hb'
      exact hmax b' hb'
    _ = B.card * (blockerBox C N b).card := by simp

/-- If every source side has cardinality `q` and the blocker index set has size
at most `t^n`, then some blocker box has product large enough that its
geometric-mean side size is at least `q / t`.  The conclusion is kept in
natural-number form. -/
theorem exists_blockerBox_prod_mul_ge_pow_of_card_eq
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    {B : Finset β} (hBnonempty : B.Nonempty)
    (C : ∀ i, Finset (α i)) (N : β → ∀ i, Finset (α i))
    (hcover : ∀ x, x ∈ sourceBox C → ∃ b ∈ B, ∀ i, x i ∈ N b i)
    {q t : ℕ} (hC : ∀ i, (C i).card = q) (hB : B.card ≤ t ^ n) :
    ∃ b ∈ B, q ^ n ≤ t ^ n * Finset.univ.prod fun i => ((C i ∩ N b i).card) := by
  obtain ⟨b, hb, hlarge⟩ :=
    exists_blockerBox_card_mul_ge_sourceBox_card_of_cover hBnonempty C N hcover
  refine ⟨b, hb, ?_⟩
  calc
    q ^ n = (sourceBox C).card := by
      rw [sourceBox_card]
      simp [hC]
    _ ≤ B.card * (blockerBox C N b).card := hlarge
    _ ≤ t ^ n * (blockerBox C N b).card := by
      gcongr
    _ = t ^ n * Finset.univ.prod fun i => ((C i ∩ N b i).card) := by
      rw [blockerBox_card]

/-- The previous product estimate specialized to the `4^n` support bound used
in the Hall-rectangle geometric-mean calculation. -/
theorem exists_blockerBox_prod_mul_ge_four_pow_of_card_eq
    [∀ i, DecidableEq (α i)] [DecidableEq β]
    {B : Finset β} (hBnonempty : B.Nonempty)
    (C : ∀ i, Finset (α i)) (N : β → ∀ i, Finset (α i))
    (hcover : ∀ x, x ∈ sourceBox C → ∃ b ∈ B, ∀ i, x i ∈ N b i)
    {q : ℕ} (hC : ∀ i, (C i).card = q) (hB : B.card ≤ 4 ^ n) :
    ∃ b ∈ B, q ^ n ≤ 4 ^ n * Finset.univ.prod fun i => ((C i ∩ N b i).card) := by
  simpa using
    exists_blockerBox_prod_mul_ge_pow_of_card_eq
      hBnonempty C N hcover hC (t := 4) hB

end TotalColoring.HallRectangles
