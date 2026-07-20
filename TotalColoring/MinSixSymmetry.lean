import Mathlib

/-!
# Minimum-six active-core symmetry reduction

This module formalizes the finite symmetry quotient used for the two-triple
`K₆` core in the minimum-six active descriptor calculation.  It proves only
the group, orbit, representative, and abstract invariant-transport layer.

The predicate transported by the final theorem is supplied as an explicit
hypothesis.  In particular, this module does not define the compact descriptor
model, accept solver output, prove representative infeasibility, construct an
endpoint certificate, or prove a total-coloring theorem.
-/

open scoped Pointwise

namespace TotalColoring

namespace MinSixSymmetry

/-- The six vertices of the two-triple core. -/
abbrev Core := Fin 6

/-- A column mask on the six-vertex core. -/
abbrev Mask := Finset Core

/-- The first exceptional triple. -/
def leftTriple : Mask := {0, 1, 2}

/-- The second exceptional triple. -/
def rightTriple : Mask := {3, 4, 5}

/-- The unordered pair of exceptional triples. -/
def coreBlocks : Finset Mask := {leftTriple, rightTriple}

/-- Core permutations preserving the unordered pair of triples. -/
def CoreSymmetry : Subgroup (Equiv.Perm Core) :=
  MulAction.stabilizer (Equiv.Perm Core) coreBlocks

/-- A computable membership instance for the finite stabilizer. -/
local instance coreSymmetryMembership :
    DecidablePred (fun g : Equiv.Perm Core ↦ g ∈ CoreSymmetry) :=
  fun g ↦ show Decidable (g • coreBlocks = coreBlocks) from inferInstance

/-- A public finite enumeration of the 72 core symmetries. -/
instance coreSymmetryFintype : Fintype CoreSymmetry :=
  CoreSymmetry.instFintypeSubtypeMemOfDecidablePred

/-- The unordered two-triple stabilizer has order `72`. -/
theorem coreSymmetry_card : Fintype.card CoreSymmetry = 72 := by
  decide

/-- The unsorted pair of triple-intersection sizes. -/
abbrev RawOrbitKey := Fin 4 × Fin 4

/-- A sorted pair of triple-intersection sizes. -/
def OrbitKey := {p : RawOrbitKey // p.1 ≤ p.2}

/-- The number of selected mask vertices in the first triple. -/
def leftCount (B : Mask) : Fin 4 :=
  ⟨(B ∩ leftTriple).card, by
    have hi : B ∩ leftTriple ⊆ leftTriple := Finset.inter_subset_right
    have hcard := Finset.card_le_card hi
    simpa [leftTriple] using Nat.lt_succ_of_le hcard⟩

/-- The number of selected mask vertices in the second triple. -/
def rightCount (B : Mask) : Fin 4 :=
  ⟨(B ∩ rightTriple).card, by
    have hi : B ∩ rightTriple ⊆ rightTriple := Finset.inter_subset_right
    have hcard := Finset.card_le_card hi
    simpa [rightTriple] using Nat.lt_succ_of_le hcard⟩

/-- The sorted pair of intersection sizes classifying a mask orbit. -/
def orbitKey (B : Mask) : OrbitKey :=
  ⟨(min (leftCount B) (rightCount B),
      max (leftCount B) (rightCount B)), min_le_max⟩

deriving instance Fintype for OrbitKey
deriving instance DecidableEq for OrbitKey

/-- There are ten possible sorted intersection-size keys. -/
theorem orbitKey_card : Fintype.card OrbitKey = 10 := by
  decide

/-- A key whose two entries have total size at least two. -/
def AdmissibleKey := {k : OrbitKey // 2 ≤ k.1.1.val + k.1.2.val}

deriving instance Fintype for AdmissibleKey

/-- Exactly eight keys satisfy the ambient minimum-incidence exclusion. -/
theorem admissibleKey_card : Fintype.card AdmissibleKey = 8 := by
  decide

/-- Interpret the six low bits of a natural number as a core mask. -/
def maskOfCode (code : ℕ) : Mask :=
  Finset.univ.filter fun b ↦ code.testBit b.val

/-- The representative codes used by the final sealed finite symmetry replay.

An earlier semantic note used the alternate same-orbit masks `12` and `19`
for keys `(1,1)` and `(1,2)`.  The final replay uses `9` and `11`, respectively,
which are the codes fixed here. -/
def representativeCode (k : OrbitKey) : ℕ :=
  match k.1.1.val, k.1.2.val with
  | 0, 0 => 0
  | 0, 1 => 1
  | 0, 2 => 5
  | 0, 3 => 7
  | 1, 1 => 9
  | 1, 2 => 11
  | 1, 3 => 15
  | 2, 2 => 27
  | 2, 3 => 31
  | 3, 3 => 63
  | _, _ => 0

/-- One fixed mask representative for each sorted intersection-size key. -/
def representative (k : OrbitKey) : Mask := maskOfCode (representativeCode k)

/-- Every listed representative has its advertised key. -/
theorem orbitKey_representative :
    ∀ k : OrbitKey, orbitKey (representative k) = k := by
  decide

/-- Every core mask is carried to the listed representative with the same key.

This is a tiny kernel-reduced census over the 64 masks and 72 symmetries.  It
contains no solver result or descriptor-model assertion. -/
theorem exists_symmetry_to_representative :
    ∀ B : Mask, ∃ g : CoreSymmetry,
      g • B = representative (orbitKey B) := by
  set_option maxRecDepth 100000 in
    decide

/-- A mask allowed by the ambient incidence lower bound. -/
def Admissible (B : Mask) : Prop := 2 ≤ B.card

instance admissibleDecidable (B : Mask) : Decidable (Admissible B) :=
  by
    change Decidable (2 ≤ B.card)
    infer_instance

/-- The cardinality of a mask is the sum of the entries of its orbit key. -/
theorem card_eq_orbitKey_sum :
    ∀ B : Mask,
      B.card = (orbitKey B).1.1.val + (orbitKey B).1.2.val := by
  decide

/-- There are 64 masks before the ambient exclusion. -/
theorem mask_card : Fintype.card Mask = 64 := by
  decide

/-- There are 57 masks of cardinality at least two. -/
theorem admissibleMask_card :
    Fintype.card {B : Mask // Admissible B} = 57 := by
  set_option maxRecDepth 100000 in
    decide

/-- A predicate on masks is invariant under the two-triple symmetry group. -/
def MaskInvariant (P : Mask → Prop) : Prop :=
  ∀ g : CoreSymmetry, ∀ B : Mask, P (g • B) ↔ P B

/-- An invariant predicate holds on every admissible mask once it holds on the
eight admissible representatives.

The invariance and representative premises remain explicit.  Instantiating
`P` with a semantic no-blocker predicate will require separate definitions and
proofs that transport descriptors and complete certificates. -/
theorem all_admissible_of_representatives
    (P : Mask → Prop)
    (hInvariant : MaskInvariant P)
    (hRepresentative : ∀ k : AdmissibleKey, P (representative k.1)) :
    ∀ B : Mask, Admissible B → P B := by
  intro B hB
  obtain ⟨g, hg⟩ := exists_symmetry_to_representative B
  have hKey : 2 ≤ (orbitKey B).1.1.val + (orbitKey B).1.2.val := by
    rw [← card_eq_orbitKey_sum B]
    exact hB
  have hRep : P (representative (orbitKey B)) :=
    hRepresentative ⟨orbitKey B, hKey⟩
  have hImage : P (g • B) := by simpa [hg] using hRep
  exact (hInvariant g B).mp hImage

end MinSixSymmetry

end TotalColoring
