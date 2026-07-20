import TotalColoring.MinSixCageModel
import TotalColoring.MinSixSymmetry

/-!
# Minimum-six mask bridge

This module identifies the six-bit `Fin 64` masks used by the semantic cage
model with the `Finset (Fin 6)` masks used by the order-72 symmetry quotient.
It checks the bit, cardinality, admissibility, and eight canonical-
representative interfaces by kernel reduction over these tiny finite types.

It does not transport descriptors or endpoint certificates, relate either
model to a CNF, refute a semantic blocker, or prove a total-colouring theorem.
-/

namespace TotalColoring

namespace MinSixCage.Mask

/-- Interpret a semantic six-bit mask as a symmetry mask. -/
def toSymmetry (B : MinSixCage.Mask) : MinSixSymmetry.Mask :=
  MinSixSymmetry.maskOfCode B.val

/-- The semantic admissibility predicate is decidable on six-bit masks. -/
instance admissibleDecidable (B : MinSixCage.Mask) :
    Decidable B.Admissible := by
  unfold MinSixCage.Mask.Admissible
  infer_instance

/-- Literal canonical-mask membership is decidable. -/
instance canonicalRepresentativeDecidable (B : MinSixCage.Mask) :
    Decidable B.CanonicalRepresentative := by
  unfold MinSixCage.Mask.CanonicalRepresentative
  infer_instance

/-- The semantic division-and-remainder bit convention agrees exactly with
membership in the symmetry mask. -/
theorem bit_iff_mem_toSymmetry :
    ∀ (B : MinSixCage.Mask) (v : MinSixCage.CoreVertex),
      B.bit v ↔ v ∈ B.toSymmetry := by
  decide

/-- Semantic popcount is cardinality of the corresponding symmetry mask. -/
theorem popcount_eq_toSymmetry_card :
    ∀ B : MinSixCage.Mask, B.popcount = B.toSymmetry.card := by
  decide

/-- The two formulations of the ambient at-least-two exclusion agree. -/
theorem admissible_iff_toSymmetry_admissible :
    ∀ B : MinSixCage.Mask,
      B.Admissible ↔ MinSixSymmetry.Admissible B.toSymmetry := by
  decide

/-- No information is lost when a value below `64` is read as its six low
bits. -/
theorem toSymmetry_injective : Function.Injective toSymmetry := by
  decide

end MinSixCage.Mask

namespace MinSixMaskBridge

/-- Every admissible orbit representative code lies in the six-bit range. -/
theorem representativeCode_lt_64 :
    ∀ k : MinSixSymmetry.AdmissibleKey,
      MinSixSymmetry.representativeCode k.1 < 64 := by
  decide

/-- The semantic mask attached to an admissible symmetry key. -/
def canonicalMask (k : MinSixSymmetry.AdmissibleKey) : MinSixCage.Mask :=
  ⟨MinSixSymmetry.representativeCode k.1, representativeCode_lt_64 k⟩

/-- The semantic mask has exactly the representative code assigned to its
symmetry key. -/
theorem canonicalMask_val (k : MinSixSymmetry.AdmissibleKey) :
    (canonicalMask k).val = MinSixSymmetry.representativeCode k.1 :=
  rfl

/-- Converting the semantic canonical mask gives the literal symmetry
representative, not merely another mask in its orbit. -/
theorem canonicalMask_toSymmetry (k : MinSixSymmetry.AdmissibleKey) :
    (canonicalMask k).toSymmetry = MinSixSymmetry.representative k.1 :=
  rfl

/-- Every mask constructed from an admissible symmetry key is one of the
eight literal semantic canonical representatives. -/
theorem canonicalMask_isCanonical :
    ∀ k : MinSixSymmetry.AdmissibleKey,
      (canonicalMask k).CanonicalRepresentative := by
  decide

/-- The map from admissible orbit keys to literal semantic representatives is
injective. -/
theorem canonicalMask_injective : Function.Injective canonicalMask := by
  decide

/-- A semantic mask is one of the eight canonical masks exactly when it is
the canonical mask of an admissible symmetry key. -/
theorem canonicalRepresentative_iff_exists_key :
    ∀ B : MinSixCage.Mask,
      B.CanonicalRepresentative ↔
        ∃ k : MinSixSymmetry.AdmissibleKey, B = canonicalMask k := by
  decide

/-- The admissible key representing a literal canonical semantic mask is
unique. -/
theorem canonicalRepresentative_iff_existsUnique_key
    (B : MinSixCage.Mask) :
    B.CanonicalRepresentative ↔
      ∃! k : MinSixSymmetry.AdmissibleKey, B = canonicalMask k := by
  constructor
  · intro hB
    obtain ⟨k, hk⟩ := (canonicalRepresentative_iff_exists_key B).mp hB
    refine ⟨k, hk, ?_⟩
    intro y hy
    exact canonicalMask_injective (hy.symm.trans hk)
  · rintro ⟨k, hk, _⟩
    rw [hk]
    exact canonicalMask_isCanonical k

/-- Equivalently, the converted mask is literally one of the eight symmetry
representatives, with a unique admissible key. -/
theorem canonicalRepresentative_iff_existsUnique_representative
    (B : MinSixCage.Mask) :
    B.CanonicalRepresentative ↔
      ∃! k : MinSixSymmetry.AdmissibleKey,
        B.toSymmetry = MinSixSymmetry.representative k.1 := by
  constructor
  · intro hB
    obtain ⟨k, hk, hUnique⟩ :=
      (canonicalRepresentative_iff_existsUnique_key B).mp hB
    refine ⟨k, ?_, ?_⟩
    · rw [hk, canonicalMask_toSymmetry]
    · intro y hy
      apply hUnique y
      apply MinSixCage.Mask.toSymmetry_injective
      rw [canonicalMask_toSymmetry]
      exact hy
  · rintro ⟨k, hk, _⟩
    have hEq : B = canonicalMask k := by
      apply MinSixCage.Mask.toSymmetry_injective
      rw [canonicalMask_toSymmetry]
      exact hk
    rw [hEq]
    exact canonicalMask_isCanonical k

/-- The literal semantic canonical representatives are all admissible. -/
theorem canonicalRepresentative_admissible
    {B : MinSixCage.Mask} (hB : B.CanonicalRepresentative) :
    B.Admissible := by
  have hKey := (canonicalRepresentative_iff_existsUnique_key B).mp hB
  obtain ⟨k, hk, _⟩ := hKey
  subst B
  exact (MinSixCage.Mask.admissible_iff_toSymmetry_admissible
    (canonicalMask k)).mpr (by
      rw [canonicalMask_toSymmetry]
      rw [MinSixSymmetry.Admissible, MinSixSymmetry.card_eq_orbitKey_sum,
        MinSixSymmetry.orbitKey_representative]
      exact k.2)

end MinSixMaskBridge

end TotalColoring
