import TotalColoring.CriticalState
import Mathlib.Data.Nat.Find

/-!
# Extracting an outside-edge-minimal noncolorable member

This module discharges the finite-minimum step deliberately left explicit in
`CriticalState`.  Starting from any noncolorable member on a fixed finite
vertex type and with a fixed distinguished finset `J`, it minimizes the
natural number `outsideEdgeCount H J` and packages a witness as
`IsOutsideEdgeMinimalNoncolorable`.

The structural class depends on a `DecidableRel H.Adj` instance because its
finite degree and incidence data do.  We therefore use one canonical classical
instance for every graph in the minimization predicate and transport incoming
class-membership proofs across decidability instances only through
`Subsingleton.elim`.  No choice of decision procedure can affect the
proposition proved here.
-/

namespace TotalColoring

universe u

namespace MinimalExtraction

variable {V : Type u} [Fintype V] [DecidableEq V]

/-- Membership in the auxiliary class is independent of the proof-level
choice of adjacency decision procedure. -/
private theorem inAuxiliaryClass_decidableRel_irrel
    (D : ℕ) (H : SimpleGraph V) (J : Finset (Sym2 V))
    (hAdj₁ hAdj₂ : DecidableRel H.Adj)
    (hmember : @InAuxiliaryClass V _ _ D H hAdj₁ J) :
    @InAuxiliaryClass V _ _ D H hAdj₂ J := by
  have hAdj : hAdj₁ = hAdj₂ := Subsingleton.elim _ _
  subst hAdj
  exact hmember

/-- Every noncolorable member on a finite vertex type has a noncolorable
member on the same vertex type and with the same stable distinguished finset
which minimizes the number of edges outside that finset.

The returned structure uses the canonical classical adjacency decision
procedure.  The explicit instance in the statement makes the transport across
the graph-valued existential visible rather than relying on typeclass search
to guess an instance for an as-yet unknown graph.
-/
theorem exists_outsideEdgeMinimalNoncolorable
    (D : ℕ) (H : SimpleGraph V) [hAdjH : DecidableRel H.Adj]
    (J : Finset (Sym2 V))
    (hmember : InAuxiliaryClass D H J)
    (hnoncolorable : ¬HasValidRainbowColoring D H J) :
    ∃ Hmin : SimpleGraph V,
      @IsOutsideEdgeMinimalNoncolorable V _ _ D Hmin
        (Classical.decRel Hmin.Adj) J := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∃ H' : SimpleGraph V,
      @InAuxiliaryClass V _ _ D H' (Classical.decRel H'.Adj) J ∧
      ¬HasValidRainbowColoring D H' J ∧
      outsideEdgeCount H' J = n
  have hmemberCanonical :
      @InAuxiliaryClass V _ _ D H (Classical.decRel H.Adj) J :=
    inAuxiliaryClass_decidableRel_irrel D H J hAdjH
      (Classical.decRel H.Adj) hmember
  have hP : ∃ n, P n := by
    exact ⟨outsideEdgeCount H J, H, hmemberCanonical,
      hnoncolorable, rfl⟩
  let nmin : ℕ := Nat.find hP
  have hspec : P nmin := Nat.find_spec hP
  rcases hspec with
    ⟨Hmin, hmemberMin, hnoncolorableMin, hcountMin⟩
  refine ⟨Hmin, ?_⟩
  letI hAdjMin : DecidableRel Hmin.Adj := Classical.decRel Hmin.Adj
  refine {
    member := hmemberMin
    noncolorable := hnoncolorableMin
    minimal := ?_
  }
  intro H' hAdjH' hmember' hnoncolorable'
  have hmember'Canonical :
      @InAuxiliaryClass V _ _ D H' (Classical.decRel H'.Adj) J :=
    inAuxiliaryClass_decidableRel_irrel D H' J hAdjH'
      (Classical.decRel H'.Adj) hmember'
  have hP' : P (outsideEdgeCount H' J) := by
    exact ⟨H', hmember'Canonical, hnoncolorable', rfl⟩
  rw [hcountMin]
  exact Nat.find_min' hP hP'

end MinimalExtraction

end TotalColoring
