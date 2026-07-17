import TotalColoring.Auxiliary
import TotalColoring.CriticalAllDClosure

/-!
# Conditional transfer from the auxiliary class to total coloring

This module composes the all-parameter auxiliary rainbow-coloring theorem with
the abstract decoding interface.  The composition remains conditional on a
supplied `Auxiliary.Extension` and on the explicit fact that every selector
edge used for a vertex color belongs to the distinguished set.

No concrete equitable partition or pair/singleton auxiliary graph is
constructed here.
-/

namespace TotalColoring.Auxiliary

universe u v w

variable {V : Type u} {W : Type v}
variable {G : SimpleGraph V} {H : SimpleGraph W}

namespace Extension

/-- Rainbowness on the full distinguished set implies selector rainbowness
when every selector edge belongs to that set. -/
theorem rainbow_of_rainbowOn_distinguished
    {C : Type w} (X : Extension G H) (a : EdgeAssignment H C)
    (J : Finset (Sym2 W))
    (hclassEdge : ∀ vertex, X.classEdge vertex ∈ distinguishedEdgeSet H J)
    (hrainbow : a.RainbowOn (distinguishedEdgeSet H J)) :
    a.Rainbow X.classEdge := by
  intro vertex other hne
  exact hrainbow (hclassEdge vertex) (hclassEdge other) hne

/-- A supplied conflict-preserving extension whose selector edges are
distinguished decodes every auxiliary-class member to a valid total coloring
with the auxiliary `D + 2` palette.

This theorem does not construct `X` or prove the selector-membership
hypothesis for an arbitrary input graph. -/
theorem exists_valid_decode_of_inAuxiliaryClass
    [Fintype W] [DecidableEq W]
    (D : ℕ) (X : Extension G H) [DecidableRel H.Adj]
    (J : Finset (Sym2 W))
    (hclassEdge : ∀ vertex, X.classEdge vertex ∈ distinguishedEdgeSet H J)
    (hmember : InAuxiliaryClass D H J) :
    ∃ assignment : Assignment G (ExtensionPalette D), assignment.Valid := by
  rcases MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass
      D H J hmember with ⟨a, hvalid, hrainbow⟩
  exact ⟨X.decode a, X.decode_valid a hvalid
    (X.rainbow_of_rainbowOn_distinguished a J hclassEdge hrainbow)⟩

end Extension

end TotalColoring.Auxiliary
