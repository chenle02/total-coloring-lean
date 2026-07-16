import TotalColoring.OrderedFan
import Mathlib.Data.Finset.Card

/-!
# Finite leaf sets of ordered fans

This module exposes the duplicate-free leaf list of a `LinearFanPath` as a
finset for later missing-incidence counts.  It contains no maximality or
multiplicity assertion.
-/

namespace TotalColoring

universe u v

namespace PartialEdgeAssignment.LinearFanPath

variable {V : Type u} {G : SimpleGraph V} {C : Type v}
variable {a : PartialEdgeAssignment G C} {J : Set G.edgeSet} {center : V}

/-- Distinct fan spokes have distinct declared leaves. -/
theorem nodup_leaves [DecidableEq V] (F : LinearFanPath a J center) :
    (F.spokes.map CenterSpoke.leaf).Nodup := by
  apply List.Nodup.map
  · intro p q hpq
    exact CenterSpoke.ext hpq
  · exact F.nodup_spokes

/-- The finite set of leaves appearing on a linear fan path. -/
def leafFinset [DecidableEq V] (F : LinearFanPath a J center) : Finset V :=
  (F.spokes.map CenterSpoke.leaf).toFinset

@[simp]
theorem mem_leafFinset_iff [DecidableEq V]
    (F : LinearFanPath a J center) (v : V) :
    v ∈ F.leafFinset ↔ ∃ p ∈ F.spokes, p.leaf = v := by
  simp [leafFinset]

@[simp]
theorem root_leaf_mem_leafFinset [DecidableEq V]
    (F : LinearFanPath a J center) : F.root.leaf ∈ F.leafFinset := by
  exact (mem_leafFinset_iff F F.root.leaf).2
    ⟨F.root, F.root_mem_spokes, rfl⟩

@[simp]
theorem terminal_leaf_mem_leafFinset [DecidableEq V]
    (F : LinearFanPath a J center) : F.terminal.leaf ∈ F.leafFinset := by
  exact (mem_leafFinset_iff F F.terminal.leaf).2
    ⟨F.terminal, F.terminal_mem_spokes, rfl⟩

/-- The leaf finset has exactly as many members as the ordered spoke list. -/
theorem card_leafFinset [DecidableEq V]
    (F : LinearFanPath a J center) :
    F.leafFinset.card = F.spokes.length := by
  simpa [leafFinset] using
    List.toFinset_card_of_nodup F.nodup_leaves

end PartialEdgeAssignment.LinearFanPath

end TotalColoring
