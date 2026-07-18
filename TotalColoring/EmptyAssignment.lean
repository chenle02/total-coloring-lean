import TotalColoring.Total

/-!
# Total coloring on an empty vertex type

An empty vertex type has no vertices and no edges, so every color type admits
a vacuously valid total-coloring assignment.
-/

namespace TotalColoring

universe u v

variable {V : Type u} [IsEmpty V]

/-- Every graph on an empty vertex type has a valid total-coloring assignment,
even when the color type is itself empty. -/
theorem exists_valid_assignment_of_isEmpty (G : SimpleGraph V) (C : Type v) :
    ∃ a : Assignment G C, a.Valid := by
  refine ⟨⟨isEmptyElim, isEmptyElim⟩, ?_⟩
  constructor
  · intro v
    exact isEmptyElim v
  constructor
  · intro e
    exact isEmptyElim e
  · intro v
    exact isEmptyElim v

end TotalColoring
