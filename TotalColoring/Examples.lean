import TotalColoring.Certificate

/-!
# Tiny checked examples

The examples exercise both acceptance and rejection. They are smoke tests, not
bounded-census or unbounded mathematical claims.
-/

namespace TotalColoring.Examples

open TotalColoring.Certificate

/-- The one-vertex graph. -/
abbrev K1 : SimpleGraph (Fin 1) := ⊥

/-- A one-color total coloring of `K1`. -/
def k1Certificate : Assignment K1 (Fin 1) where
  vertexColor _ := 0
  edgeColor _ := 0

theorem k1_checked : checkTotal k1Certificate = true := by
  decide

theorem k1_valid : k1Certificate.Valid :=
  checkTotal_sound k1Certificate k1_checked

/-- The complete graph on two vertices. -/
abbrev K2 : SimpleGraph (Fin 2) := ⊤

/-- A three-color total coloring of `K2`. -/
def k2Certificate : Assignment K2 (Fin 3) where
  vertexColor v := Fin.castLE (by decide : 2 ≤ 3) v
  edgeColor _ := 2

theorem k2_checked : checkTotal k2Certificate = true := by
  decide

theorem k2_valid : k2Certificate.Valid :=
  checkTotal_sound k2Certificate k2_checked

/-- An invalid assignment that gives both adjacent vertices of `K2` color zero. -/
def invalidK2Certificate : Assignment K2 (Fin 3) where
  vertexColor _ := 0
  edgeColor _ := 1

theorem invalidK2_rejected : checkTotal invalidK2Certificate = false := by
  decide

end TotalColoring.Examples
