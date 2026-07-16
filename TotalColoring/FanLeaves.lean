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

private theorem reflTransGen_of_mem_chain
    {X : Type*} {R : X → X → Prop} (x : X) (xs : List X)
    (hchain : (x :: xs).IsChain R) {y : X} (hy : y ∈ x :: xs) :
    Relation.ReflTransGen R x y := by
  induction xs generalizing x with
  | nil =>
      simp only [List.mem_singleton] at hy
      subst y
      exact Relation.ReflTransGen.refl
  | cons z zs ih =>
      have hparts : R x z ∧ (z :: zs).IsChain R := by
        simpa [List.isChain_cons] using hchain
      rcases List.mem_cons.mp hy with hxy | hyTail
      · subst y
        exact Relation.ReflTransGen.refl
      · exact (Relation.ReflTransGen.single hparts.1).trans
          (ih z hparts.2 hyTail)

/-- Every spoke appearing in a linear fan path is dependency-reachable from
the root spoke.  This strengthens the terminal-only interface without
introducing a maximality assumption. -/
theorem centerReachable_of_mem_spokes
    (F : LinearFanPath a J center) {p : CenterSpoke G center}
    (hp : p ∈ F.spokes) :
    a.CenterReachable J center F.root.leaf p.leaf := by
  have hpLeaf : p.leaf ∈ F.spokes.map CenterSpoke.leaf :=
    List.mem_map.mpr ⟨p, hp, rfl⟩
  change Relation.ReflTransGen (a.CenterDependency J center)
    F.root.leaf p.leaf
  exact reflTransGen_of_mem_chain F.root.leaf
    (F.tail.map CenterSpoke.leaf)
    (by simpa [LinearFanPath.spokes] using F.leaf_chain)
    (by simpa [LinearFanPath.spokes] using hpLeaf)

/-- Finset form of dependency reachability for every selected fan leaf. -/
theorem centerReachable_of_mem_leafFinset [DecidableEq V]
    (F : LinearFanPath a J center) {leaf : V}
    (hleaf : leaf ∈ F.leafFinset) :
    a.CenterReachable J center F.root.leaf leaf := by
  rcases (F.mem_leafFinset_iff leaf).mp hleaf with ⟨p, hp, rfl⟩
  exact F.centerReachable_of_mem_spokes hp

/-- The leaf finset has exactly as many members as the ordered spoke list. -/
theorem card_leafFinset [DecidableEq V]
    (F : LinearFanPath a J center) :
    F.leafFinset.card = F.spokes.length := by
  simpa [leafFinset] using
    List.toFinset_card_of_nodup F.nodup_leaves

end PartialEdgeAssignment.LinearFanPath

end TotalColoring
