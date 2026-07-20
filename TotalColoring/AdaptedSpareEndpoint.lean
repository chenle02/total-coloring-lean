import TotalColoring.Graph
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Adapted-spare endpoint coloring

This module isolates the vertex-coloring logic used by the adapted-spare
construction.  Vertices in `A` receive one fresh spare color, vertices in
`B` receive supplied donor labels, and every other vertex receives its
supplied missing old color.

The main theorem is an exact equivalence for this endpoint assignment.  It
does not construct `A`, `B`, a donor matching, donor labels, a proper edge
coloring, or a total coloring.  In particular, it makes no unrestricted total
coloring claim.
-/

namespace TotalColoring

universe u v

section Endpoint

variable {V : Type u} [DecidableEq V]
variable {C : Type v}
variable (K : SimpleGraph V)

/-- Endpoint colors for the adapted-spare construction.  `none` is the one
fresh spare color; `some c` embeds an old color.  Membership in `A` takes
priority, while the intended exact theorem assumes `A` and `B` disjoint. -/
def adaptedSpareVertexColor (A B : Finset V) (missing head : V → C) :
    V → Option C := fun v ↦
  if v ∈ A then none else some (if v ∈ B then head v else missing v)

/-- Every equal-missing conflict has an endpoint in `A ∪ B`. -/
def EqualMissingConflictsCovered (A B : Finset V) (missing : V → C) : Prop :=
  ∀ ⦃v w : V⦄, K.Adj v w → missing v = missing w →
    v ∈ A ∪ B ∨ w ∈ A ∪ B

/-- A donor label at a head differs from the missing color of every unchanged
neighbor. -/
def HeadLabelsClean (A B : Finset V) (missing head : V → C) : Prop :=
  ∀ ⦃b u : V⦄, b ∈ B → u ∉ A → u ∉ B → K.Adj b u →
    head b ≠ missing u

/-- Donor labels properly color the graph induced by the head set. -/
def HeadLabelsProper (B : Finset V) (head : V → C) : Prop :=
  ∀ ⦃b c : V⦄, b ∈ B → c ∈ B → K.Adj b c → head b ≠ head c

/-- The adapted-spare endpoint assignment is proper exactly when the spare
set is independent, the equal-missing conflicts are covered, the head labels
are clean against unchanged neighbors, and adjacent heads have different
labels.

This is the vertex-side exact interface.  The theorem assumes the intended
disjointness of the spare set and head set; it does not assert that the head
labels arise from a physical donor matching. -/
theorem adaptedSpareVertexColor_proper_iff
    (A B : Finset V) (missing head : V → C) (hAB : Disjoint A B) :
    (∀ ⦃v w : V⦄, K.Adj v w →
      adaptedSpareVertexColor A B missing head v ≠
        adaptedSpareVertexColor A B missing head w) ↔
      K.IsIndepSet (A : Set V) ∧
      EqualMissingConflictsCovered K A B missing ∧
      HeadLabelsClean K A B missing head ∧
      HeadLabelsProper K B head := by
  constructor
  · intro hproper
    have hindependent : K.IsIndepSet (A : Set V) := by
      intro v hv w hw hvw hvwAdj
      have hvA : v ∈ A := hv
      have hwA : w ∈ A := hw
      exact hproper hvwAdj (by
        simp [adaptedSpareVertexColor, hvA, hwA])
    have hcovered : EqualMissingConflictsCovered K A B missing := by
      intro v w hvw hmissing
      by_cases hv : v ∈ A ∪ B
      · exact Or.inl hv
      by_cases hw : w ∈ A ∪ B
      · exact Or.inr hw
      have hvA : v ∉ A := fun hvA ↦ hv (Finset.mem_union_left B hvA)
      have hvB : v ∉ B := fun hvB ↦ hv (Finset.mem_union_right A hvB)
      have hwA : w ∉ A := fun hwA ↦ hw (Finset.mem_union_left B hwA)
      have hwB : w ∉ B := fun hwB ↦ hw (Finset.mem_union_right A hwB)
      exfalso
      exact (hproper hvw) (by
        simp [adaptedSpareVertexColor, hvA, hvB, hwA, hwB, hmissing])
    have hclean : HeadLabelsClean K A B missing head := by
      intro b u hbB huA huB hbu
      have hbA : b ∉ A := by
        intro hbA
        exact Finset.disjoint_left.mp hAB hbA hbB
      intro hlabel
      apply hproper hbu
      simp [adaptedSpareVertexColor, hbA, hbB, huA, huB, hlabel]
    have hheads : HeadLabelsProper K B head := by
      intro b c hbB hcB hbc
      have hbA : b ∉ A := by
        intro hbA
        exact Finset.disjoint_left.mp hAB hbA hbB
      have hcA : c ∉ A := by
        intro hcA
        exact Finset.disjoint_left.mp hAB hcA hcB
      intro hlabel
      apply hproper hbc
      simp [adaptedSpareVertexColor, hbA, hbB, hcA, hcB, hlabel]
    exact ⟨hindependent, hcovered, hclean, hheads⟩
  · rintro ⟨hindependent, hcovered, hclean, hheads⟩ v w hvw
    by_cases hvA : v ∈ A
    · by_cases hwA : w ∈ A
      · exact (hindependent hvA hwA hvw.ne hvw).elim
      · simp [adaptedSpareVertexColor, hvA, hwA]
    · by_cases hwA : w ∈ A
      · simp [adaptedSpareVertexColor, hvA, hwA]
      · by_cases hvB : v ∈ B
        · by_cases hwB : w ∈ B
          · have hne := hheads hvB hwB hvw
            simpa [adaptedSpareVertexColor, hvA, hvB, hwA, hwB] using hne
          · have hne := hclean hvB hwA hwB hvw
            simpa [adaptedSpareVertexColor, hvA, hvB, hwA, hwB] using hne
        · by_cases hwB : w ∈ B
          · have hne := hclean hwB hvA hvB hvw.symm
            simpa [adaptedSpareVertexColor, hvA, hvB, hwA, hwB] using hne.symm
          · have hne : missing v ≠ missing w := by
              intro hmissing
              rcases hcovered hvw hmissing with hv | hw
              · exact (Finset.mem_union.mp hv).elim hvA hvB
              · exact (Finset.mem_union.mp hw).elim hwA hwB
            simpa [adaptedSpareVertexColor, hvA, hvB, hwA, hwB] using hne

end Endpoint

end TotalColoring
