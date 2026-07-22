import Mathlib

/-!
# Semantic minimum-six active-cage model

This file isolates the finite semantic proposition that the proof-producing
minimum-six search must refute.  It deliberately contains no solver call,
serialized CNF, or computational verdict.  A later encoding module must prove
that every `Blocker` supplies a satisfying assignment of the checked CNF.

The model is the compact active-`K₆` cage interface only.  It is not a
total-colouring theorem and does not cover the non-cage or non-`K₆` branches.
-/

namespace TotalColoring.MinSixCage

/-- The six vertices in the two-triple core. -/
abbrev CoreVertex := Fin 6

/-- An unordered core edge, represented extensionally by its two endpoints. -/
abbrev CoreEdge := Finset CoreVertex

/-- The canonical unordered edge on `u` and `v`. -/
def edge (u v : CoreVertex) : CoreEdge := {u, v}

/-- One active singleton-colour descriptor in the compact cage model. -/
structure Descriptor where
  matching : Finset CoreEdge
  eligible : Finset CoreVertex
  deriving DecidableEq

/-- The core vertices covered by the factor restriction of a descriptor. -/
def Descriptor.covered (d : Descriptor) : Finset CoreVertex :=
  d.matching.biUnion id

/-- A nonempty matching of at most three genuine two-vertex core edges. -/
def ValidCoreMatching (M : Finset CoreEdge) : Prop :=
  M.Nonempty ∧
    (∀ e ∈ M, e.card = 2) ∧
    (∀ e₁ ∈ M, ∀ e₂ ∈ M, e₁ ≠ e₂ → Disjoint e₁ e₂) ∧
    M.card ≤ 3

/-- The exact local validity conditions imposed on a compact descriptor. -/
def Descriptor.Valid (d : Descriptor) : Prop :=
  ValidCoreMatching d.matching ∧
    d.eligible.Nonempty ∧
    d.eligible ⊆ d.covered ∧
    d.eligible.card ≤ 4

/-- A descriptor is nonperfect when its core restriction has fewer than
three edges.  Under `Descriptor.Valid`, this is equivalent to leaving at
least one core vertex uncovered.  In the upstream factor model that vertex
then has an outside mate; that provenance is not part of this finite model. -/
def Descriptor.Nonperfect (d : Descriptor) : Prop :=
  d.matching.card < 3

/-- The descriptor supplies the oriented core donor arc `head → tail`. -/
def Descriptor.GoodArc
    (d : Descriptor) (head tail : CoreVertex) : Prop :=
  head ∈ d.eligible ∧ edge head tail ∈ d.matching

/-- No physical core edge is used by two selected descriptors. -/
def EdgePacked (X : Finset Descriptor) : Prop :=
  ∀ d₁ ∈ X, ∀ d₂ ∈ X, d₁ ≠ d₂ →
    Disjoint d₁.matching d₂.matching

/-- Vertices `0,1,2` form the first shore. -/
def InFirstShore (v : CoreVertex) : Prop :=
  v.val < 3

/-- Vertices `3,4,5` form the second shore. -/
def InSecondShore (v : CoreVertex) : Prop :=
  3 ≤ v.val

/-- The six named role vertices are pairwise distinct and exhaust the core. -/
def RolePartition
    (spare outsideHead unchanged₀ unchanged₁ donorHead₀ donorHead₁ :
      CoreVertex) : Prop :=
  ({spare, outsideHead, unchanged₀, unchanged₁,
      donorHead₀, donorHead₁} : Finset CoreVertex) = Finset.univ

/-- One activated-owner/two-donor endpoint certificate.

`activation` is the descriptor whose owner is activated.  Its eligible
`spare` pays for the activation, while `outsideHead` is uncovered by its core
matching and is therefore served by the activated label.  The other two
heads receive distinct descriptor labels along the two disjoint oriented
donor edges determined by a cross-shore unchanged pair. -/
structure EndpointCertificate where
  activation : Descriptor
  donor₀ : Descriptor
  donor₁ : Descriptor
  spare : CoreVertex
  outsideHead : CoreVertex
  unchanged₀ : CoreVertex
  unchanged₁ : CoreVertex
  donorHead₀ : CoreVertex
  donorHead₁ : CoreVertex

/-- Semantic validity of an endpoint certificate for a selected family. -/
def EndpointCertificate.ValidFor
    (c : EndpointCertificate) (X : Finset Descriptor) : Prop :=
  c.activation ∈ X ∧
    c.donor₀ ∈ X ∧
    c.donor₁ ∈ X ∧
    c.activation ≠ c.donor₀ ∧
    c.activation ≠ c.donor₁ ∧
    c.donor₀ ≠ c.donor₁ ∧
    c.activation.Valid ∧
    c.donor₀.Valid ∧
    c.donor₁.Valid ∧
    c.activation.Nonperfect ∧
    c.spare ∈ c.activation.eligible ∧
    c.outsideHead ∉ c.activation.covered ∧
    InFirstShore c.unchanged₀ ∧
    InSecondShore c.unchanged₁ ∧
    RolePartition c.spare c.outsideHead c.unchanged₀ c.unchanged₁
      c.donorHead₀ c.donorHead₁ ∧
    ((c.donor₀.GoodArc c.donorHead₀ c.unchanged₀ ∧
        c.donor₁.GoodArc c.donorHead₁ c.unchanged₁) ∨
      (c.donor₀.GoodArc c.donorHead₀ c.unchanged₁ ∧
        c.donor₁.GoodArc c.donorHead₁ c.unchanged₀))

/-- The selected descriptors have an activated-owner endpoint. -/
def HasEndpointCertificate (X : Finset Descriptor) : Prop :=
  ∃ c : EndpointCertificate, c.ValidFor X

/-- A six-bit core column mask.  Bit `v` selects column degree four;
otherwise the required degree is three. -/
abbrev Mask := Fin 64

def Mask.bit (B : Mask) (v : CoreVertex) : Prop :=
  B.val / (2 ^ v.val) % 2 = 1

instance Mask.instDecidableBit (B : Mask) (v : CoreVertex) :
    Decidable (B.bit v) := by
  unfold Mask.bit
  infer_instance

def Mask.requiredColumn (B : Mask) (v : CoreVertex) : Nat :=
  if B.bit v then 4 else 3

/-- Number of degree-four columns represented by a mask. -/
def Mask.popcount (B : Mask) : Nat :=
  (Finset.univ.filter B.bit).card

/-- Ambient incidence excludes masks with fewer than two degree-four
columns. -/
def Mask.Admissible (B : Mask) : Prop :=
  2 ≤ B.popcount

/-- The canonical codes used by the checked order-72 symmetry quotient.
External proof generators must use these literal codes or provide a checked
transport from their same-orbit alternatives. -/
def Mask.CanonicalRepresentative (B : Mask) : Prop :=
  B.val = 5 ∨ B.val = 7 ∨ B.val = 9 ∨ B.val = 11 ∨
    B.val = 15 ∨ B.val = 27 ∨ B.val = 31 ∨ B.val = 63

/-- The literal representative codes accepted by the pinned version-one CNF
generator.  Codes `12` and `19` lie in the same respective orbits as the
final quotient's codes `9` and `11`; a checked transport or regenerated CNF is
required before the two predicates may be interchanged. -/
def Mask.GeneratorV1Representative (B : Mask) : Prop :=
  B.val = 5 ∨ B.val = 7 ∨ B.val = 12 ∨ B.val = 19 ∨
    B.val = 15 ∨ B.val = 27 ∨ B.val = 31 ∨ B.val = 63

/-- Number of selected eligibility rows containing a core vertex. -/
def columnCount (X : Finset Descriptor) (v : CoreVertex) : Nat :=
  (X.filter fun d => v ∈ d.eligible).card

/-- The semantic obstruction targeted by the minimum-six guarded CNFs.
A downstream bridge must additionally restrict `B` to the literal generated
representative codes (or supply checked symmetry transport). -/
structure Blocker (B : Mask) (X : Finset Descriptor) : Prop where
  valid : ∀ d ∈ X, d.Valid
  edgePacked : EdgePacked X
  nonperfect : ∃ d ∈ X, d.Nonperfect
  atLeastSix : 6 ≤ X.card
  columns : ∀ v, columnCount X v = B.requiredColumn v
  ambientIncidence : 20 ≤ Finset.univ.sum (fun v => columnCount X v)
  certificateFree : ¬ HasEndpointCertificate X

theorem Blocker.noEndpointCertificate
    {B : Mask} {X : Finset Descriptor} (h : Blocker B X) :
    ¬ HasEndpointCertificate X :=
  h.certificateFree

end TotalColoring.MinSixCage
