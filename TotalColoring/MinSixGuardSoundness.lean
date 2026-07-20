import TotalColoring.MinSixCageModel

/-!
# Soundness of the guarded endpoint-role clause

The compressed finite CNF shares Boolean guards for activation and donor
families.  This file proves the semantic heart of that compression: if all
three negative families meet a selected blocker and their selected donor
intersection is empty, the three chosen descriptors form an endpoint
certificate.  The theorem is independent of any descriptor enumeration or
serialized CNF.
-/

namespace TotalColoring.MinSixCage

/-- One of the two oriented donor layouts associated with an activation
matching, a spare, an outside head, and an unchanged cross-shore pair. -/
structure StructuredRole where
  activationMatching : Finset CoreEdge
  spare : CoreVertex
  outsideHead : CoreVertex
  unchanged₀ : CoreVertex
  unchanged₁ : CoreVertex
  donorHead₀ : CoreVertex
  donorHead₁ : CoreVertex
  swapped : Bool

def StructuredRole.donorTail₀ (r : StructuredRole) : CoreVertex :=
  match r.swapped with
  | false => r.unchanged₀
  | true => r.unchanged₁

def StructuredRole.donorTail₁ (r : StructuredRole) : CoreVertex :=
  match r.swapped with
  | false => r.unchanged₁
  | true => r.unchanged₀

/-- Exchange the two donor families while preserving the underlying endpoint
role.  The generator performs exactly this operation when it sorts the two
donor-family index sets. -/
def StructuredRole.flip (r : StructuredRole) : StructuredRole :=
  { r with
    donorHead₀ := r.donorHead₁
    donorHead₁ := r.donorHead₀
    swapped := !r.swapped }

@[simp] theorem StructuredRole.flip_donorTail₀ (r : StructuredRole) :
    r.flip.donorTail₀ = r.donorTail₁ := by
  cases h : r.swapped <;>
    simp [StructuredRole.flip, StructuredRole.donorTail₀,
      StructuredRole.donorTail₁, h]

@[simp] theorem StructuredRole.flip_donorTail₁ (r : StructuredRole) :
    r.flip.donorTail₁ = r.donorTail₀ := by
  cases h : r.swapped <;>
    simp [StructuredRole.flip, StructuredRole.donorTail₀,
      StructuredRole.donorTail₁, h]

/-- Conditions guaranteed by the finite structured-role enumeration. -/
structure StructuredRole.Valid (r : StructuredRole) : Prop where
  activationValid : ValidCoreMatching r.activationMatching
  activationNonperfect : r.activationMatching.card < 3
  spareCovered : r.spare ∈ r.activationMatching.biUnion id
  outsideHead : r.outsideHead ∉ r.activationMatching.biUnion id
  unchanged₀_shore : InFirstShore r.unchanged₀
  unchanged₁_shore : InSecondShore r.unchanged₁
  partition : RolePartition r.spare r.outsideHead r.unchanged₀ r.unchanged₁
    r.donorHead₀ r.donorHead₁

/-- Swapping the donor-family order preserves role validity. -/
theorem StructuredRole.Valid.flip {r : StructuredRole} (hr : r.Valid) :
    r.flip.Valid := by
  refine ⟨hr.activationValid, hr.activationNonperfect, hr.spareCovered,
    hr.outsideHead, hr.unchanged₀_shore, hr.unchanged₁_shore, ?_⟩
  have hp := hr.partition
  unfold RolePartition at hp ⊢
  ext v
  have hv := Finset.ext_iff.mp hp v
  simpa [StructuredRole.flip, or_comm, or_left_comm, or_assoc] using hv

/-- The activation guard family for a role. -/
def StructuredRole.Activates (r : StructuredRole) (d : Descriptor) : Prop :=
  d.matching = r.activationMatching ∧ r.spare ∈ d.eligible

@[simp] theorem StructuredRole.flip_activates_iff
    (r : StructuredRole) (d : Descriptor) :
    r.flip.Activates d ↔ r.Activates d := by
  rfl

/-- The first donor guard family, after filtering against the activation
matching. -/
def StructuredRole.FirstDonor (r : StructuredRole) (d : Descriptor) : Prop :=
  Disjoint d.matching r.activationMatching ∧
    d.GoodArc r.donorHead₀ r.donorTail₀

/-- The second donor guard family, after filtering against the activation
matching. -/
def StructuredRole.SecondDonor (r : StructuredRole) (d : Descriptor) : Prop :=
  Disjoint d.matching r.activationMatching ∧
    d.GoodArc r.donorHead₁ r.donorTail₁

@[simp] theorem StructuredRole.flip_firstDonor_iff
    (r : StructuredRole) (d : Descriptor) :
    r.flip.FirstDonor d ↔ r.SecondDonor d := by
  cases h : r.swapped <;>
    simp [StructuredRole.FirstDonor, StructuredRole.SecondDonor,
      StructuredRole.flip, StructuredRole.donorTail₀,
      StructuredRole.donorTail₁, h]

@[simp] theorem StructuredRole.flip_secondDonor_iff
    (r : StructuredRole) (d : Descriptor) :
    r.flip.SecondDonor d ↔ r.FirstDonor d := by
  cases h : r.swapped <;>
    simp [StructuredRole.FirstDonor, StructuredRole.SecondDonor,
      StructuredRole.flip, StructuredRole.donorTail₀,
      StructuredRole.donorTail₁, h]

@[simp] theorem StructuredRole.flip_donorIntersection_iff
    (r : StructuredRole) (d : Descriptor) :
    (r.flip.FirstDonor d ∧ r.flip.SecondDonor d) ↔
      (r.FirstDonor d ∧ r.SecondDonor d) := by
  simp [and_comm]

/-- Failure of one guarded role clause produces a semantic endpoint
certificate.  This is the key implication used by the future
`blocker_implies_cnf_sat` theorem. -/
theorem endpoint_of_guard_failure
    {X : Finset Descriptor}
    (hvalid : ∀ d ∈ X, d.Valid)
    (r : StructuredRole) (hr : r.Valid)
    {activation donor₀ donor₁ : Descriptor}
    (hactivationX : activation ∈ X)
    (hdonor₀X : donor₀ ∈ X)
    (hdonor₁X : donor₁ ∈ X)
    (hactivation : r.Activates activation)
    (hdonor₀ : r.FirstDonor donor₀)
    (hdonor₁ : r.SecondDonor donor₁)
    (hintersection : ¬ ∃ d ∈ X, r.FirstDonor d ∧ r.SecondDonor d) :
    HasEndpointCertificate X := by
  rcases hactivation with ⟨hmatching, hspare⟩
  rcases hdonor₀ with ⟨hdisjoint₀, harc₀⟩
  rcases hdonor₁ with ⟨hdisjoint₁, harc₁⟩
  have hactivation_ne_donor₀ : activation ≠ donor₀ := by
    intro h
    subst donor₀
    rw [hmatching] at hdisjoint₀
    rcases hr.activationValid.1 with ⟨e, he⟩
    exact Finset.disjoint_left.mp hdisjoint₀ he he
  have hactivation_ne_donor₁ : activation ≠ donor₁ := by
    intro h
    subst donor₁
    rw [hmatching] at hdisjoint₁
    rcases hr.activationValid.1 with ⟨e, he⟩
    exact Finset.disjoint_left.mp hdisjoint₁ he he
  have hdonors_ne : donor₀ ≠ donor₁ := by
    intro h
    subst donor₁
    exact hintersection ⟨donor₀, hdonor₀X,
      ⟨⟨hdisjoint₀, harc₀⟩, ⟨hdisjoint₁, harc₁⟩⟩⟩
  refine ⟨{
    activation := activation
    donor₀ := donor₀
    donor₁ := donor₁
    spare := r.spare
    outsideHead := r.outsideHead
    unchanged₀ := r.unchanged₀
    unchanged₁ := r.unchanged₁
    donorHead₀ := r.donorHead₀
    donorHead₁ := r.donorHead₁
  }, ?_⟩
  refine ⟨hactivationX, hdonor₀X, hdonor₁X,
    hactivation_ne_donor₀, hactivation_ne_donor₁, hdonors_ne,
    hvalid activation hactivationX, hvalid donor₀ hdonor₀X,
    hvalid donor₁ hdonor₁X, ?_, hspare, ?_, hr.unchanged₀_shore,
    hr.unchanged₁_shore, hr.partition, ?_⟩
  · simpa [Descriptor.Nonperfect, hmatching] using hr.activationNonperfect
  · simpa [Descriptor.covered, hmatching] using hr.outsideHead
  · cases hswap : r.swapped with
    | false =>
        left
        simpa [StructuredRole.donorTail₀, StructuredRole.donorTail₁, hswap]
          using And.intro harc₀ harc₁
    | true =>
        right
        simpa [StructuredRole.donorTail₀, StructuredRole.donorTail₁, hswap]
          using And.intro harc₀ harc₁

/-- A certificate-free selection satisfies the abstract guarded role clause:
if the activation and both donor families are selected, then a selected
descriptor lies in the donor-family intersection. -/
theorem guarded_role_clause
    {X : Finset Descriptor}
    (hvalid : ∀ d ∈ X, d.Valid)
    (hfree : ¬ HasEndpointCertificate X)
    (r : StructuredRole) (hr : r.Valid) :
    (∃ activation ∈ X, r.Activates activation) →
      (∃ donor₀ ∈ X, r.FirstDonor donor₀) →
      (∃ donor₁ ∈ X, r.SecondDonor donor₁) →
      ∃ d ∈ X, r.FirstDonor d ∧ r.SecondDonor d := by
  rintro ⟨activation, hactivationX, hactivation⟩
    ⟨donor₀, hdonor₀X, hdonor₀⟩
    ⟨donor₁, hdonor₁X, hdonor₁⟩
  by_contra hintersection
  exact hfree <| endpoint_of_guard_failure hvalid r hr
    hactivationX hdonor₀X hdonor₁X hactivation hdonor₀ hdonor₁
    hintersection

end TotalColoring.MinSixCage
