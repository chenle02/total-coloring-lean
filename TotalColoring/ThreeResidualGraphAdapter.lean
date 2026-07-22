import TotalColoring.CenterSpoke
import TotalColoring.ThreeResidualActivation

/-!
# Graph adapter for one-owner residual activation

This module connects a supplied edge-coloured factor system on a finite core
to the abstract one-owner update in `ThreeResidualActivation`.  Each active
label has a supplied owner and, at every core head, a physical spoke carrying
that label.  Eligibility means that the head is adjacent to the owner in the
complement of the factor graph.

The theorem below proves only the exact update identity and the owner-
cleanliness hypothesis required by the abstract escape criterion.  It does not
construct the core, active labels, owners, spokes, an activation that closes,
or a total colouring.
-/

namespace TotalColoring.ThreeResidualGraphAdapter

universe u v

/-- A vertex supplied with a proof that it belongs to the selected core. -/
abbrev CoreVertex {V : Type u} [DecidableEq V] (core : Finset V) :=
  {v : V // v ∈ core}

/-- A colour supplied with a proof that it is an active residual label. -/
abbrev ActiveLabel {C : Type v} [DecidableEq C] (active : Finset C) :=
  {c : C // c ∈ active}

/-- Physical factor data used by the residual adapter.

For every active label and core head, `spoke` records the incident factor edge
and its other endpoint.  The last field anchors the abstract label to the
actual edge colour. -/
structure CompleteCoreFactorData
    {V : Type u} {C : Type v}
    [DecidableEq V] [DecidableEq C]
    (L : SimpleGraph V) (phi : EdgeAssignment L C)
    (core : Finset V) (active : Finset C) where
  owner : ActiveLabel active → V
  spoke : ∀ (_c : ActiveLabel active) (h : CoreVertex core),
    CenterSpoke L h.1
  spoke_color : ∀ c h, phi.color (spoke c h).edge = c.1

namespace CompleteCoreFactorData

variable {V : Type u} {C : Type v}
variable [DecidableEq V] [DecidableEq C]
variable {L : SimpleGraph V} [DecidableRel L.Adj]
variable {phi : EdgeAssignment L C}
variable {core : Finset V} {active : Finset C}

/-- The physical tail of the factor edge carrying `c` at `h`. -/
def mate (D : CompleteCoreFactorData L phi core active)
    (c : ActiveLabel active) (h : CoreVertex core) : V :=
  (D.spoke c h).leaf

/-- A head is eligible for an owner when the corresponding owner--head pair
is an edge of the complement of the factor graph. -/
def eligible (D : CompleteCoreFactorData L phi core active)
    (c : ActiveLabel active) (h : CoreVertex core) : Prop :=
  D.owner c ≠ h.1 ∧ ¬ L.Adj (D.owner c) h.1

/-- Eligibility is constructively decidable from vertex equality and graph
adjacency. -/
instance instDecidableEligible
    (D : CompleteCoreFactorData L phi core active)
    (c : ActiveLabel active) (h : CoreVertex core) :
    Decidable (D.eligible c h) := by
  unfold eligible
  infer_instance

/-- Residual label--tail options before moving an owner.  A physical tail must
avoid every vertex in `avoid`. -/
def base (D : CompleteCoreFactorData L phi core active)
    (avoid : Finset V) (h : CoreVertex core) :
    Finset (ActiveLabel active × V) :=
  ((Finset.univ : Finset (ActiveLabel active)).filter fun c ↦
      D.eligible c h ∧ D.mate c h ∉ avoid).image fun c ↦
    (c, D.mate c h)

/-- Exact residual family after moving the owner of `d`.

Label `d` becomes available at every head.  Other labels retain their old
eligibility, and every surviving physical tail avoids both `avoid` and the
moved owner. -/
def afterOwner (D : CompleteCoreFactorData L phi core active)
    (avoid : Finset V) (d : ActiveLabel active) (h : CoreVertex core) :
    Finset (ActiveLabel active × V) :=
  ((Finset.univ : Finset (ActiveLabel active)).filter fun c ↦
      (c = d ∨ D.eligible c h) ∧
        D.mate c h ∉ avoid ∧ D.mate c h ≠ D.owner d).image fun c ↦
    (c, D.mate c h)

/-- The new `d`-option is usable exactly when its physical tail avoids the
forbidden set and the moved owner. -/
def canAdd (D : CompleteCoreFactorData L phi core active)
    (avoid : Finset V) (d : ActiveLabel active) (h : CoreVertex core) : Prop :=
  D.mate d h ∉ avoid ∧ D.mate d h ≠ D.owner d

/-- `canAdd` is constructively decidable from finset membership and vertex
equality; unlike `eligible` it does not use graph adjacency. -/
instance instDecidableCanAdd
    (D : CompleteCoreFactorData L phi core active)
    (avoid : Finset V) (d : ActiveLabel active) (h : CoreVertex core) :
    Decidable (D.canAdd avoid d h) := by
  unfold canAdd
  infer_instance

private theorem mem_base_iff
    (D : CompleteCoreFactorData L phi core active)
    (avoid : Finset V) (h : CoreVertex core)
    (c : ActiveLabel active) (t : V) :
    (c, t) ∈ D.base avoid h ↔
      D.eligible c h ∧ D.mate c h ∉ avoid ∧ D.mate c h = t := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨c', hc', heq⟩
    have hccond : D.eligible c' h ∧ D.mate c' h ∉ avoid :=
      (Finset.mem_filter.mp hc').2
    have hlabel : c' = c := congrArg Prod.fst heq
    subst c'
    have htail : D.mate c h = t := congrArg Prod.snd heq
    exact ⟨hccond.1, hccond.2, htail⟩
  · rintro ⟨heligible, havoid, htail⟩
    apply Finset.mem_image.mpr
    refine ⟨c, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ c, heligible, havoid⟩
    · exact Prod.ext rfl htail

private theorem mem_afterOwner_iff
    (D : CompleteCoreFactorData L phi core active)
    (avoid : Finset V) (d c : ActiveLabel active)
    (h : CoreVertex core) (t : V) :
    (c, t) ∈ D.afterOwner avoid d h ↔
      (c = d ∨ D.eligible c h) ∧
        D.mate c h ∉ avoid ∧
        D.mate c h ≠ D.owner d ∧
        D.mate c h = t := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨c', hc', heq⟩
    have hccond := (Finset.mem_filter.mp hc').2
    have hlabel : c' = c := congrArg Prod.fst heq
    subst c'
    have htail : D.mate c h = t := congrArg Prod.snd heq
    exact ⟨hccond.1, hccond.2.1, hccond.2.2, htail⟩
  · rintro ⟨havailable, havoid, howner, htail⟩
    apply Finset.mem_image.mpr
    refine ⟨c, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_univ c, havailable, havoid, howner⟩
    · exact Prod.ext rfl htail

omit [DecidableRel L.Adj] in
private theorem mate_ne_owner_of_eligible
    (D : CompleteCoreFactorData L phi core active)
    (d c : ActiveLabel active) (h : CoreVertex core)
    (hh : D.eligible d h) :
    D.mate c h ≠ D.owner d := by
  have hnot : ¬ L.Adj (D.owner d) h.1 := hh.2
  have hadj : L.Adj h.1 (D.mate c h) :=
    (D.spoke c h).adj
  intro heq
  exact hnot (by simpa only [heq] using hadj.symm)

/-- The physical one-owner residual family is exactly the abstract activation,
and every eligible row is clean of old options ending at the moved owner. -/
theorem afterOwner_eq_activate_and_clean
    (D : CompleteCoreFactorData L phi core active)
    (avoid : Finset V) (d : ActiveLabel active) :
    D.afterOwner avoid d =
        ThreeResidualActivation.activate
          (D.base avoid) (D.eligible d) (D.canAdd avoid d)
          d (D.owner d) (D.mate d) ∧
      ThreeResidualActivation.EligibleOwnerClean
        (D.base avoid) (D.eligible d) (D.owner d) := by
  have heq :
      D.afterOwner avoid d =
        ThreeResidualActivation.activate
          (D.base avoid) (D.eligible d) (D.canAdd avoid d)
          d (D.owner d) (D.mate d) := by
    funext h
    apply Finset.ext
    intro p
    rcases p with ⟨c, t⟩
    rw [mem_afterOwner_iff D avoid d c h t]
    rw [ThreeResidualActivation.mem_activate_iff]
    rw [mem_base_iff D avoid h c t]
    constructor
    · rintro ⟨havailable, havoid, howner, htail⟩
      rcases havailable with hcd | heligible
      · subst c
        by_cases hd : D.eligible d h
        · exact Or.inl ⟨⟨hd, havoid, htail⟩, Or.inl hd⟩
        · exact Or.inr ⟨hd, ⟨havoid, howner⟩, by
            apply Prod.ext
            · rfl
            · exact htail.symm⟩
      · have htowner : t ≠ D.owner d := by
          intro ht
          exact howner (htail.trans ht)
        exact Or.inl
          ⟨⟨heligible, havoid, htail⟩, Or.inr htowner⟩
    · intro hp
      rcases hp with hold | hnew
      · rcases hold with ⟨hbase, hsafe⟩
        rcases hbase with ⟨heligible, havoid, htail⟩
        rcases hsafe with hd | htowner
        · exact ⟨Or.inr heligible, havoid,
            mate_ne_owner_of_eligible D d c h hd, htail⟩
        · have howner : D.mate c h ≠ D.owner d := by
            intro hm
            exact htowner (htail.symm.trans hm)
          exact ⟨Or.inr heligible, havoid, howner, htail⟩
      · rcases hnew with ⟨_hd, hcan, hp⟩
        change D.mate d h ∉ avoid ∧ D.mate d h ≠ D.owner d at hcan
        rcases hcan with ⟨havoid, howner⟩
        have hc : c = d := congrArg Prod.fst hp
        have ht : t = D.mate d h := congrArg Prod.snd hp
        subst c
        exact ⟨Or.inl rfl, havoid, howner, ht.symm⟩
  have hclean :
      ThreeResidualActivation.EligibleOwnerClean
        (D.base avoid) (D.eligible d) (D.owner d) := by
    intro h p hh hp
    rcases p with ⟨c, t⟩
    rcases (mem_base_iff D avoid h c t).mp hp with ⟨_, _, htail⟩
    intro ht
    exact mate_ne_owner_of_eligible D d c h hh (htail.trans ht)
  exact ⟨heq, hclean⟩

end CompleteCoreFactorData

end TotalColoring.ThreeResidualGraphAdapter
