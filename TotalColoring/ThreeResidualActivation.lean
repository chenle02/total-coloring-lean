import Mathlib

/-!
# One-owner activation of three residual option sets

This module isolates the abstract bookkeeping behind a one-owner activation.
Each residual option is a label--tail pair.  Activating label `d` moves its
owner `owner`: an eligible residual row is unchanged, while an ineligible row
loses its old options with tail `owner` and may gain the one new option
`(d, newTail h)`.

The main theorem gives an exact escape criterion.  If the old residual family
does not close, the activated family closes precisely by using one genuinely
new `d`-option together with one surviving old option.  The theorem is
abstract: applying it to the total-colouring argument still requires a
graph-facing proof that the concrete residual sets obey `activate` and
`EligibleOwnerClean`.
-/

namespace TotalColoring.ThreeResidualActivation

variable {Head Label Tail : Type*}
  [DecidableEq Label] [DecidableEq Tail]

/-- Two options can be used together when both their labels and tails differ. -/
def Compatible (p q : Label × Tail) : Prop :=
  p.1 ≠ q.1 ∧ p.2 ≠ q.2

/-- A residual family closes when an eligible spare head leaves two distinct
retained heads carrying compatible options. -/
def Closes
    (P : Head → Finset (Label × Tail)) (eligible : Head → Prop) : Prop :=
  ∃ a h k, a ≠ h ∧ a ≠ k ∧ h ≠ k ∧ eligible a ∧
    ∃ p ∈ P h, ∃ q ∈ P k, Compatible p q

/-- Abstract update performed by moving the owner of label `d`.

Eligible rows are unchanged.  Ineligible rows lose every old point whose tail
is the moved owner and, when `canAdd h` holds, gain the new point with label
`d` and tail `newTail h`. -/
def activate
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail) :
    Head → Finset (Label × Tail) :=
  fun h ↦
    if eligible h then P h
    else
      (P h).filter (fun p ↦ p.2 ≠ owner) ∪
        if canAdd h then {(d, newTail h)} else ∅

/-- The graph-facing cleanliness condition needed by the abstract escape
argument: an eligible row has no old option ending at the moved owner. -/
def EligibleOwnerClean
    (P : Head → Finset (Label × Tail))
    (eligible : Head → Prop) (owner : Tail) : Prop :=
  ∀ ⦃h p⦄, eligible h → p ∈ P h → p.2 ≠ owner

/-- The concrete new--old witness produced by a useful activation. -/
def NewOldEscape
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    (d : Label) (owner : Tail) (newTail : Head → Tail) : Prop :=
  ∃ a h k, a ≠ h ∧ a ≠ k ∧ h ≠ k ∧ eligible a ∧
    ¬ eligible h ∧ canAdd h ∧
      ∃ q ∈ P k,
        q.1 ≠ d ∧ q.2 ≠ owner ∧ q.2 ≠ newTail h

theorem activate_of_eligible
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    {h : Head} (hh : eligible h) :
    activate P eligible canAdd d owner newTail h = P h := by
  simp [activate, hh]

/-- If every retained head is eligible, moving the owner is inert on the
entire residual family. -/
theorem activate_eq_of_all_eligible
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    (hall : ∀ h, eligible h) :
    activate P eligible canAdd d owner newTail = P := by
  funext h
  exact activate_of_eligible P eligible canAdd d owner newTail (hall h)

/-- In particular, an activation eligible at every head creates no new
closing certificate. -/
theorem closes_activate_iff_of_all_eligible
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    (hall : ∀ h, eligible h) :
    Closes (activate P eligible canAdd d owner newTail) eligible ↔
      Closes P eligible := by
  rw [activate_eq_of_all_eligible P eligible canAdd d owner newTail hall]

theorem activate_of_ineligible
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    {h : Head} (hh : ¬ eligible h) :
    activate P eligible canAdd d owner newTail h =
      (P h).filter (fun p ↦ p.2 ≠ owner) ∪
        if canAdd h then {(d, newTail h)} else ∅ := by
  simp [activate, hh]

theorem mem_activate_iff
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    {h : Head} {p : Label × Tail} :
    p ∈ activate P eligible canAdd d owner newTail h ↔
      (p ∈ P h ∧ (eligible h ∨ p.2 ≠ owner)) ∨
        (¬ eligible h ∧ canAdd h ∧ p = (d, newTail h)) := by
  by_cases he : eligible h <;> by_cases hn : canAdd h <;>
    simp [activate, he, hn, or_comm]

theorem new_mem_activate
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    {h : Head} (he : ¬ eligible h) (hn : canAdd h) :
    (d, newTail h) ∈ activate P eligible canAdd d owner newTail h := by
  simp [activate, he, hn]

theorem old_mem_activate_of_tail_ne
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    {h : Head} {p : Label × Tail}
    (hp : p ∈ P h) (htail : p.2 ≠ owner) :
    p ∈ activate P eligible canAdd d owner newTail h := by
  by_cases he : eligible h
  · simpa [activate, he] using hp
  · simp [activate, he, hp, htail]

theorem new_eq_of_mem_activate_not_old
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    {h : Head} {p : Label × Tail}
    (hmem : p ∈ activate P eligible canAdd d owner newTail h)
    (hold : p ∉ P h) :
    ¬ eligible h ∧ canAdd h ∧ p = (d, newTail h) := by
  rcases (mem_activate_iff P eligible canAdd d owner newTail).mp hmem with h | h
  · exact (hold h.1).elim
  · exact h

private theorem old_tail_ne_owner
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    (hclean : EligibleOwnerClean P eligible owner)
    {h : Head} {p : Label × Tail}
    (hmem : p ∈ activate P eligible canAdd d owner newTail h)
    (hold : p ∈ P h) (hlabel : p.1 ≠ d) :
    p.2 ≠ owner := by
  rcases (mem_activate_iff P eligible canAdd d owner newTail).mp hmem with h | h
  · rcases h.2 with he | htail
    · exact hclean he hold
    · exact htail
  · exfalso
    apply hlabel
    simp [h.2.2]

/-- Exact abstract escape criterion for a one-owner activation.

If no eligible spare closes the old residual family, and eligible rows never
use the moved owner as an old tail, then the activated family closes if and
only if one ineligible row contributes its new `d`-option and the other row
contributes a surviving old option with a different label, owner, and new
tail. -/
theorem closes_activate_iff_newOldEscape
    (P : Head → Finset (Label × Tail))
    (eligible canAdd : Head → Prop)
    [DecidablePred eligible] [DecidablePred canAdd]
    (d : Label) (owner : Tail) (newTail : Head → Tail)
    (hclean : EligibleOwnerClean P eligible owner)
    (hno : ¬ Closes P eligible) :
    Closes (activate P eligible canAdd d owner newTail) eligible ↔
      NewOldEscape P eligible canAdd d owner newTail := by
  constructor
  · rintro ⟨a, h, k, hah, hak, hhk, ha, p, hp, q, hq, hpq⟩
    by_cases hpold : p ∈ P h
    · have hqnot : q ∉ P k := by
        intro hqold
        exact hno ⟨a, h, k, hah, hak, hhk, ha,
          p, hpold, q, hqold, hpq⟩
      obtain ⟨hknot, hkadd, rfl⟩ :=
        new_eq_of_mem_activate_not_old P eligible canAdd d owner newTail hq hqnot
      have hptail : p.2 ≠ owner :=
        old_tail_ne_owner P eligible canAdd d owner newTail hclean hp hpold hpq.1
      exact ⟨a, k, h, hak, hah, hhk.symm, ha, hknot, hkadd,
        p, hpold, hpq.1, hptail, hpq.2⟩
    · obtain ⟨hhnot, hhadd, rfl⟩ :=
        new_eq_of_mem_activate_not_old P eligible canAdd d owner newTail hp hpold
      have hqold : q ∈ P k := by
        by_contra hqnot
        obtain ⟨_, _, hqeq⟩ :=
          new_eq_of_mem_activate_not_old P eligible canAdd d owner newTail hq hqnot
        apply hpq.1
        simp [hqeq]
      have hqtail : q.2 ≠ owner :=
        old_tail_ne_owner P eligible canAdd d owner newTail hclean hq hqold
          hpq.1.symm
      exact ⟨a, h, k, hah, hak, hhk, ha, hhnot, hhadd,
        q, hqold, hpq.1.symm, hqtail, hpq.2.symm⟩
  · rintro ⟨a, h, k, hah, hak, hhk, ha, hhnot, hhadd,
      q, hqold, hqlabel, hqowner, hqtail⟩
    refine ⟨a, h, k, hah, hak, hhk, ha,
      (d, newTail h), ?_, q, ?_, ?_⟩
    · exact new_mem_activate P eligible canAdd d owner newTail hhnot hhadd
    · exact old_mem_activate_of_tail_ne P eligible canAdd d owner newTail
        hqold hqowner
    · exact ⟨hqlabel.symm, hqtail.symm⟩

end TotalColoring.ThreeResidualActivation
