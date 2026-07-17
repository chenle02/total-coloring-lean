import Mathlib.Data.Finset.Card
import Mathlib.Logic.Relation

/-!
# Directed dominator regions

This module isolates the graph-theoretic core of the direct-entry argument.
For a relation `R`, a root `r`, and a prospective dominator `q`, the
`dominatorRegion` consists of the nonroot vertices which cannot be reached
from `r` while avoiding `q`.

The final lemmas model deleting a chosen set of entries into `q`.  One
surviving source outside the dominator region is enough to retain `q`, and
then every vertex which was reachable before the deletion is still
reachable.  No coloring, finiteness, or maximality hypothesis is used here.
-/

namespace TotalColoring

namespace DirectedDominator

universe u

variable {V : Type u}

/-- The edge relation obtained by forbidding the vertex `q` at both ends. -/
def Avoiding (R : V → V → Prop) (q : V) : V → V → Prop :=
  fun source target => R source target ∧ source ≠ q ∧ target ≠ q

/-- Reachability from `root` to `target` along a path which avoids `q`. -/
def AvoidReach (R : V → V → Prop) (root q target : V) : Prop :=
  Relation.ReflTransGen (Avoiding R q) root target

/-- The `q`-dominator region relative to `root`.  The root is excluded
literally, matching the region used by the direct-entry proof. -/
def DominatorRegion (R : V → V → Prop) (root q : V) : Set V :=
  {target | target ≠ root ∧ ¬AvoidReach R root q target}

/-- Delete precisely the selected source entries whose target is `q`. -/
def DeleteEntries (R : V → V → Prop) (q : V) (deleted : Set V) :
    V → V → Prop :=
  fun source target => R source target ∧ ¬(source ∈ deleted ∧ target = q)

/-- The supplied predecessors which lie outside the dominator region. -/
noncomputable def externalSources
    (R : V → V → Prop) (root q : V) (sources : Finset V) : Finset V := by
  classical
  exact sources.filter fun source => source ∉ DominatorRegion R root q

/-- Robustness against deletion of at most `budget` selected entries into
`q`: every vertex reachable in the original relation remains reachable. -/
def EntryRobust [DecidableEq V]
    (R : V → V → Prop) (root q : V) (sources : Finset V)
    (budget : ℕ) : Prop :=
  ∀ deleted : Finset V, deleted ⊆ sources → deleted.card ≤ budget →
    ∀ target : V, Relation.ReflTransGen R root target →
      Relation.ReflTransGen
        (DeleteEntries R q (deleted : Set V)) root target

@[simp]
theorem mem_externalSources_iff
    {R : V → V → Prop} {root q source : V} {sources : Finset V} :
    source ∈ externalSources R root q sources ↔
      source ∈ sources ∧ source ∉ DominatorRegion R root q := by
  classical
  simp [externalSources]

@[simp]
theorem root_not_mem_dominatorRegion (R : V → V → Prop) (root q : V) :
    root ∉ DominatorRegion R root q := by
  intro hroot
  exact hroot.1 rfl

/-- An avoiding path starting away from `q` also ends away from `q`. -/
theorem ne_target_of_avoidReach
    {R : V → V → Prop} {root q target : V}
    (hroot : root ≠ q) (hreach : AvoidReach R root q target) :
    target ≠ q := by
  induction hreach with
  | refl => exact hroot
  | @tail source target hprefix hstep ih =>
      exact hstep.2.2

/-- Every ordinary reachable target is either reachable while avoiding `q`,
or is reachable from `q`. -/
theorem avoidReach_or_reachable_from
    {R : V → V → Prop} {root q target : V}
    (hroot : root ≠ q)
    (hreach : Relation.ReflTransGen R root target) :
    AvoidReach R root q target ∨ Relation.ReflTransGen R q target := by
  induction hreach with
  | refl =>
      exact Or.inl Relation.ReflTransGen.refl
  | @tail source target hprefix hstep ih =>
      rcases ih with havoid | hfromQ
      · by_cases htarget : target = q
        · subst target
          exact Or.inr Relation.ReflTransGen.refl
        · left
          exact Relation.ReflTransGen.tail havoid
            ⟨hstep, ne_target_of_avoidReach hroot havoid, htarget⟩
      · exact Or.inr (Relation.ReflTransGen.tail hfromQ hstep)

/-- The prospective dominator belongs to its own region when it differs from
the root. -/
theorem target_mem_dominatorRegion
    {R : V → V → Prop} {root q : V} (hroot : root ≠ q) :
    q ∈ DominatorRegion R root q := by
  refine ⟨hroot.symm, ?_⟩
  intro havoid
  exact (ne_target_of_avoidReach hroot havoid) rfl

/-- A reachable member of the dominator region is reachable from the
dominator itself. -/
theorem reachable_from_of_mem_dominatorRegion
    {R : V → V → Prop} {root q target : V}
    (hroot : root ≠ q)
    (hreach : Relation.ReflTransGen R root target)
    (hdom : target ∈ DominatorRegion R root q) :
    Relation.ReflTransGen R q target := by
  rcases avoidReach_or_reachable_from hroot hreach with havoid | hfromQ
  · exact (hdom.2 havoid).elim
  · exact hfromQ

/-- Outside the dominator region, a nonroot vertex has a `q`-avoiding
rooted path. -/
theorem avoidReach_of_not_mem_dominatorRegion
    {R : V → V → Prop} {root q target : V}
    (htarget : target ≠ root)
    (houtside : target ∉ DominatorRegion R root q) :
    AvoidReach R root q target := by
  classical
  exact Classical.byContradiction fun havoid =>
    houtside ⟨htarget, havoid⟩

/-- No edge can enter the strict interior of a dominator region from outside
that region. -/
theorem no_entry_to_dominatorRegion_of_ne_target
    {R : V → V → Prop} {root q source target : V}
    (hroot : root ≠ q)
    (hsource : source ∉ DominatorRegion R root q)
    (htarget : target ∈ DominatorRegion R root q)
    (htargetQ : target ≠ q)
    (hedge : R source target) : False := by
  have hsourceAvoid : AvoidReach R root q source := by
    by_cases hsourceRoot : source = root
    · subst source
      exact Relation.ReflTransGen.refl
    · exact avoidReach_of_not_mem_dominatorRegion hsourceRoot hsource
  have hsourceQ : source ≠ q :=
    ne_target_of_avoidReach hroot hsourceAvoid
  have htargetAvoid : AvoidReach R root q target :=
    Relation.ReflTransGen.tail hsourceAvoid
      ⟨hedge, hsourceQ, htargetQ⟩
  exact htarget.2 htargetAvoid

/-- A relation with entries deleted is a subrelation of the original one. -/
theorem deleteEntries_le
    (R : V → V → Prop) (q : V) (deleted : Set V) :
    DeleteEntries R q deleted ≤ R := by
  intro source target hstep
  exact hstep.1

/-- A path starting at `q` remains after deleting arbitrary later entries
into `q`: whenever an old path re-enters `q`, discard the preceding loop. -/
theorem reachable_from_target_deleteEntries
    {R : V → V → Prop} {q target : V} {deleted : Set V}
    (hreach : Relation.ReflTransGen R q target) :
    Relation.ReflTransGen (DeleteEntries R q deleted) q target := by
  induction hreach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail source target hprefix hstep ih =>
      by_cases htarget : target = q
      · subst target
        exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.tail ih
          ⟨hstep, by
            rintro ⟨_, htargetQ⟩
            exact htarget htargetQ⟩

/-- A path avoiding `q` survives every deletion of entries into `q`. -/
theorem avoidReach_deleteEntries
    {R : V → V → Prop} {root q target : V} {deleted : Set V}
    (hreach : AvoidReach R root q target) :
    Relation.ReflTransGen (DeleteEntries R q deleted) root target := by
  exact Relation.ReflTransGen.mono (r := Avoiding R q)
    (p := DeleteEntries R q deleted) (fun source target hstep =>
      ⟨hstep.1, by
        rintro ⟨_, htarget⟩
        exact hstep.2.2 htarget⟩) root target hreach

/-- One undeleted entry from outside the dominator region keeps `q`
reachable after the selected entries are removed. -/
theorem target_reachable_deleteEntries_of_external_source
    {R : V → V → Prop} {root q source : V} {deleted : Set V}
    (_hroot : root ≠ q)
    (hsource : source ∉ DominatorRegion R root q)
    (hsourceDeleted : source ∉ deleted)
    (hedge : R source q) :
    Relation.ReflTransGen (DeleteEntries R q deleted) root q := by
  have hsourceAvoid : AvoidReach R root q source := by
    by_cases hsourceRoot : source = root
    · subst source
      exact Relation.ReflTransGen.refl
    · exact avoidReach_of_not_mem_dominatorRegion hsourceRoot hsource
  have hprefix :=
    avoidReach_deleteEntries (deleted := deleted) hsourceAvoid
  exact Relation.ReflTransGen.tail hprefix
    ⟨hedge, by
      rintro ⟨hsourceMem, _⟩
      exact hsourceDeleted hsourceMem⟩

/-- Once `q` survives a deletion of entries into it, every vertex that was
reachable before the deletion is still reachable. -/
theorem reachable_deleteEntries_of_target_reachable
    {R : V → V → Prop} {root q target : V} {deleted : Set V}
    (hroot : root ≠ q)
    (hqReach :
      Relation.ReflTransGen (DeleteEntries R q deleted) root q)
    (htargetReach : Relation.ReflTransGen R root target) :
    Relation.ReflTransGen (DeleteEntries R q deleted) root target := by
  by_cases hdom : target ∈ DominatorRegion R root q
  · have hfromQ : Relation.ReflTransGen R q target :=
      reachable_from_of_mem_dominatorRegion hroot htargetReach hdom
    exact hqReach.trans (reachable_from_target_deleteEntries hfromQ)
  · by_cases htargetRoot : target = root
    · subst target
      exact Relation.ReflTransGen.refl
    · exact avoidReach_deleteEntries
        (avoidReach_of_not_mem_dominatorRegion htargetRoot hdom)

/-- Combined robust-entry form: one undeleted external predecessor of `q`
preserves every old rooted-reachable vertex. -/
theorem reachable_deleteEntries_of_external_source
    {R : V → V → Prop} {root q source target : V} {deleted : Set V}
    (hroot : root ≠ q)
    (hsource : source ∉ DominatorRegion R root q)
    (hsourceDeleted : source ∉ deleted)
    (hedge : R source q)
    (htargetReach : Relation.ReflTransGen R root target) :
    Relation.ReflTransGen (DeleteEntries R q deleted) root target := by
  exact reachable_deleteEntries_of_target_reachable hroot
    (target_reachable_deleteEntries_of_external_source
      hroot hsource hsourceDeleted hedge)
    htargetReach

/-- If fewer sources are deleted than there are external sources, one
external source survives. -/
theorem exists_externalSource_not_mem_of_card_lt
    [DecidableEq V]
    {R : V → V → Prop} {root q : V}
    (sources deleted : Finset V)
    (hcard : deleted.card < (externalSources R root q sources).card) :
    ∃ source ∈ sources,
      source ∉ DominatorRegion R root q ∧ source ∉ deleted := by
  classical
  have hnotSubset : ¬externalSources R root q sources ⊆ deleted := by
    intro hsubset
    have hle := Finset.card_le_card hsubset
    exact (Nat.not_lt_of_ge hle) hcard
  rcases Finset.not_subset.mp hnotSubset with
    ⟨source, hsourceExternal, hsourceDeleted⟩
  exact ⟨source, (mem_externalSources_iff.mp hsourceExternal).1,
    (mem_externalSources_iff.mp hsourceExternal).2, hsourceDeleted⟩

/-- Finite robust-entry form.  Deleting fewer entries than the number of
external supplied predecessors preserves every old rooted-reachable vertex. -/
theorem reachable_deleteEntries_of_card_lt_externalSources
    [DecidableEq V]
    {R : V → V → Prop} {root q target : V}
    (sources deleted : Finset V)
    (hroot : root ≠ q)
    (hcard : deleted.card < (externalSources R root q sources).card)
    (hentries : ∀ source ∈ sources, R source q)
    (htargetReach : Relation.ReflTransGen R root target) :
    Relation.ReflTransGen
      (DeleteEntries R q (deleted : Set V)) root target := by
  rcases exists_externalSource_not_mem_of_card_lt
      (R := R) (root := root) (q := q) sources deleted hcard with
    ⟨source, hsource, hsourceExternal, hsourceDeleted⟩
  exact reachable_deleteEntries_of_external_source hroot hsourceExternal
    hsourceDeleted (hentries source hsource) htargetReach

/-- If every entry into `q` from outside its dominator region is deleted,
every vertex still reachable from the root remains outside the region. -/
theorem not_mem_dominatorRegion_of_reachable_deleteExternalEntries
    {R : V → V → Prop} {root q target : V}
    (hroot : root ≠ q)
    (hreach : Relation.ReflTransGen
      (DeleteEntries R q (DominatorRegion R root q)ᶜ) root target) :
    target ∉ DominatorRegion R root q := by
  induction hreach with
  | refl => exact root_not_mem_dominatorRegion R root q
  | @tail source target hprefix hstep ih =>
      intro htarget
      by_cases htargetQ : target = q
      · exact hstep.2 ⟨ih, htargetQ⟩
      · exact no_entry_to_dominatorRegion_of_ne_target hroot ih htarget
          htargetQ hstep.1

/-- Deleting all external entries into `q` makes `q` unreachable.  This is
the converse cut statement paired with the surviving-external-entry theorem. -/
theorem target_not_reachable_deleteExternalEntries
    {R : V → V → Prop} {root q : V} (hroot : root ≠ q) :
    ¬Relation.ReflTransGen
      (DeleteEntries R q (DominatorRegion R root q)ᶜ) root q := by
  intro hreach
  exact (not_mem_dominatorRegion_of_reachable_deleteExternalEntries
    hroot hreach) (target_mem_dominatorRegion hroot)

/-- The finite version of deleting all external supplied entries.  The
completeness hypothesis says that `sources` contains every predecessor of
`q`; this is automatic for a dependency color column. -/
theorem target_not_reachable_deleteExternalSources
    [DecidableEq V]
    {R : V → V → Prop} {root q : V} (sources : Finset V)
    (hroot : root ≠ q)
    (hcomplete : ∀ source : V,
      Relation.ReflTransGen R root source → R source q →
        source ∈ sources) :
    ¬Relation.ReflTransGen
      (DeleteEntries R q
        (externalSources R root q sources : Set V)) root q := by
  intro hreach
  have houtside : ∀ {target : V},
      Relation.ReflTransGen
        (DeleteEntries R q
          (externalSources R root q sources : Set V)) root target →
      target ∉ DominatorRegion R root q := by
    intro target htargetReach
    induction htargetReach with
    | refl => exact root_not_mem_dominatorRegion R root q
    | @tail source target hprefix hstep ih =>
        intro htarget
        by_cases htargetQ : target = q
        · subst target
          apply hstep.2
          refine ⟨?_, rfl⟩
          have hsourceOld : Relation.ReflTransGen R root source :=
            Relation.ReflTransGen.mono
              (deleteEntries_le R q
                (externalSources R root q sources : Set V))
              root source hprefix
          exact mem_externalSources_iff.mpr
            ⟨hcomplete source hsourceOld hstep.1, ih⟩
        · exact no_entry_to_dominatorRegion_of_ne_target hroot ih htarget
            htargetQ hstep.1
  exact (houtside hreach) (target_mem_dominatorRegion hroot)

/-- More external sources than the deletion budget imply entry robustness. -/
theorem entryRobust_of_lt_card_externalSources
    [DecidableEq V]
    {R : V → V → Prop} {root q : V} {sources : Finset V} {budget : ℕ}
    (hroot : root ≠ q)
    (hcard : budget < (externalSources R root q sources).card)
    (hentries : ∀ source ∈ sources, R source q) :
    EntryRobust R root q sources budget := by
  intro deleted _hdeletedSubset hdeletedCard target htargetReach
  exact reachable_deleteEntries_of_card_lt_externalSources sources deleted
    hroot (Nat.lt_of_le_of_lt hdeletedCard hcard) hentries htargetReach

/-- If all predecessors are listed and `q` is initially reachable, entry
robustness forces the external-source count to exceed the deletion budget. -/
theorem lt_card_externalSources_of_entryRobust
    [DecidableEq V]
    {R : V → V → Prop} {root q : V} {sources : Finset V} {budget : ℕ}
    (hroot : root ≠ q)
    (hqReach : Relation.ReflTransGen R root q)
    (hcomplete : ∀ source : V,
      Relation.ReflTransGen R root source → R source q →
        source ∈ sources)
    (hrobust : EntryRobust R root q sources budget) :
    budget < (externalSources R root q sources).card := by
  classical
  by_cases hcard : budget < (externalSources R root q sources).card
  · exact hcard
  · have hle : (externalSources R root q sources).card ≤ budget :=
      Nat.le_of_not_gt hcard
    have hsubset : externalSources R root q sources ⊆ sources := by
      intro source hsource
      exact (mem_externalSources_iff.mp hsource).1
    have hsurvives := hrobust (externalSources R root q sources)
      hsubset hle q hqReach
    exact ((target_not_reachable_deleteExternalSources sources hroot hcomplete)
      hsurvives).elim

/-- Exact finite robust-entry characterization. -/
theorem entryRobust_iff_lt_card_externalSources
    [DecidableEq V]
    {R : V → V → Prop} {root q : V} {sources : Finset V} {budget : ℕ}
    (hroot : root ≠ q)
    (hqReach : Relation.ReflTransGen R root q)
    (hentries : ∀ source ∈ sources, R source q)
    (hcomplete : ∀ source : V,
      Relation.ReflTransGen R root source → R source q →
        source ∈ sources) :
    EntryRobust R root q sources budget ↔
      budget < (externalSources R root q sources).card := by
  constructor
  · exact lt_card_externalSources_of_entryRobust hroot hqReach hcomplete
  · intro hcard
    exact entryRobust_of_lt_card_externalSources hroot hcard hentries

end DirectedDominator

end TotalColoring
