import Mathlib.Data.List.Chain
import Mathlib.Data.List.Nodup

/-!
# Simple witnesses for reflexive-transitive reachability

This module turns an abstract reflexive-transitive reachability proof into a
finite directed path with no repeated vertices.  The construction removes a
loop as soon as a new endpoint has already appeared: it truncates the current
simple path at that occurrence instead of appending the endpoint again.

Only decidable equality on the carrier is needed.  In particular, neither a
finite carrier nor a decidable relation is required.
-/

namespace TotalColoring

namespace SimpleReachability

universe u

variable {α : Type u} {r : α → α → Prop}

/-- A member of a nonempty list occurs as the last vertex of a nonempty
prefix.  Chainhood and absence of repetitions pass to that prefix. -/
private theorem exists_simple_prefix_to_mem [DecidableEq α]
    {l : List α} {c : α}
    (hlne : l ≠ []) (hchain : l.IsChain r) (hnodup : l.Nodup)
    (hc : c ∈ l) :
    ∃ p : List α, ∃ hpne : p ≠ [],
      p.IsChain r ∧ p.Nodup ∧
        p.head hpne = l.head hlne ∧ p.getLast hpne = c := by
  rw [List.mem_iff_append] at hc
  rcases hc with ⟨before, after, rfl⟩
  refine ⟨before ++ [c], by simp, ?_, ?_, ?_, ?_⟩
  · exact hchain.prefix ⟨after, by simp [List.append_assoc]⟩
  · have hpref : before ++ [c] <+: before ++ c :: after :=
      ⟨after, by simp [List.append_assoc]⟩
    exact hnodup.sublist hpref.sublist
  · cases before <;> simp
  · simp

/-- Reflexive-transitive reachability admits a nonempty, repetition-free
directed list path with the prescribed first and last vertices.

This strengthens `List.exists_isChain_ne_nil_of_relationReflTransGen` by
ensuring `List.Nodup`. -/
theorem exists_nodup_isChain_of_reflTransGen [DecidableEq α]
    {a b : α} (h : Relation.ReflTransGen r a b) :
    ∃ l : List α, ∃ hlne : l ≠ [],
      l.IsChain r ∧ l.Nodup ∧
        l.head hlne = a ∧ l.getLast hlne = b := by
  induction h with
  | refl =>
      exact ⟨[a], by simp, List.IsChain.singleton a,
        List.nodup_singleton a, rfl, rfl⟩
  | @tail b c hab hbc ih =>
      rcases ih with ⟨l, hlne, hchain, hnodup, hhead, hlast⟩
      by_cases hc : c ∈ l
      · rcases exists_simple_prefix_to_mem hlne hchain hnodup hc with
          ⟨p, hpne, hpchain, hpnodup, hphead, hplast⟩
        exact ⟨p, hpne, hpchain, hpnodup, hphead.trans hhead, hplast⟩
      · refine ⟨l ++ [c], by simp, ?_, ?_, ?_, ?_⟩
        · refine hchain.append (List.IsChain.singleton c) ?_
          intro x hx y hy
          simp [List.getLast?_eq_some_getLast hlne, hlast] at hx
          simp at hy
          subst x
          subst y
          exact hbc
        · simpa [List.concat_eq_append] using hnodup.concat hc
        · exact (List.head_append_of_ne_nil hlne).trans hhead
        · simp

end SimpleReachability

end TotalColoring
