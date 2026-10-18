/-
Copyright (c) 2026 Le Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Le Chen
-/
import Mathlib

/-!
# Comparator challenge: the partial-edge selector decoder

Statement only, in Mathlib's vocabulary. Start from old edge colors
`phi : G.edgeSet → Fin q`, old vertex colors `g : V → Fin q`, a vertex set `S`
and an edge set `F`, and a fresh color `fresh : Fin (q + 1)`. The decoded total
assignment colors a vertex `fresh` if it is in `S` and `fresh.succAbove (g v)`
otherwise, and an edge `fresh` if it is in `F` and `fresh.succAbove (phi e)`
otherwise (`Fin.succAbove` embeds `Fin q` into `Fin (q + 1)` missing `fresh`).

Hypotheses: `phi` is proper on adjacent edges both outside `F`; `S` is
independent in `G`; `F` is a matching (no two members adjacent in Mathlib's
line graph); no edge of `F` meets `S`; outside `S`, the old color `g v` differs
from `phi` on every incident edge outside `F`; and `g` is proper on adjacent
vertices outside `S`.

Claim: the decoded assignment is a total coloring (adjacent vertices, adjacent
edges, and a vertex and an incident edge get different colors).
-/

namespace TotalColoringAudit.PartialEdgeSelector

theorem partialEdgeSelectorAssignment_valid
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {q : ℕ}
    (fresh : Fin (q + 1)) (phi : G.edgeSet → Fin q)
    (S : Finset V) (F : Finset G.edgeSet) (g : V → Fin q)
    (hphi : ∀ e f : G.edgeSet, e ∉ F → f ∉ F → G.lineGraph.Adj e f → phi e ≠ phi f)
    (hS : G.IsIndepSet (S : Set V))
    (hF : ∀ ⦃e f : G.edgeSet⦄, e ∈ F → f ∈ F → ¬G.lineGraph.Adj e f)
    (havoid : ∀ ⦃v : V⦄, v ∈ S → ∀ ⦃e : G.edgeSet⦄, e ∈ F → v ∉ (e : Sym2 V))
    (hallowed : ∀ v, v ∉ S → ∀ e : G.edgeSet, v ∈ (e : Sym2 V) → e ∉ F → phi e ≠ g v)
    (hproper : ∀ v, v ∉ S → ∀ w, w ∉ S → G.Adj v w → g v ≠ g w) :
    (∀ v w, G.Adj v w →
        (if v ∈ S then fresh else fresh.succAbove (g v)) ≠
          (if w ∈ S then fresh else fresh.succAbove (g w))) ∧
      (∀ e f, G.lineGraph.Adj e f →
        (if e ∈ F then fresh else fresh.succAbove (phi e)) ≠
          (if f ∈ F then fresh else fresh.succAbove (phi f))) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) →
        (if v ∈ S then fresh else fresh.succAbove (g v)) ≠
          (if e ∈ F then fresh else fresh.succAbove (phi e))) := by
  sorry

end TotalColoringAudit.PartialEdgeSelector
