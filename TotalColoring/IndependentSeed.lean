import TotalColoring.MissingGeneralCount
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Independent-seed total-coloring decoder

A supplied proper `q`-edge coloring, an independent set reserved for one
fresh color, and a supplied weighted peel order on its complement produce a
valid total coloring with `q + 1` colors.

The theorem is deliberately conditional.  In the intended specialization
`q = G.maxDegree + 1`, the palette has `G.maxDegree + 2` colors, but this
module does not supply Vizing's edge coloring or prove that an independent
seed certificate exists for every graph.
-/

namespace TotalColoring

universe u

namespace EdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type}

/-- Embed a complete edge assignment into the existing partial-assignment API. -/
def toPartial (a : EdgeAssignment G C) : PartialEdgeAssignment G C where
  color e := some (a.color e)

@[simp] theorem toPartial_color (a : EdgeAssignment G C) (e : G.edgeSet) :
    a.toPartial.color e = some (a.color e) := rfl

end EdgeAssignment

section Decoder

variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V} {q : ℕ}

/-- Decode an old-palette edge coloring, an independent fresh-color seed, and
old-palette colors on the complement into one total assignment. -/
def independentSeedAssignment
    (phi : EdgeAssignment G (Fin q)) (A : Finset V) (g : V → Fin q) :
    Assignment G (Fin (q + 1)) where
  vertexColor v := if v ∈ A then Fin.last q else Fin.castSucc (g v)
  edgeColor e := Fin.castSucc (phi.color e)

/-- Soundness of the independent-seed decoder. -/
theorem independentSeedAssignment_valid
    (phi : EdgeAssignment G (Fin q)) (A : Finset V) (g : V → Fin q)
    (hphi : phi.Valid)
    (hA : G.IsIndepSet (A : Set V))
    (hmissing : ∀ v, v ∉ A → ∀ e, Incident v e → phi.color e ≠ g v)
    (hproper : ∀ v, v ∉ A → ∀ w, w ∉ A → G.Adj v w → g v ≠ g w) :
    (independentSeedAssignment phi A g).Valid := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w hvw
    by_cases hv : v ∈ A
    · by_cases hw : w ∈ A
      · exact (hA hv hw hvw.ne hvw).elim
      · simpa [independentSeedAssignment, hv, hw] using
          (Fin.castSucc_ne_last (g w)).symm
    · by_cases hw : w ∈ A
      · simp [independentSeedAssignment, hv, hw]
      · intro heq
        apply hproper v hv w hw hvw
        exact (Fin.castSucc_injective q) (by
          simpa [independentSeedAssignment, hv, hw] using heq)
  · intro e f hef heq
    apply hphi e f hef
    exact (Fin.castSucc_injective q) (by
      simpa [independentSeedAssignment] using heq)
  · intro v e hve
    by_cases hv : v ∈ A
    · simpa [independentSeedAssignment, hv] using
        (Fin.castSucc_ne_last (phi.color e)).symm
    · intro heq
      apply hmissing v hv e hve
      exact ((Fin.castSucc_injective q) (by
        simpa [independentSeedAssignment, hv] using heq)).symm

end Decoder

section OneStep

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {q : ℕ}

/-- Fewer than `q - degree(v)` forbidden old colors cannot cover all old
colors missing on the incident edges at `v`. -/
theorem exists_missing_not_mem_of_card_lt_slack
    (phi : EdgeAssignment G (Fin q)) (v : V) (used : Finset (Fin q))
    (hused : used.card < q - G.degree v) :
    ∃ c : Fin q,
      c ∈ phi.toPartial.missingColorsAt Finset.univ v ∧ c ∉ used := by
  have hmissing : q - G.degree v ≤
      (phi.toPartial.missingColorsAt Finset.univ v).card := by
    simpa using
      PartialEdgeAssignment.palette_card_sub_degree_le_missingColorsAt_card
        phi.toPartial (Finset.univ : Finset (Fin q)) v
  have hlt : used.card <
      (phi.toPartial.missingColorsAt Finset.univ v).card :=
    lt_of_lt_of_le hused hmissing
  obtain ⟨c, hc⟩ := Finset.sdiff_nonempty_of_card_lt_card hlt
  exact ⟨c, (Finset.mem_sdiff.mp hc).1, (Finset.mem_sdiff.mp hc).2⟩

end OneStep

section PeelCertificate

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Recursive weighted peel inequalities, aligned with induction on the
supplied deletion order. -/
def IsPeelOrder (q : ℕ) : List V → Prop
  | [] => True
  | v :: tail =>
      (G.neighborFinset v ∩ tail.toFinset).card < q - G.degree v ∧
      IsPeelOrder q tail

/-- Data certifying that the complement of an independent seed peels under
the ambient slack `q - degree_G(v)`. -/
structure IndependentSeedPeelCertificate (A : Finset V) (q : ℕ) where
  order : List V
  nodup : order.Nodup
  covers : ∀ v, v ∈ order ↔ v ∉ A
  peels : IsPeelOrder G q order

/-- Reverse-greedy invariant on a suffix of the peel order. -/
def OldColoringGood {q : ℕ} (phi : EdgeAssignment G (Fin q))
    (order : List V) (g : V → Fin q) : Prop :=
  (∀ v, v ∈ order → phi.toPartial.MissingAt v (g v)) ∧
  (∀ v, v ∈ order → ∀ w, w ∈ order → G.Adj v w → g v ≠ g w)

/-- Reverse greedy coloring along a supplied peel order. -/
theorem exists_oldColoringGood_of_isPeelOrder {q : ℕ}
    (phi : EdgeAssignment G (Fin q)) (defaultColor : Fin q) :
    ∀ order : List V, order.Nodup → IsPeelOrder G q order →
      ∃ g : V → Fin q, OldColoringGood G phi order g := by
  intro order
  induction order with
  | nil =>
      intro _ _
      exact ⟨fun _ ↦ defaultColor, by simp [OldColoringGood]⟩
  | cons v tail ih =>
      intro hnodup hpeel
      have hvnot : v ∉ tail := (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hvbound :
          (G.neighborFinset v ∩ tail.toFinset).card < q - G.degree v :=
        hpeel.1
      have htailPeel : IsPeelOrder G q tail := hpeel.2
      obtain ⟨g, hgmissing, hgproper⟩ := ih htailNodup htailPeel
      let later : Finset V := G.neighborFinset v ∩ tail.toFinset
      let used : Finset (Fin q) := later.image g
      have husedCard : used.card < q - G.degree v := by
        exact lt_of_le_of_lt Finset.card_image_le hvbound
      obtain ⟨c, hcmissing, hcnotused⟩ :=
        exists_missing_not_mem_of_card_lt_slack phi v used husedCard
      let g' : V → Fin q := Function.update g v c
      refine ⟨g', ?_, ?_⟩
      · intro x hx
        rcases (List.mem_cons.mp hx) with rfl | hxtail
        · have hc :=
            (PartialEdgeAssignment.mem_missingColorsAt.mp hcmissing).2
          simpa [g'] using hc
        · have hxne : x ≠ v := by
            intro hxv
            subst x
            exact hvnot hxtail
          simpa [g', Function.update_of_ne hxne] using hgmissing x hxtail
      · intro x hx y hy hxy
        rcases (List.mem_cons.mp hx) with rfl | hxtail
        · rcases (List.mem_cons.mp hy) with rfl | hytail
          · exact (hxy.ne rfl).elim
          · have hyne : y ≠ x := hxy.ne.symm
            have hgyused : g y ∈ used := by
              apply Finset.mem_image.mpr
              refine ⟨y, ?_, rfl⟩
              simp [later, hxy, hytail]
            have hcgy : c ≠ g y := by
              intro hcgy
              apply hcnotused
              simpa [hcgy] using hgyused
            simpa [g', hyne] using hcgy
        · rcases (List.mem_cons.mp hy) with rfl | hytail
          · have hxne : x ≠ y := hxy.ne
            have hgxused : g x ∈ used := by
              apply Finset.mem_image.mpr
              refine ⟨x, ?_, rfl⟩
              simp [later, hxy.symm, hxtail]
            have hcx : c ≠ g x := by
              intro hcx
              apply hcnotused
              simpa [hcx] using hgxused
            simpa [g', hxne] using hcx.symm
          · have hxne : x ≠ v := by
              intro hxv
              subst x
              exact hvnot hxtail
            have hyne : y ≠ v := by
              intro hyv
              subst y
              exact hvnot hytail
            simpa [g', hxne, hyne] using
              hgproper x hxtail y hytail hxy

/-- A supplied proper `q`-edge coloring and independent-seed peel certificate
produce a valid total coloring with `q + 1` colors. -/
theorem exists_valid_assignment_of_independentSeedPeel {q : ℕ}
    (hq : 0 < q) (phi : EdgeAssignment G (Fin q)) (hphi : phi.Valid)
    (A : Finset V) (hA : G.IsIndepSet (A : Set V))
    (cert : IndependentSeedPeelCertificate G A q) :
    ∃ a : Assignment G (Fin (q + 1)), a.Valid := by
  let defaultColor : Fin q := ⟨0, hq⟩
  obtain ⟨g, hgmissing, hgproper⟩ :=
    exists_oldColoringGood_of_isPeelOrder G phi defaultColor cert.order
      cert.nodup cert.peels
  let a := independentSeedAssignment phi A g
  refine ⟨a, ?_⟩
  apply independentSeedAssignment_valid phi A g hphi hA
  · intro v hv e hve
    have hm := hgmissing v ((cert.covers v).2 hv) e hve
    simpa [EdgeAssignment.toPartial] using hm
  · intro v hv w hw hvw
    exact hgproper v ((cert.covers v).2 hv)
      w ((cert.covers w).2 hw) hvw

/-- Maximum-degree specialization of the conditional decoder.  The proper
`Delta + 1` edge coloring and the independent-seed peel certificate remain
explicit inputs; this is not an unconditional Total Coloring Conjecture. -/
theorem exists_valid_assignment_of_maxDegreeIndependentSeedPeel
    (phi : EdgeAssignment G (Fin (G.maxDegree + 1))) (hphi : phi.Valid)
    (A : Finset V) (hA : G.IsIndepSet (A : Set V))
    (cert : IndependentSeedPeelCertificate G A (G.maxDegree + 1)) :
    ∃ a : Assignment G (Fin (G.maxDegree + 2)), a.Valid := by
  simpa [Nat.add_assoc] using
    exists_valid_assignment_of_independentSeedPeel G (Nat.zero_lt_succ _)
      phi hphi A hA cert

end PeelCertificate

end TotalColoring
