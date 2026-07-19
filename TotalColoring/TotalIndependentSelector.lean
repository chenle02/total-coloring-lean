import TotalColoring.IndependentSeed

/-!
# Total-independent selector decoder

A supplied proper old-palette edge coloring may use one fresh color on an
independent set of vertices and, simultaneously, on a matching of edges which
avoids those vertices.  A supplied old-coloring of the remaining core, plus a
supplied weighted peel certificate for the vertices outside the core, then
produces a valid total coloring with one additional color.

The declarations in this module are deliberately conditional.  They do not
construct a Vizing edge coloring, a canonical weighted core, a selector, a
rainbow spanning path, or any of the supplied coloring certificates.
-/

namespace TotalColoring

universe u

section Selector

variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V} {q : ℕ}

/-- A finite family of graph edges is a matching when no two selected edges
are adjacent in the line graph. -/
def EdgeFinsetIsMatching (F : Finset G.edgeSet) : Prop :=
  ∀ ⦃e f : G.edgeSet⦄, e ∈ F → f ∈ F → ¬G.lineGraph.Adj e f

/-- The selected edges avoid every vertex in `S`. -/
def EdgeFinsetAvoids (F : Finset G.edgeSet) (S : Finset V) : Prop :=
  ∀ ⦃v : V⦄, v ∈ S → ∀ ⦃e : G.edgeSet⦄, e ∈ F → ¬Incident v e

/-- An old color is allowed at `v` after every selected edge is moved to the
fresh color.  Only the incident edges which retain their old colors constrain
the old vertex color. -/
def SelectorOldColorAllowed (phi : EdgeAssignment G (Fin q))
    (F : Finset G.edgeSet) (v : V) (c : Fin q) : Prop :=
  ∀ e : G.edgeSet, Incident v e → e ∉ F → phi.color e ≠ c

/-- Move every selected edge to the one fresh color. -/
def selectorEdgeAssignment (phi : EdgeAssignment G (Fin q))
    (F : Finset G.edgeSet) : EdgeAssignment G (Fin (q + 1)) where
  color e := if e ∈ F then Fin.last q else Fin.castSucc (phi.color e)

/-- The selected-edge lift preserves proper edge coloring. -/
theorem selectorEdgeAssignment_valid
    (phi : EdgeAssignment G (Fin q)) (F : Finset G.edgeSet)
    (hphi : phi.Valid) (hF : EdgeFinsetIsMatching (G := G) F) :
    (selectorEdgeAssignment phi F).Valid := by
  intro e f hef
  by_cases he : e ∈ F
  · by_cases hf : f ∈ F
    · exact (hF he hf hef).elim
    · simpa [selectorEdgeAssignment, he, hf] using
        (Fin.castSucc_ne_last (phi.color f)).symm
  · by_cases hf : f ∈ F
    · simp [selectorEdgeAssignment, he, hf]
    · intro heq
      apply hphi e f hef
      exact Fin.castSucc_injective q (by
        simpa [selectorEdgeAssignment, he, hf] using heq)

/-- Decode the fresh vertex set, fresh edge matching, and old colors on every
other vertex into a total assignment. -/
def totalIndependentSelectorAssignment
    (phi : EdgeAssignment G (Fin q)) (S : Finset V)
    (F : Finset G.edgeSet) (g : V → Fin q) :
    Assignment G (Fin (q + 1)) where
  vertexColor v := if v ∈ S then Fin.last q else Fin.castSucc (g v)
  edgeColor := (selectorEdgeAssignment phi F).color

/-- Soundness of the total-independent selector decoder once old colors have
been supplied on every vertex outside `S`. -/
theorem totalIndependentSelectorAssignment_valid
    (phi : EdgeAssignment G (Fin q)) (S : Finset V)
    (F : Finset G.edgeSet) (g : V → Fin q)
    (hphi : phi.Valid)
    (hS : G.IsIndepSet (S : Set V))
    (hF : EdgeFinsetIsMatching (G := G) F)
    (havoid : EdgeFinsetAvoids (G := G) F S)
    (hallowed : ∀ v, v ∉ S → SelectorOldColorAllowed phi F v (g v))
    (hproper : ∀ v, v ∉ S → ∀ w, w ∉ S → G.Adj v w → g v ≠ g w) :
    (totalIndependentSelectorAssignment phi S F g).Valid := by
  refine ⟨?_, selectorEdgeAssignment_valid phi F hphi hF, ?_⟩
  · intro v w hvw
    by_cases hv : v ∈ S
    · by_cases hw : w ∈ S
      · exact (hS hv hw hvw.ne hvw).elim
      · simpa [totalIndependentSelectorAssignment, hv, hw] using
          (Fin.castSucc_ne_last (g w)).symm
    · by_cases hw : w ∈ S
      · simp [totalIndependentSelectorAssignment, hv, hw]
      · intro heq
        apply hproper v hv w hw hvw
        exact Fin.castSucc_injective q (by
          simpa [totalIndependentSelectorAssignment, hv, hw] using heq)
  · intro v e hve
    by_cases hv : v ∈ S
    · have he : e ∉ F := by
        intro heF
        exact havoid hv heF hve
      simpa [totalIndependentSelectorAssignment, selectorEdgeAssignment,
        hv, he] using (Fin.castSucc_ne_last (phi.color e)).symm
    · by_cases he : e ∈ F
      · simp [totalIndependentSelectorAssignment, selectorEdgeAssignment,
          hv, he]
      · intro heq
        apply hallowed v hv e hve he
        exact (Fin.castSucc_injective q (by
          simpa [totalIndependentSelectorAssignment, selectorEdgeAssignment,
            hv, he] using heq)).symm

end Selector

section SpareLift

variable {V : Type u} [DecidableEq V]
variable {G : SimpleGraph V} {q : ℕ}

/-- The actual-list-coloring invariant on the old-colored part of `X`.

Vertices in `S` use the fresh color and are deliberately omitted.  At every
other vertex the old color must avoid the incident edges which retain their
old colors, and adjacent old-colored vertices must receive distinct colors. -/
def SelectorOldColoringGoodOn (H : SimpleGraph V)
    (phi : EdgeAssignment H (Fin q))
    (S : Finset V) (F : Finset H.edgeSet) (X : Finset V)
  (g : V → Fin q) : Prop :=
  (∀ v, v ∈ X → v ∉ S → SelectorOldColorAllowed phi F v (g v)) ∧
  (∀ v, v ∈ X → v ∉ S → ∀ w, w ∈ X → w ∉ S →
    H.Adj v w → g v ≠ g w)

/-- Recolor a supplied matching with an old color which was globally unused
by the original edge coloring. -/
def spareLiftEdgeAssignment (phi₀ : EdgeAssignment G (Fin q))
    (R : Finset G.edgeSet) (spare : Fin q) : EdgeAssignment G (Fin q) where
  color e := if e ∈ R then spare else phi₀.color e

/-- Recoloring a matching with a globally unused old color preserves proper
edge coloring. -/
theorem spareLiftEdgeAssignment_valid
    (phi₀ : EdgeAssignment G (Fin q)) (R : Finset G.edgeSet)
    (spare : Fin q) (hphi₀ : phi₀.Valid)
    (hR : EdgeFinsetIsMatching (G := G) R)
    (hspare : ∀ e, phi₀.color e ≠ spare) :
    (spareLiftEdgeAssignment phi₀ R spare).Valid := by
  intro e f hef
  by_cases he : e ∈ R
  · by_cases hf : f ∈ R
    · exact (hR he hf hef).elim
    · simpa [spareLiftEdgeAssignment, he, hf] using
        (hspare f).symm
  · by_cases hf : f ∈ R
    · simpa [spareLiftEdgeAssignment, he, hf] using hspare e
    · simpa [spareLiftEdgeAssignment, he, hf] using hphi₀ e f hef

/-- The pointwise donor condition behind the alternating rainbow-path
exchange.  Each old-colored core vertex receives the old color of an
incident edge which is moved either to the unused old spare or to the fresh
total color. -/
def HasSelectorDonor (phi₀ : EdgeAssignment G (Fin q))
    (R F : Finset G.edgeSet) (v : V) (c : Fin q) : Prop :=
  ∃ d : G.edgeSet,
    Incident v d ∧ phi₀.color d = c ∧ (d ∈ R ∨ d ∈ F)

/-- Donor edges turn a supplied proper core coloring into a proper
actual-list coloring after the old-spare lift.

This is the formal exchange seam used by the rainbow-path construction.  It
does not assert that donor edges or a rainbow path exist. -/
theorem selectorOldColoringGoodOn_spareLift_of_donors
    (phi₀ : EdgeAssignment G (Fin q)) (hphi₀ : phi₀.Valid)
    (R F : Finset G.edgeSet) (spare : Fin q)
    (hspare : ∀ e, phi₀.color e ≠ spare)
    (S K : Finset V) (g : V → Fin q)
    (hproper : ∀ v, v ∈ K → v ∉ S → ∀ w, w ∈ K → w ∉ S →
      G.Adj v w → g v ≠ g w)
    (hdonor : ∀ v, v ∈ K → v ∉ S → HasSelectorDonor phi₀ R F v (g v)) :
    SelectorOldColoringGoodOn G
      (spareLiftEdgeAssignment phi₀ R spare) S F K g := by
  refine ⟨?_, hproper⟩
  intro v hvK hvS e hve heF
  obtain ⟨d, hvd, hdcolor, hdRF⟩ := hdonor v hvK hvS
  by_cases heR : e ∈ R
  · have hne : spare ≠ g v := by
      simpa [hdcolor] using (hspare d).symm
    simpa [spareLiftEdgeAssignment, heR] using hne
  · have hed : e ≠ d := by
      intro hed
      subst d
      exact hdRF.elim heR heF
    have hedAdj : G.lineGraph.Adj e d :=
      SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨hed, v, hve, hvd⟩
    have hcolors : phi₀.color e ≠ phi₀.color d := hphi₀ e d hedAdj
    simpa [spareLiftEdgeAssignment, heR, hdcolor] using hcolors

end SpareLift

section CorePeel

variable {V : Type u} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] {q : ℕ}

/-- Recursive peel inequalities relative to an already colored core.

At the step for `v`, the forbidden old vertex colors can come from the
old-colored core `K \ S` and from the later vertices in the peel order. -/
def IsSelectorCorePeelOrder (S K : Finset V) (q : ℕ) : List V → Prop
  | [] => True
  | v :: tail =>
      (G.neighborFinset v ∩ ((K \ S) ∪ tail.toFinset)).card <
          q - G.degree v ∧
      IsSelectorCorePeelOrder S K q tail

/-- Supplied evidence that the complement of `K` admits the exact
core-relative peel inequalities needed by the selector decoder. -/
structure SelectorCorePeelCertificate (S K : Finset V) (q : ℕ) where
  seed_subset_core : S ⊆ K
  order : List V
  nodup : order.Nodup
  covers : ∀ v, v ∈ order ↔ v ∉ K
  peels : IsSelectorCorePeelOrder G S K q order

/-- Reverse greedy extension of a supplied proper actual-list coloring on
`K \ S` along a supplied core-relative peel order. -/
theorem exists_selectorOldColoringGoodOn_union_of_isSelectorCorePeelOrder
    (phi : EdgeAssignment G (Fin q)) (S K : Finset V)
    (F : Finset G.edgeSet) (g₀ : V → Fin q)
    (hSK : S ⊆ K)
    (hcore : SelectorOldColoringGoodOn G phi S F K g₀) :
    ∀ order : List V,
      order.Nodup →
      (∀ v, v ∈ order → v ∉ K) →
      IsSelectorCorePeelOrder G S K q order →
      ∃ g : V → Fin q,
        SelectorOldColoringGoodOn G phi S F (K ∪ order.toFinset) g := by
  intro order
  induction order with
  | nil =>
      intro _ _ _
      exact ⟨g₀, by simpa [SelectorOldColoringGoodOn] using hcore⟩
  | cons v tail ih =>
      intro hnodup houtside hpeel
      have hvnotTail : v ∉ tail := (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hnodup).2
      have hvnotK : v ∉ K := houtside v (by simp)
      have hvnotS : v ∉ S := by
        intro hvS
        exact hvnotK (hSK hvS)
      have htailOutside : ∀ x, x ∈ tail → x ∉ K := by
        intro x hx
        exact houtside x (by simp [hx])
      have hvbound :
          (G.neighborFinset v ∩ ((K \ S) ∪ tail.toFinset)).card <
            q - G.degree v := hpeel.1
      have htailPeel : IsSelectorCorePeelOrder G S K q tail := hpeel.2
      obtain ⟨g, hgallowed, hgproper⟩ :=
        ih htailNodup htailOutside htailPeel
      let later : Finset V :=
        G.neighborFinset v ∩ ((K \ S) ∪ tail.toFinset)
      let used : Finset (Fin q) := later.image g
      have husedCard : used.card < q - G.degree v := by
        exact lt_of_le_of_lt Finset.card_image_le hvbound
      obtain ⟨c, hcmissing, hcnotused⟩ :=
        exists_missing_not_mem_of_card_lt_slack phi v used husedCard
      have hcmissingAt : phi.toPartial.MissingAt v c :=
        (PartialEdgeAssignment.mem_missingColorsAt.mp hcmissing).2
      let g' : V → Fin q := Function.update g v c
      have old_of_new_of_ne {x : V}
          (hx : x ∈ K ∪ (v :: tail).toFinset) (hxne : x ≠ v) :
          x ∈ K ∪ tail.toFinset := by
        simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at hx ⊢
        rcases hx with hxK | hxv | hxtail
        · exact Or.inl hxK
        · exact (hxne hxv).elim
        · exact Or.inr hxtail
      have active_of_old {x : V}
          (hx : x ∈ K ∪ tail.toFinset) (hxS : x ∉ S) :
          x ∈ (K \ S) ∪ tail.toFinset := by
        rcases Finset.mem_union.mp hx with hxK | hxtail
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_sdiff.mpr ⟨hxK, hxS⟩))
        · exact Finset.mem_union.mpr (Or.inr hxtail)
      refine ⟨g', ?_, ?_⟩
      · intro x hx hxS
        by_cases hxv : x = v
        · subst x
          intro e hve _
          have hm := hcmissingAt e hve
          simpa [g', EdgeAssignment.toPartial] using hm
        · have hxold := old_of_new_of_ne hx hxv
          simpa [g', Function.update_of_ne hxv] using
            hgallowed x hxold hxS
      · intro x hx hxS y hy hyS hxy
        by_cases hxv : x = v
        · subst x
          have hyv : y ≠ v := hxy.ne.symm
          have hyold := old_of_new_of_ne hy hyv
          have hyactive := active_of_old hyold hyS
          have hgyused : g y ∈ used := by
            apply Finset.mem_image.mpr
            refine ⟨y, ?_, rfl⟩
            simp [later, hxy, hyactive]
          have hcgy : c ≠ g y := by
            intro hcgy
            apply hcnotused
            simpa [hcgy] using hgyused
          simpa [g', hyv] using hcgy
        · by_cases hyv : y = v
          · subst y
            have hxold := old_of_new_of_ne hx hxv
            have hxactive := active_of_old hxold hxS
            have hgxused : g x ∈ used := by
              apply Finset.mem_image.mpr
              refine ⟨x, ?_, rfl⟩
              simp [later, hxy.symm, hxactive]
            have hcgx : c ≠ g x := by
              intro hcgx
              apply hcnotused
              simpa [hcgx] using hgxused
            simpa [g', hxv] using hcgx.symm
          · have hxold := old_of_new_of_ne hx hxv
            have hyold := old_of_new_of_ne hy hyv
            simpa [g', Function.update_of_ne hxv,
              Function.update_of_ne hyv] using
              hgproper x hxold hxS y hyold hyS hxy

/-- A supplied proper old-palette edge coloring, independent fresh vertex
set, fresh edge matching, proper actual-list coloring of `K \ S`, and exact
core-relative peel certificate decode to a valid total coloring. -/
theorem exists_valid_assignment_of_totalIndependentSelectorPeel
    (phi : EdgeAssignment G (Fin q)) (hphi : phi.Valid)
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (F : Finset G.edgeSet) (hF : EdgeFinsetIsMatching (G := G) F)
    (havoid : EdgeFinsetAvoids (G := G) F S)
    (K : Finset V) (g₀ : V → Fin q)
    (hcore : SelectorOldColoringGoodOn G phi S F K g₀)
    (cert : SelectorCorePeelCertificate G S K q) :
    ∃ a : Assignment G (Fin (q + 1)), a.Valid := by
  obtain ⟨g, hgallowed, hgproper⟩ :=
    exists_selectorOldColoringGoodOn_union_of_isSelectorCorePeelOrder
      G phi S K F g₀ cert.seed_subset_core hcore cert.order cert.nodup
      (fun v hv ↦ (cert.covers v).1 hv) cert.peels
  have hcovered : ∀ v, v ∈ K ∪ cert.order.toFinset := by
    intro v
    by_cases hvK : v ∈ K
    · exact Finset.mem_union.mpr (Or.inl hvK)
    · exact Finset.mem_union.mpr
        (Or.inr (List.mem_toFinset.mpr ((cert.covers v).2 hvK)))
  let a := totalIndependentSelectorAssignment phi S F g
  refine ⟨a, ?_⟩
  apply totalIndependentSelectorAssignment_valid phi S F g hphi hS hF havoid
  · intro v hvS
    exact hgallowed v (hcovered v) hvS
  · intro v hvS w hwS hvw
    exact hgproper v (hcovered v) hvS w (hcovered w) hwS hvw

/-- Maximum-degree specialization of the conditional total-independent
selector decoder.  The proper edge coloring, selector data, core coloring,
and peel certificate all remain explicit inputs. -/
theorem exists_valid_assignment_of_maxDegreeTotalIndependentSelectorPeel
    (phi : EdgeAssignment G (Fin (G.maxDegree + 1))) (hphi : phi.Valid)
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (F : Finset G.edgeSet) (hF : EdgeFinsetIsMatching (G := G) F)
    (havoid : EdgeFinsetAvoids (G := G) F S)
    (K : Finset V) (g₀ : V → Fin (G.maxDegree + 1))
    (hcore : SelectorOldColoringGoodOn G phi S F K g₀)
    (cert : SelectorCorePeelCertificate G S K (G.maxDegree + 1)) :
    ∃ a : Assignment G (Fin (G.maxDegree + 2)), a.Valid := by
  simpa [Nat.add_assoc] using
    exists_valid_assignment_of_totalIndependentSelectorPeel G phi hphi S hS
      F hF havoid K g₀ hcore cert

/-- Explicit certificate for the consequences of an alternating rainbow path
spanning the supplied core.

There are `k + 1` ordered path vertices and `k` ordered path edges.  Edge
index `i` is zero-based, so even indices are the prose proof's odd-position
edges moved to the unused old color, while odd indices are moved to the fresh
total color.  Matching and seed-avoidance facts are retained as checked
certificate fields; this declaration does not assert that such a path exists. -/
structure AlternatingRainbowPathSelectorCertificate
    (phi₀ : EdgeAssignment G (Fin q)) (K : Finset V) (k : ℕ) where
  vertex : Fin (k + 1) → V
  edge : Fin k → G.edgeSet
  vertex_injective : Function.Injective vertex
  edge_endpoints : ∀ i,
    (edge i : Sym2 V) = s(vertex i.castSucc, vertex i.succ)
  spans_core : ∀ v, v ∈ K ↔ ∃ i, vertex i = v
  rainbow : Function.Injective (fun i ↦ phi₀.color (edge i))
  spare : Fin q
  spare_unused : ∀ e, phi₀.color e ≠ spare
  oldLiftEdges : Finset G.edgeSet
  freshEdges : Finset G.edgeSet
  alternates : ∀ i,
    (edge i ∈ oldLiftEdges ↔ Even i.val) ∧
    (edge i ∈ freshEdges ↔ Odd i.val)
  oldLift_matching : EdgeFinsetIsMatching (G := G) oldLiftEdges
  fresh_matching : EdgeFinsetIsMatching (G := G) freshEdges
  fresh_avoids_start :
    EdgeFinsetAvoids (G := G) freshEdges {vertex 0}
  coreColor : V → Fin q
  coreColor_succ : ∀ i,
    coreColor (vertex i.succ) = phi₀.color (edge i)
  peel : SelectorCorePeelCertificate G {vertex 0} K q

/-- An explicit alternating rainbow-path certificate and its supplied peel
certificate decode to a valid total coloring with one additional color. -/
theorem exists_valid_assignment_of_alternatingRainbowPathSelector
    (phi₀ : EdgeAssignment G (Fin q)) (hphi₀ : phi₀.Valid)
    (K : Finset V) (k : ℕ)
    (cert : AlternatingRainbowPathSelectorCertificate G phi₀ K k) :
    ∃ a : Assignment G (Fin (q + 1)), a.Valid := by
  let S : Finset V := {cert.vertex 0}
  let phi := spareLiftEdgeAssignment phi₀ cert.oldLiftEdges cert.spare
  have hphi : phi.Valid :=
    spareLiftEdgeAssignment_valid phi₀ cert.oldLiftEdges cert.spare
      hphi₀ cert.oldLift_matching cert.spare_unused
  have hS : G.IsIndepSet (S : Set V) := by
    simp [S, SimpleGraph.IsIndepSet]
  have predecessor_of_core_not_start :
      ∀ v, v ∈ K → v ∉ S → ∃ i : Fin k, cert.vertex i.succ = v := by
    intro v hvK hvS
    obtain ⟨j, hj⟩ := (cert.spans_core v).1 hvK
    have hj0 : j ≠ 0 := by
      intro hj0
      subst j
      apply hvS
      simp [S, hj]
    obtain ⟨i, hi⟩ := Fin.exists_succ_eq_of_ne_zero hj0
    refine ⟨i, ?_⟩
    rw [hi]
    exact hj
  have hproper :
      ∀ v, v ∈ K → v ∉ S → ∀ w, w ∈ K → w ∉ S →
        G.Adj v w → cert.coreColor v ≠ cert.coreColor w := by
    intro v hvK hvS w hwK hwS hvw
    obtain ⟨i, hi⟩ := predecessor_of_core_not_start v hvK hvS
    obtain ⟨j, hj⟩ := predecessor_of_core_not_start w hwK hwS
    have hij : i ≠ j := by
      intro hij
      subst j
      apply hvw.ne
      exact hi.symm.trans hj
    have hcolor : phi₀.color (cert.edge i) ≠
        phi₀.color (cert.edge j) := by
      intro hcolor
      exact hij (cert.rainbow hcolor)
    calc
      cert.coreColor v = phi₀.color (cert.edge i) := by
        rw [← hi]
        exact cert.coreColor_succ i
      _ ≠ phi₀.color (cert.edge j) := hcolor
      _ = cert.coreColor w := by
        rw [← hj]
        exact (cert.coreColor_succ j).symm
  have hdonor :
      ∀ v, v ∈ K → v ∉ S →
        HasSelectorDonor phi₀ cert.oldLiftEdges cert.freshEdges v
          (cert.coreColor v) := by
    intro v hvK hvS
    obtain ⟨i, hi⟩ := predecessor_of_core_not_start v hvK hvS
    refine ⟨cert.edge i, ?_, ?_, ?_⟩
    · change v ∈ (cert.edge i : Sym2 V)
      rw [← hi, cert.edge_endpoints]
      simp
    · rw [← hi]
      exact (cert.coreColor_succ i).symm
    · rcases Nat.even_or_odd i.val with heven | hodd
      · exact Or.inl ((cert.alternates i).1.mpr heven)
      · exact Or.inr ((cert.alternates i).2.mpr hodd)
  have hcore : SelectorOldColoringGoodOn G phi S cert.freshEdges K
      cert.coreColor := by
    exact selectorOldColoringGoodOn_spareLift_of_donors phi₀ hphi₀
      cert.oldLiftEdges cert.freshEdges cert.spare cert.spare_unused S K
      cert.coreColor hproper hdonor
  exact exists_valid_assignment_of_totalIndependentSelectorPeel G phi hphi
    S hS cert.freshEdges cert.fresh_matching cert.fresh_avoids_start K
    cert.coreColor hcore cert.peel

/-- Maximum-degree specialization of the explicit alternating rainbow-path
wrapper.  Path and peel existence remain certificate inputs. -/
theorem exists_valid_assignment_of_maxDegreeAlternatingRainbowPathSelector
    (phi₀ : EdgeAssignment G (Fin (G.maxDegree + 1))) (hphi₀ : phi₀.Valid)
    (K : Finset V) (k : ℕ)
    (cert : AlternatingRainbowPathSelectorCertificate G phi₀ K k) :
    ∃ a : Assignment G (Fin (G.maxDegree + 2)), a.Valid := by
  simpa [Nat.add_assoc] using
    exists_valid_assignment_of_alternatingRainbowPathSelector G phi₀
      hphi₀ K k cert

end CorePeel

end TotalColoring
