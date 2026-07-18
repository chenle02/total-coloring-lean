import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
import Mathlib.Combinatorics.SimpleGraph.Operations

/-!
# A minimum-degree lower bound for matchings

This module isolates the finite graph-theoretic matching lemma needed by the
pair/singleton construction.  A matching is represented as a spanning simple
subgraph whose neighbor set at every vertex is subsingleton.  This avoids
adding irrelevant vertex-set bookkeeping: the covered vertices are exactly
the support of that spanning subgraph.

The proof chooses a maximum-cardinality matching by `SimpleGraph.IsExtremal`.
Two uncovered vertices cannot be adjacent, and a matched edge cannot complete
an augmenting path of length three between two uncovered vertices.  Applying
these two exchange facts to the neighborhoods of two uncovered vertices gives
the standard degree-sum contradiction.
-/

namespace TotalColoring.MatchingLowerBound

open Finset

universe u

variable {V : Type u}

/-- A spanning simple graph is a matching when every vertex has at most one
neighbor.  Its support is therefore the set of vertices covered by the
matching. -/
def IsMatchingGraph (M : SimpleGraph V) : Prop :=
  ∀ v, (M.neighborSet v).Subsingleton

/-- The extremal property used below: `M` is a matching contained in `H`. -/
def MatchingSubgraphOf (H M : SimpleGraph V) : Prop :=
  M ≤ H ∧ IsMatchingGraph M

theorem isMatchingGraph_bot : IsMatchingGraph (⊥ : SimpleGraph V) := by
  intro v a ha b hb
  simp only [SimpleGraph.mem_neighborSet, SimpleGraph.bot_adj] at ha

theorem IsMatchingGraph.mono {M N : SimpleGraph V} (hM : IsMatchingGraph M)
    (hNM : N ≤ M) : IsMatchingGraph N := by
  intro v a ha b hb
  exact hM v (SimpleGraph.neighborSet_mono hNM v ha)
    (SimpleGraph.neighborSet_mono hNM v hb)

theorem IsMatchingGraph.degree_le_one [Fintype V] {M : SimpleGraph V}
    [DecidableRel M.Adj] (hM : IsMatchingGraph M) (v : V) : M.degree v ≤ 1 := by
  rw [← M.card_neighborFinset_eq_degree v, Finset.card_le_one_iff_subsingleton]
  simpa only [SimpleGraph.coe_neighborFinset] using hM v

/-- Every edge of a matching contributes its two distinct endpoints to the
support. -/
theorem IsMatchingGraph.card_support_eq_twice_card_edgeFinset [Fintype V]
    {M : SimpleGraph V} [DecidableRel M.Adj] (hM : IsMatchingGraph M) :
    #M.support.toFinset = 2 * #M.edgeFinset := by
  calc
    #M.support.toFinset = ∑ v ∈ M.support.toFinset, 1 := by simp
    _ = ∑ v ∈ M.support.toFinset, M.degree v := by
      apply Finset.sum_congr rfl
      intro v hv
      have hv' : v ∈ M.support := by simpa using hv
      have hpos : 0 < M.degree v := (M.degree_pos_iff_mem_support v).2 hv'
      have hle : M.degree v ≤ 1 := hM.degree_le_one v
      omega
    _ = 2 * #M.edgeFinset := by
      simpa only using M.sum_degrees_support_eq_twice_card_edges

/-- `edgeFinset.card` is independent of the particular `Fintype` witness used
to enumerate the edge set.  The `Set.ncard` normal form is useful when an
extremal graph and an explicitly constructed graph acquire different finite
edge-set instances. -/
private theorem edgeFinset_card_eq_edgeSet_ncard {G : SimpleGraph V}
    [Fintype G.edgeSet] : #G.edgeFinset = G.edgeSet.ncard := by
  change G.edgeSet.toFinset.card = G.edgeSet.ncard
  exact (Set.ncard_eq_toFinset_card' G.edgeSet).symm

/-- The unique mate of a covered vertex; uncovered vertices are fixed. -/
noncomputable def mate (M : SimpleGraph V) (v : V) : V := by
  classical
  exact if hv : v ∈ M.support then Classical.choose (M.mem_support.mp hv) else v

theorem mate_eq_self_of_not_mem_support (M : SimpleGraph V) {v : V}
    (hv : v ∉ M.support) : mate M v = v := by
  simp [mate, hv]

theorem adj_mate (M : SimpleGraph V) {v : V} (hv : v ∈ M.support) :
    M.Adj v (mate M v) := by
  rw [mate, dif_pos hv]
  exact Classical.choose_spec (M.mem_support.mp hv)

theorem IsMatchingGraph.mate_eq_of_adj {M : SimpleGraph V}
    (hM : IsMatchingGraph M) {v w : V} (hvw : M.Adj v w) : mate M v = w := by
  have hv : v ∈ M.support := hvw.mem_support_left
  rw [mate, dif_pos hv]
  exact hM v (Classical.choose_spec (M.mem_support.mp hv)) hvw

theorem mate_mem_support {M : SimpleGraph V} {v : V} (hv : v ∈ M.support) :
    mate M v ∈ M.support := by
  exact (adj_mate M hv).mem_support_right

theorem IsMatchingGraph.mate_mate {M : SimpleGraph V} (hM : IsMatchingGraph M)
    (v : V) : mate M (mate M v) = v := by
  by_cases hv : v ∈ M.support
  · exact hM.mate_eq_of_adj (adj_mate M hv).symm
  · simp [mate_eq_self_of_not_mem_support M hv]

theorem IsMatchingGraph.mate_injective {M : SimpleGraph V}
    (hM : IsMatchingGraph M) : Function.Injective (mate M) :=
  Function.LeftInverse.injective hM.mate_mate

private theorem IsMatchingGraph.sup_edge_of_uncovered {M : SimpleGraph V}
    (hM : IsMatchingGraph M) {u v : V} (hu : u ∉ M.support)
    (hv : v ∉ M.support) :
    IsMatchingGraph (M ⊔ SimpleGraph.edge u v) := by
  have hu_iso : ∀ z, ¬M.Adj u z := fun z huz ↦ hu huz.mem_support_left
  have hv_iso : ∀ z, ¬M.Adj v z := fun z hvz ↦ hv hvz.mem_support_left
  intro z a hza b hzb
  rw [SimpleGraph.mem_neighborSet] at hza hzb
  rw [SimpleGraph.sup_adj] at hza hzb
  rcases hza with hza | hza <;> rcases hzb with hzb | hzb
  · exact hM z hza hzb
  · rw [SimpleGraph.edge_adj] at hzb
    rcases hzb.1 with hzb | hzb
    · exact (hu_iso _ (hzb.1 ▸ hza)).elim
    · exact (hv_iso _ (hzb.1 ▸ hza)).elim
  · rw [SimpleGraph.edge_adj] at hza
    rcases hza.1 with hza | hza
    · exact (hu_iso _ (hza.1 ▸ hzb)).elim
    · exact (hv_iso _ (hza.1 ▸ hzb)).elim
  · rw [SimpleGraph.edge_adj] at hza hzb
    rcases hza.1 with hza | hza <;> rcases hzb.1 with hzb | hzb <;> grind

private theorem edge_le_of_adj {H : SimpleGraph V} {u v : V}
    (huv : H.Adj u v) : SimpleGraph.edge u v ≤ H := by
  intro x y hxy
  rw [SimpleGraph.edge_adj] at hxy
  rcases hxy.1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact huv
  · exact huv.symm

private theorem edge_adj_neighbor_eq {u v z a b : V}
    (hza : (SimpleGraph.edge u v).Adj z a)
    (hzb : (SimpleGraph.edge u v).Adj z b) : a = b := by
  rw [SimpleGraph.edge_adj] at hza hzb
  rcases hza.1 with hza | hza <;> rcases hzb.1 with hzb | hzb <;> grind

private theorem disjoint_new_edges_not_both_adjacent {u v x y z a b : V}
    (huv : u ≠ v) (huy : u ≠ y) (hvx : v ≠ x) (hxy : x ≠ y)
    (hza : (SimpleGraph.edge u x).Adj z a)
    (hzb : (SimpleGraph.edge v y).Adj z b) : False := by
  rw [SimpleGraph.edge_adj] at hza hzb
  rcases hza.1 with hza | hza <;> rcases hzb.1 with hzb | hzb <;> grind

private theorem IsMatchingGraph.exchange {M : SimpleGraph V}
    (hM : IsMatchingGraph M) {u v x y : V} (hu : u ∉ M.support)
    (hv : v ∉ M.support) (huv : u ≠ v) (huy : u ≠ y)
    (hvx : v ≠ x) (hxy : x ≠ y)
    (hmxy : M.Adj x y) :
    IsMatchingGraph
      ((M.deleteEdges ({s(x, y)} : Set (Sym2 V)) ⊔ SimpleGraph.edge u x) ⊔
        SimpleGraph.edge v y) := by
  have hu_iso : ∀ z, ¬M.Adj u z := fun z huz ↦ hu huz.mem_support_left
  have hv_iso : ∀ z, ¬M.Adj v z := fun z hvz ↦ hv hvz.mem_support_left
  have hx_only : ∀ {z}, M.Adj x z → z = y := fun {z} hxz ↦ hM x hxz hmxy
  have hy_only : ∀ {z}, M.Adj y z → z = x := fun {z} hyz ↦ hM y hyz hmxy.symm
  have hdeleted_xy : s(x, y) ∈ ({s(x, y)} : Set (Sym2 V)) := Set.mem_singleton _
  have hdeleted_yx : s(y, x) ∈ ({s(x, y)} : Set (Sym2 V)) := by
    rw [Set.mem_singleton_iff, Sym2.eq_swap]
  intro z a hza b hzb
  rw [SimpleGraph.mem_neighborSet] at hza hzb
  rw [SimpleGraph.sup_adj, SimpleGraph.sup_adj, SimpleGraph.deleteEdges_adj] at hza hzb
  rcases hza with (hza | hza) | hza <;> rcases hzb with (hzb | hzb) | hzb
  · exact hM z hza.1 hzb.1
  · rw [SimpleGraph.edge_adj] at hzb
    rcases hzb.1 with hzb | hzb
    · exact (hu_iso _ (hzb.1 ▸ hza.1)).elim
    · have ha : a = y := hx_only (hzb.1 ▸ hza.1)
      have hdel : s(z, a) ∈ ({s(x, y)} : Set (Sym2 V)) := by
        rw [hzb.1, ha]
        exact hdeleted_xy
      exact (hza.2 hdel).elim
  · rw [SimpleGraph.edge_adj] at hzb
    rcases hzb.1 with hzb | hzb
    · exact (hv_iso _ (hzb.1 ▸ hza.1)).elim
    · have ha : a = x := hy_only (hzb.1 ▸ hza.1)
      have hdel : s(z, a) ∈ ({s(x, y)} : Set (Sym2 V)) := by
        rw [hzb.1, ha]
        exact hdeleted_yx
      exact (hza.2 hdel).elim
  · rw [SimpleGraph.edge_adj] at hza
    rcases hza.1 with hza | hza
    · exact (hu_iso _ (hza.1 ▸ hzb.1)).elim
    · have hb : b = y := hx_only (hza.1 ▸ hzb.1)
      have hdel : s(z, b) ∈ ({s(x, y)} : Set (Sym2 V)) := by
        rw [hza.1, hb]
        exact hdeleted_xy
      exact (hzb.2 hdel).elim
  · exact edge_adj_neighbor_eq hza hzb
  · exact (disjoint_new_edges_not_both_adjacent huv huy hvx hxy hza hzb).elim
  · rw [SimpleGraph.edge_adj] at hza
    rcases hza.1 with hza | hza
    · exact (hv_iso _ (hza.1 ▸ hzb.1)).elim
    · have hb : b = x := hy_only (hza.1 ▸ hzb.1)
      have hdel : s(z, b) ∈ ({s(x, y)} : Set (Sym2 V)) := by
        rw [hza.1, hb]
        exact hdeleted_yx
      exact (hzb.2 hdel).elim
  · exact (disjoint_new_edges_not_both_adjacent huv huy hvx hxy hzb hza).elim
  · exact edge_adj_neighbor_eq hza hzb

private theorem ncard_edgeSet_sup_edge [Fintype V] {M : SimpleGraph V}
    {u v : V} (hn : ¬M.Adj u v) (huv : u ≠ v) :
    (M ⊔ SimpleGraph.edge u v).edgeSet.ncard = M.edgeSet.ncard + 1 := by
  classical
  have he : s(u, v) ∉ M.edgeSet := hn
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_edge_of_ne huv, Set.union_singleton,
    Set.ncard_insert_of_notMem he]

private theorem ncard_edgeSet_exchange [Fintype V] {M : SimpleGraph V}
    {u v x y : V} (hu : u ∉ M.support)
    (hv : v ∉ M.support) (huv : u ≠ v) (hux : u ≠ x)
    (hvx : v ≠ x) (hvy : v ≠ y) (hmxy : M.Adj x y) :
    ((M.deleteEdges ({s(x, y)} : Set (Sym2 V)) ⊔ SimpleGraph.edge u x) ⊔
        SimpleGraph.edge v y).edgeSet.ncard = M.edgeSet.ncard + 1 := by
  classical
  have hxyEdge : s(x, y) ∈ M.edgeSet := hmxy
  have huxEdge : s(u, x) ∉ M.edgeSet := by
    intro h
    change M.Adj u x at h
    exact hu h.mem_support_left
  have hvyEdge : s(v, y) ∉ M.edgeSet := by
    intro h
    change M.Adj v y at h
    exact hv h.mem_support_left
  have huxFresh : s(u, x) ∉ M.edgeSet \ {s(x, y)} := fun h ↦ huxEdge h.1
  have hvyFresh : s(v, y) ∉ insert s(u, x) (M.edgeSet \ {s(x, y)}) := by
    rw [Set.mem_insert_iff, not_or]
    constructor
    · rw [Sym2.eq_iff]
      grind
    · exact fun h ↦ hvyEdge h.1
  rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_sup,
    SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_edge_of_ne hux,
    SimpleGraph.edgeSet_edge_of_ne hvy, Set.union_singleton, Set.union_singleton,
    Set.ncard_insert_of_notMem hvyFresh, Set.ncard_insert_of_notMem huxFresh,
    Set.ncard_sdiff_singleton_add_one hxyEdge]

private theorem uncovered_neighbor_mem_support [Fintype V] {H M : SimpleGraph V}
    [DecidableRel H.Adj] [DecidableRel M.Adj]
    (hmax : M.IsExtremal (MatchingSubgraphOf H)) {u x : V}
    (hu : u ∉ M.support) (hux : H.Adj u x) : x ∈ M.support := by
  classical
  by_contra hx
  have hmx : ¬M.Adj u x := fun h ↦ hu h.mem_support_left
  have hcandidate : MatchingSubgraphOf H (M ⊔ SimpleGraph.edge u x) := by
    constructor
    · exact sup_le hmax.1.1 (edge_le_of_adj hux)
    · exact hmax.1.2.sup_edge_of_uncovered hu hx
  have hle : (M ⊔ SimpleGraph.edge u x).edgeSet.ncard ≤ M.edgeSet.ncard := by
    simpa only [edgeFinset_card_eq_edgeSet_ncard] using hmax.2 hcandidate
  have hcard : (M ⊔ SimpleGraph.edge u x).edgeSet.ncard = M.edgeSet.ncard + 1 :=
    ncard_edgeSet_sup_edge hmx hux.ne
  rw [hcard] at hle
  omega

private theorem no_length_three_augmenting_path [Fintype V]
    {H M : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel M.Adj]
    (hmax : M.IsExtremal (MatchingSubgraphOf H)) {u v x y : V}
    (hu : u ∉ M.support) (hv : v ∉ M.support) (huv : u ≠ v)
    (hux : H.Adj u x) (hvy : H.Adj v y) : ¬M.Adj x y := by
  classical
  intro hmxy
  have huy : u ≠ y := by
    intro huy
    apply hu
    simpa [huy] using hmxy.mem_support_right
  have hvx : v ≠ x := by
    intro hvx
    apply hv
    simpa [hvx] using hmxy.mem_support_left
  let M' :=
    (M.deleteEdges ({s(x, y)} : Set (Sym2 V)) ⊔ SimpleGraph.edge u x) ⊔
      SimpleGraph.edge v y
  have hcandidate : MatchingSubgraphOf H M' := by
    constructor
    · exact sup_le
        (sup_le ((SimpleGraph.deleteEdges_le (G := M) _).trans hmax.1.1)
          (edge_le_of_adj hux))
        (edge_le_of_adj hvy)
    · exact hmax.1.2.exchange hu hv huv huy hvx hmxy.ne hmxy
  have hle : M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
    simpa only [edgeFinset_card_eq_edgeSet_ncard] using hmax.2 hcandidate
  have hcard : M'.edgeSet.ncard = M.edgeSet.ncard + 1 := by
    exact ncard_edgeSet_exchange hu hv huv hux.ne hvx hvy.ne hmxy
  rw [hcard] at hle
  omega

private theorem edgeFinset_card_ge_of_extremal [Fintype V]
    {H M : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel M.Adj]
    (hmax : M.IsExtremal (MatchingSubgraphOf H)) (k : ℕ)
    (hdegree : ∀ v, k ≤ H.degree v) (horder : 2 * k ≤ Fintype.card V) :
    k ≤ #M.edgeFinset := by
  classical
  by_contra hmk
  have hmk' : #M.edgeFinset < k := Nat.lt_of_not_ge hmk
  have hsupport := hmax.1.2.card_support_eq_twice_card_edgeFinset
  let U := Finset.univ \ M.support.toFinset
  have hUcard : 1 < #U := by
    rw [show U = Finset.univ \ M.support.toFinset by rfl,
      Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hsupport]
    omega
  obtain ⟨u, huU, v, hvU, huv⟩ := Finset.one_lt_card.mp hUcard
  have hu : u ∉ M.support := by simpa [U] using huU
  have hv : v ∉ M.support := by simpa [U] using hvU
  let A := H.neighborFinset u
  let C := H.neighborFinset v
  let B := C.image (mate M)
  have hA_sub : A ⊆ M.support.toFinset := by
    intro x hx
    have hux : H.Adj u x := by simpa [A] using hx
    have hxs := uncovered_neighbor_mem_support hmax hu hux
    simpa using hxs
  have hB_sub : B ⊆ M.support.toFinset := by
    intro x hx
    obtain ⟨y, hyC, rfl⟩ := Finset.mem_image.mp hx
    have hvy : H.Adj v y := by simpa [C] using hyC
    have hys := uncovered_neighbor_mem_support hmax hv hvy
    simpa using mate_mem_support hys
  have hdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    obtain ⟨y, hyC, hyx⟩ := Finset.mem_image.mp hxB
    have hux : H.Adj u x := by simpa [A] using hxA
    have hvy : H.Adj v y := by simpa [C] using hyC
    have hys := uncovered_neighbor_mem_support hmax hv hvy
    have hmxy : M.Adj x y := by
      rw [← hyx]
      exact (adj_mate M hys).symm
    exact no_length_three_augmenting_path hmax hu hv huv hux hvy hmxy
  have hBcard : #B = #C := by
    exact Finset.card_image_of_injective C hmax.1.2.mate_injective
  have hdegreeSum : H.degree u + H.degree v ≤ 2 * #M.edgeFinset := by
    have hunion : #A + #C ≤ #M.support.toFinset := by
      calc
        #A + #C = #A + #B := by rw [hBcard]
        _ = #(A ∪ B) := (Finset.card_union_of_disjoint hdisjoint).symm
        _ ≤ #M.support.toFinset :=
          Finset.card_le_card (Finset.union_subset hA_sub hB_sub)
    simpa [A, C, hsupport] using hunion
  have hku := hdegree u
  have hkv := hdegree v
  omega

/-- If every vertex has degree at least `k` and the graph has at least `2 * k`
vertices, then it contains a matching with at least `k` edges. -/
theorem exists_matchingGraph_edgeFinset_card_ge [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hdegree : ∀ v, k ≤ H.degree v) (horder : 2 * k ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, ∃ _ : DecidableRel M.Adj,
      M ≤ H ∧ IsMatchingGraph M ∧ k ≤ #M.edgeFinset := by
  obtain ⟨M, instM, hmax⟩ :=
    (SimpleGraph.exists_isExtremal_iff_exists (MatchingSubgraphOf H)).mpr
      ⟨⊥, bot_le, isMatchingGraph_bot⟩
  letI : DecidableRel M.Adj := instM
  exact ⟨M, instM, hmax.1.1, hmax.1.2,
    edgeFinset_card_ge_of_extremal hmax k hdegree horder⟩

/-- Coverage form of `exists_matchingGraph_edgeFinset_card_ge`: the support of
the returned matching contains at least `2 * k` vertices. -/
theorem exists_matchingGraph_support_card_ge [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hdegree : ∀ v, k ≤ H.degree v) (horder : 2 * k ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, ∃ _ : DecidableRel M.Adj,
      M ≤ H ∧ IsMatchingGraph M ∧ 2 * k ≤ #M.support.toFinset := by
  obtain ⟨M, instM, hMH, hM, hcard⟩ :=
    exists_matchingGraph_edgeFinset_card_ge H k hdegree horder
  letI : DecidableRel M.Adj := instM
  refine ⟨M, instM, hMH, hM, ?_⟩
  rw [hM.card_support_eq_twice_card_edgeFinset]
  omega

end TotalColoring.MatchingLowerBound
