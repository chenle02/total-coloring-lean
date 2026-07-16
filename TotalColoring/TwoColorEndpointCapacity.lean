import TotalColoring.TwoColorGeometry
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Global endpoint capacity of a two-color component

The local geometry in `TwoColorGeometry` rules out branching at one vertex.
This module adds the global finite argument.  A genuine physical component is
projected to a graph whose vertices are exactly those met by the component.
Line-graph reachability makes that vertex graph connected, while validity
makes every vertex degree at most two.  The degree-sum formula and the
connected bound `|V| ≤ |E| + 1` then give at most two degree-one vertices.

No path/cycle classification is chosen, and no fan, criticality, or
distinguished-edge hypothesis is used.
-/

namespace TotalColoring

universe u v

open scoped BigOperators

/-- The graph on exactly the vertices met by an edge set.  Two such vertices
are adjacent when a common edge of the set witnesses their incidence. -/
def EdgeSetVertexGraph {V : Type u} {G : SimpleGraph V}
    (K : Set G.edgeSet) : SimpleGraph {v : V // EdgeSetMeetsVertex K v} where
  Adj p q := p ≠ q ∧ ∃ e, e ∈ K ∧ Incident p.1 e ∧ Incident q.1 e
  symm := ⟨by
    intro p q hpq
    refine ⟨hpq.1.symm, ?_⟩
    rcases hpq.2 with ⟨e, heK, hp, hq⟩
    exact ⟨e, heK, hq, hp⟩⟩
  loopless := ⟨by
    intro p hp
    exact hp.1 rfl⟩

noncomputable instance edgeSetVertexFintype {V : Type u} [Fintype V]
    {G : SimpleGraph V} (K : Set G.edgeSet) :
    Fintype {v : V // EdgeSetMeetsVertex K v} :=
  Fintype.ofFinite _

noncomputable instance edgeSetVertexGraphDecidableRel {V : Type u}
    {G : SimpleGraph V} (K : Set G.edgeSet) :
    DecidableRel (EdgeSetVertexGraph K).Adj :=
  Classical.decRel _

namespace EdgeSetVertexGraph

variable {V : Type u} {G : SimpleGraph V} {K : Set G.edgeSet}

theorem adj_iff {p q : {v : V // EdgeSetMeetsVertex K v}} :
    (EdgeSetVertexGraph K).Adj p q ↔
      p ≠ q ∧ ∃ e, e ∈ K ∧ Incident p.1 e ∧ Incident q.1 e :=
  Iff.rfl

private theorem val_eq_of_same_incident_edge
    {p q r : {v : V // EdgeSetMeetsVertex K v}} {e : G.edgeSet}
    (hpq : p ≠ q) (hpr : p ≠ r)
    (hp : Incident p.1 e) (hq : Incident q.1 e)
    (hr : Incident r.1 e) : q.1 = r.1 := by
  have hpqVal : p.1 ≠ q.1 := by
    intro h
    exact hpq (Subtype.ext h)
  have hprVal : p.1 ≠ r.1 := by
    intro h
    exact hpr (Subtype.ext h)
  have heqQ : (e : Sym2 V) = s(p.1, q.1) :=
    (Sym2.mem_and_mem_iff hpqVal).mp ⟨hp, hq⟩
  have heqR : (e : Sym2 V) = s(p.1, r.1) :=
    (Sym2.mem_and_mem_iff hprVal).mp ⟨hp, hr⟩
  exact Sym2.congr_right.mp (heqQ.symm.trans heqR)

private theorem reachable_of_same_edge
    {p q : {v : V // EdgeSetMeetsVertex K v}} {e : G.edgeSet}
    (heK : e ∈ K) (hp : Incident p.1 e) (hq : Incident q.1 e) :
    (EdgeSetVertexGraph K).Reachable p q := by
  by_cases hpq : p = q
  · subst q
    exact SimpleGraph.Reachable.rfl
  · exact (show (EdgeSetVertexGraph K).Adj p q from
      ⟨hpq, ⟨e, heK, hp, hq⟩⟩).reachable

end EdgeSetVertexGraph

namespace PartialEdgeAssignment

variable {V : Type u} {G : SimpleGraph V} {C : Type v}

/-- Any two edges in one genuine component are mutually reachable in the
supported two-color line graph. -/
theorem twoColorReachable_of_mem_of_mem_component
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {e f : G.edgeSet} (heK : e ∈ K) (hfK : f ∈ K) :
    a.TwoColorReachable alpha beta e f := by
  rcases hK with ⟨root, hroot, rfl⟩
  exact (a.twoColorReachable_symm alpha beta heK).trans hfK

/-- Genuine components for the same ordered color pair which share an edge
are equal. -/
theorem isTwoColorKempeComponent_eq_of_common_member
    (a : PartialEdgeAssignment G C) {alpha beta : C}
    {K L : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (hL : a.IsTwoColorKempeComponent alpha beta L)
    {e : G.edgeSet} (heK : e ∈ K) (heL : e ∈ L) : K = L := by
  apply Set.Subset.antisymm
  · intro f hfK
    rcases hL with ⟨root, hroot, hLdef⟩
    rw [hLdef] at heL ⊢
    exact heL.trans
      (twoColorReachable_of_mem_of_mem_component a hK heK hfK)
  · intro f hfL
    rcases hK with ⟨root, hroot, hKdef⟩
    rw [hKdef] at heK ⊢
    exact heK.trans
      (twoColorReachable_of_mem_of_mem_component a hL heL hfL)

/-- Reachability from a member of a genuine component stays inside that
component. -/
theorem mem_component_of_mem_of_twoColorReachable
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {e f : G.edgeSet} (heK : e ∈ K)
    (hef : a.TwoColorReachable alpha beta e f) : f ∈ K := by
  rcases hK with ⟨root, hroot, rfl⟩
  exact heK.trans hef

private theorem edgeSetVertexGraph_reachable_of_twoColorStep
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    {e f : G.edgeSet} (heK : e ∈ K) (hfK : f ∈ K)
    (hef : a.TwoColorStep alpha beta e f)
    {p q : {v : V // EdgeSetMeetsVertex K v}}
    (hp : Incident p.1 e) (hq : Incident q.1 f) :
    (EdgeSetVertexGraph K).Reachable p q := by
  rcases SimpleGraph.lineGraph_adj_iff_exists.mp hef.1 with
    ⟨_hefNe, x, hxe, hxf⟩
  let middle : {v : V // EdgeSetMeetsVertex K v} :=
    ⟨x, ⟨e, heK, hxe⟩⟩
  exact (EdgeSetVertexGraph.reachable_of_same_edge
      (q := middle) heK hp hxe).trans
    (EdgeSetVertexGraph.reachable_of_same_edge
      (p := middle) hfK hxf hq)

/-- Edge reachability in a genuine component projects to reachability between
arbitrary incident vertices in its vertex graph. -/
theorem edgeSetVertexGraph_reachable_of_twoColorReachable
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {e f : G.edgeSet} (heK : e ∈ K) (hfK : f ∈ K)
    (hef : a.TwoColorReachable alpha beta e f)
    {p q : {v : V // EdgeSetMeetsVertex K v}}
    (hp : Incident p.1 e) (hq : Incident q.1 f) :
    (EdgeSetVertexGraph K).Reachable p q := by
  induction hef using Relation.ReflTransGen.trans_induction_on generalizing p q with
  | refl =>
      exact EdgeSetVertexGraph.reachable_of_same_edge heK hp hq
  | single hstep =>
      exact edgeSetVertexGraph_reachable_of_twoColorStep
        a heK hfK hstep hp hq
  | @trans e middle f hem hmf ihm imf =>
      have hmiddleK : middle ∈ K :=
        mem_component_of_mem_of_twoColorReachable a hK heK hem
      obtain ⟨⟨x, y⟩, hxyG⟩ := middle
      let r : {v : V // EdgeSetMeetsVertex K v} :=
        ⟨x, ⟨⟨s(x, y), hxyG⟩, hmiddleK, Sym2.mem_mk_left x y⟩⟩
      exact (ihm (p := p) (q := r) heK hmiddleK hp
          (Sym2.mem_mk_left x y)).trans
        (imf (p := r) (q := q) hmiddleK hfK
          (Sym2.mem_mk_left x y) hq)

/-- The vertex graph of a genuine component is connected. -/
theorem edgeSetVertexGraph_connected
    (a : PartialEdgeAssignment G C) {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K) :
    (EdgeSetVertexGraph K).Connected := by
  rcases hK with ⟨root, hroot, hKroot⟩
  have hrootK : root ∈ K := by
    rw [hKroot]
    exact a.root_mem_twoColorReachabilityClass alpha beta root
  obtain ⟨⟨x, y⟩, hxyG⟩ := root
  let p : {v : V // EdgeSetMeetsVertex K v} :=
    ⟨x, ⟨⟨s(x, y), hxyG⟩, hrootK, Sym2.mem_mk_left x y⟩⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable _).2 ⟨p, ?_⟩
  intro q
  rcases q.2 with ⟨f, hfK, hqf⟩
  exact edgeSetVertexGraph_reachable_of_twoColorReachable a
    ⟨⟨s(x, y), hxyG⟩, hroot, hKroot⟩ hrootK hfK
      (twoColorReachable_of_mem_of_mem_component a
        ⟨⟨s(x, y), hxyG⟩, hroot, hKroot⟩ hrootK hfK)
      (Sym2.mem_mk_left x y) hqf

/-- Valid two-color geometry gives degree at most two in the component's
vertex graph. -/
theorem edgeSetVertexGraph_degree_le_two
    [Fintype V] [DecidableEq V]
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    (p : {v : V // EdgeSetMeetsVertex K v}) :
    (EdgeSetVertexGraph K).degree p ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 2 < ((EdgeSetVertexGraph K).neighborFinset p).card := by
    simpa [SimpleGraph.card_neighborFinset_eq_degree] using
      Nat.lt_of_not_ge hnot
  rcases Finset.two_lt_card_iff.mp hthree with
    ⟨q, r, s, hq, hr, hs, hqr, hqs, hrs⟩
  have hpq : (EdgeSetVertexGraph K).Adj p q := by simpa using hq
  have hpr : (EdgeSetVertexGraph K).Adj p r := by simpa using hr
  have hps : (EdgeSetVertexGraph K).Adj p s := by simpa using hs
  rcases hpq.2 with ⟨e, heK, hpe, hqe⟩
  rcases hpr.2 with ⟨f, hfK, hpf, hrf⟩
  rcases hps.2 with ⟨g, hgK, hpg, hsg⟩
  have hbranch := twoColorSupported_incident_edges_no_branch hvalid
    hpe hpf hpg
    (twoColorSupported_of_mem_component a hK heK)
    (twoColorSupported_of_mem_component a hK hfK)
    (twoColorSupported_of_mem_component a hK hgK)
  rcases hbranch with hef | heg | hfg
  · apply hqr
    apply Subtype.ext
    exact EdgeSetVertexGraph.val_eq_of_same_incident_edge
      hpq.1 hpr.1 hpe hqe (hef ▸ hrf)
  · apply hqs
    apply Subtype.ext
    exact EdgeSetVertexGraph.val_eq_of_same_incident_edge
      hpq.1 hps.1 hpe hqe (heg ▸ hsg)
  · apply hrs
    apply Subtype.ext
    exact EdgeSetVertexGraph.val_eq_of_same_incident_edge
      hpr.1 hps.1 hpf hrf (hfg ▸ hsg)

/-- A component endpoint becomes a degree-one vertex of the projected graph. -/
theorem edgeSetVertexGraph_degree_eq_one_of_endpoint
    [Fintype V] [DecidableEq V]
    {K : Set G.edgeSet} {v : V} (hend : EdgeSetIsEndpoint K v) :
    (EdgeSetVertexGraph K).degree
      (⟨v, ⟨hend.choose, hend.choose_spec.1, hend.choose_spec.2.1⟩⟩ :
        {v : V // EdgeSetMeetsVertex K v}) = 1 := by
  classical
  let p : {v : V // EdgeSetMeetsVertex K v} :=
    ⟨v, ⟨hend.choose, hend.choose_spec.1, hend.choose_spec.2.1⟩⟩
  rcases hend with ⟨e, heK, hve, hunique⟩
  rcases Sym2.mem_iff_exists.mp hve with ⟨w, heq⟩
  have hedge : s(v, w) ∈ G.edgeSet := by simpa [heq] using e.2
  have hadj : G.Adj v w := hedge
  have hvw : v ≠ w := hadj.ne
  have hwe : Incident w e := by
    change w ∈ (e : Sym2 V)
    rw [heq]
    exact Sym2.mem_mk_right v w
  let q : {v : V // EdgeSetMeetsVertex K v} := ⟨w, ⟨e, heK, hwe⟩⟩
  rw [SimpleGraph.degree_eq_one_iff_existsUnique_adj]
  refine ⟨q, ?_, ?_⟩
  · refine ⟨?_, ⟨e, heK, hve, hwe⟩⟩
    intro hpq
    exact hvw (congrArg Subtype.val hpq)
  · intro r hpr
    rcases hpr.2 with ⟨f, hfK, hvf, hrf⟩
    have hfe : f = e := hunique hfK hvf
    apply Subtype.ext
    exact EdgeSetVertexGraph.val_eq_of_same_incident_edge
      hpr.1 (show p ≠ q by
        intro hpq
        exact hvw (congrArg Subtype.val hpq))
      hvf hrf (hfe ▸ hwe)

end PartialEdgeAssignment

/-- A finite connected graph of maximum degree at most two has at most two
degree-one vertices. -/
theorem connected_degree_one_card_le_two
    {W : Type*} [Fintype W] (F : SimpleGraph W) [DecidableRel F.Adj]
    (hconn : F.Connected) (hdeg : ∀ w, F.degree w ≤ 2) :
    (Finset.univ.filter fun w => F.degree w = 1).card ≤ 2 := by
  let ends := Finset.univ.filter fun w => F.degree w = 1
  have hlocal (w : W) :
      F.degree w + (if F.degree w = 1 then 1 else 0) ≤ 2 := by
    have := hdeg w
    split_ifs <;> omega
  have hsum :
      (∑ w, F.degree w) + ends.card ≤ 2 * Fintype.card W := by
    calc
      (∑ w, F.degree w) + ends.card =
          ∑ w, (F.degree w + if F.degree w = 1 then 1 else 0) := by
            simp [ends, Finset.sum_add_distrib]
      _ ≤ ∑ _w : W, 2 := Finset.sum_le_sum fun _ _ => hlocal _
      _ = 2 * Fintype.card W := by simp [Nat.mul_comm]
  have hsum' :
      2 * F.edgeFinset.card + ends.card ≤ 2 * Fintype.card W := by
    rwa [F.sum_degrees_eq_twice_card_edges] at hsum
  have hconn' : Fintype.card W ≤ F.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  change ends.card ≤ 2
  omega

namespace PartialEdgeAssignment

/-- Three endpoints of one finite genuine component cannot be pairwise
distinct. -/
theorem endpoint_triple_has_repetition_of_component
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} {C : Type v}
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {x y z : V}
    (hx : EdgeSetIsEndpoint K x) (hy : EdgeSetIsEndpoint K y)
    (hz : EdgeSetIsEndpoint K z) :
    x = y ∨ x = z ∨ y = z := by
  classical
  by_contra hdistinct
  simp only [not_or] at hdistinct
  have hxy : x ≠ y := hdistinct.1
  have hxz : x ≠ z := hdistinct.2.1
  have hyz : y ≠ z := hdistinct.2.2
  let px : {w : V // EdgeSetMeetsVertex K w} :=
    ⟨x, ⟨hx.choose, hx.choose_spec.1, hx.choose_spec.2.1⟩⟩
  let py : {w : V // EdgeSetMeetsVertex K w} :=
    ⟨y, ⟨hy.choose, hy.choose_spec.1, hy.choose_spec.2.1⟩⟩
  let pz : {w : V // EdgeSetMeetsVertex K w} :=
    ⟨z, ⟨hz.choose, hz.choose_spec.1, hz.choose_spec.2.1⟩⟩
  let F := EdgeSetVertexGraph K
  have hcard := connected_degree_one_card_le_two F
    (edgeSetVertexGraph_connected a hK)
    (edgeSetVertexGraph_degree_le_two hvalid hK)
  apply (Nat.not_lt_of_ge hcard)
  apply Finset.two_lt_card_iff.mpr
  refine ⟨px, py, pz, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact edgeSetVertexGraph_degree_eq_one_of_endpoint hx
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact edgeSetVertexGraph_degree_eq_one_of_endpoint hy
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact edgeSetVertexGraph_degree_eq_one_of_endpoint hz
  · intro h
    exact hxy (congrArg Subtype.val h)
  · intro h
    exact hxz (congrArg Subtype.val h)
  · intro h
    exact hyz (congrArg Subtype.val h)

/-- The endpoint set of a finite genuine two-color component has cardinality
at most two. -/
theorem edgeSetIsEndpoint_ncard_le_two_of_component
    {V : Type u} [Fintype V]
    {G : SimpleGraph V} {C : Type v}
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K) :
    ({w : V | EdgeSetIsEndpoint K w} : Set V).ncard ≤ 2 := by
  classical
  by_contra hnot
  have hthree : 2 < ({w : V | EdgeSetIsEndpoint K w} : Set V).ncard :=
    Nat.lt_of_not_ge hnot
  rcases (Set.two_lt_ncard_iff
      (s := {w : V | EdgeSetIsEndpoint K w})).mp hthree with
    ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩
  rcases endpoint_triple_has_repetition_of_component hvalid hK hx hy hz with
    h | h | h
  · exact hxy h
  · exact hxz h
  · exact hyz h

end PartialEdgeAssignment

end TotalColoring
