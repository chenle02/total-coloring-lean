import TotalColoring.TwoColorEndpointCapacity

/-!
# Path structure and bridge sides of a finite two-color component

`TwoColorEndpointCapacity` projects a genuine physical two-color component to
the graph on the vertices met by that component.  It proves that this vertex
graph is connected and has maximum degree at most two, and that every physical
endpoint has degree one in the projection.

This module records the next global geometric consequence.  A finite connected
graph of maximum degree at most two which has a degree-one vertex is a tree.
Consequently, a finite genuine two-color component with an endpoint is
path-like: its projected graph has a unique path between any two vertices and
every projected edge is a bridge.

For later pivot arguments, `DeletedEdgeSide F p q` orients the cut made by
deleting the edge `pq`: it is the set reachable from `q` after that deletion.
For a bridge, the side contains `q`, omits `p`, and its only possible boundary
edge in `F` is `pq`.  This is the graph-theoretic detachment statement; no fan,
root pivot, recoloring, or distinguished-edge claim is made here.
-/

namespace TotalColoring

universe u v

open scoped BigOperators

/-- A finite connected graph of maximum degree at most two with a degree-one
vertex is a tree. -/
theorem connected_degree_le_two_isTree_of_degree_eq_one
    {W : Type*} [Fintype W] (F : SimpleGraph W) [DecidableRel F.Adj]
    (hconn : F.Connected) (hdeg : ∀ w, F.degree w ≤ 2)
    {endpoint : W} (hendpoint : F.degree endpoint = 1) :
    F.IsTree := by
  classical
  have hlocal (w : W) :
      F.degree w + (if w = endpoint then 1 else 0) ≤ 2 := by
    by_cases hw : w = endpoint
    · subst w
      simp [hendpoint]
    · simpa [hw] using hdeg w
  have hsum :
      (∑ w, F.degree w) + 1 ≤ 2 * Fintype.card W := by
    calc
      (∑ w, F.degree w) + 1 =
          ∑ w, (F.degree w + if w = endpoint then 1 else 0) := by
            rw [Finset.sum_add_distrib]
            simp
      _ ≤ ∑ _w : W, 2 :=
        Finset.sum_le_sum fun _ _ ↦ hlocal _
      _ = 2 * Fintype.card W := by simp [Nat.mul_comm]
  have hedge_lt : F.edgeFinset.card < Fintype.card W := by
    rw [F.sum_degrees_eq_twice_card_edges] at hsum
    omega
  have hconn_card : Fintype.card W ≤ F.edgeFinset.card + 1 := by
    simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using
      hconn.card_vert_le_card_edgeSet_add_one
  have hcard : F.edgeFinset.card + 1 = Fintype.card W := by
    omega
  apply (SimpleGraph.isTree_iff_connected_and_card).2
  refine ⟨hconn, ?_⟩
  simpa [Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card] using hcard

/-- The projected vertex graph of a finite genuine two-color component is a
tree as soon as one physical endpoint is supplied. -/
theorem PartialEdgeAssignment.edgeSetVertexGraph_isTree_of_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Type v}
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {endpoint : V} (hendpoint : EdgeSetIsEndpoint K endpoint) :
    (EdgeSetVertexGraph K).IsTree := by
  let p : {w : V // EdgeSetMeetsVertex K w} :=
    ⟨endpoint, ⟨hendpoint.choose, hendpoint.choose_spec.1,
      hendpoint.choose_spec.2.1⟩⟩
  apply connected_degree_le_two_isTree_of_degree_eq_one
    (EdgeSetVertexGraph K)
    (PartialEdgeAssignment.edgeSetVertexGraph_connected a hK)
    (PartialEdgeAssignment.edgeSetVertexGraph_degree_le_two hvalid hK)
    (endpoint := p)
  exact PartialEdgeAssignment.edgeSetVertexGraph_degree_eq_one_of_endpoint
    hendpoint

/-- Path-like form: between any two met vertices of a finite genuine
component with an endpoint there is a unique projected path. -/
theorem PartialEdgeAssignment.edgeSetVertexGraph_existsUnique_path_of_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Type v}
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {endpoint : V} (hendpoint : EdgeSetIsEndpoint K endpoint)
    (p q : {w : V // EdgeSetMeetsVertex K w}) :
    ∃! path : (EdgeSetVertexGraph K).Walk p q, path.IsPath :=
  (PartialEdgeAssignment.edgeSetVertexGraph_isTree_of_endpoint
    hvalid hK hendpoint).existsUnique_path p q

/-- Every projected edge of a finite genuine component with an endpoint is a
bridge. -/
theorem PartialEdgeAssignment.edgeSetVertexGraph_isBridge_of_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Type v}
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {endpoint : V} (hendpoint : EdgeSetIsEndpoint K endpoint)
    {p q : {w : V // EdgeSetMeetsVertex K w}}
    (hpq : (EdgeSetVertexGraph K).Adj p q) :
    (EdgeSetVertexGraph K).IsBridge s(p, q) := by
  exact SimpleGraph.isAcyclic_iff_forall_adj_isBridge.mp
    (PartialEdgeAssignment.edgeSetVertexGraph_isTree_of_endpoint
      hvalid hK hendpoint).isAcyclic hpq

/-- Deleting any projected edge of a finite genuine component with an
endpoint separates that edge's two endpoints. -/
theorem PartialEdgeAssignment.edgeSetVertexGraph_not_reachable_deleteEdge_of_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Type v}
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {endpoint : V} (hendpoint : EdgeSetIsEndpoint K endpoint)
    {p q : {w : V // EdgeSetMeetsVertex K w}}
    (hpq : (EdgeSetVertexGraph K).Adj p q) :
    ¬((EdgeSetVertexGraph K).deleteEdges {s(p, q)}).Reachable p q := by
  exact SimpleGraph.isBridge_iff.mp
    (PartialEdgeAssignment.edgeSetVertexGraph_isBridge_of_endpoint
      hvalid hK hendpoint hpq)

/-- The side of an oriented deleted edge which contains its second endpoint. -/
def DeletedEdgeSide {W : Type*} (F : SimpleGraph W) (p q : W) : Set W :=
  {w | (F.deleteEdges {s(p, q)}).Reachable q w}

@[simp]
theorem right_mem_deletedEdgeSide {W : Type*} (F : SimpleGraph W) (p q : W) :
    q ∈ DeletedEdgeSide F p q := by
  exact SimpleGraph.Reachable.rfl

/-- If `pq` is a bridge, the side oriented from `q` omits `p`. -/
theorem left_not_mem_deletedEdgeSide_of_isBridge
    {W : Type*} {F : SimpleGraph W} {p q : W}
    (hbridge : F.IsBridge s(p, q)) :
    p ∉ DeletedEdgeSide F p q := by
  intro hqp
  change (F.deleteEdges {s(p, q)}).Reachable q p at hqp
  exact SimpleGraph.isBridge_iff.mp hbridge
    (SimpleGraph.reachable_comm.mpr hqp)

/-- The deleted-edge side is closed across every surviving edge. -/
theorem mem_deletedEdgeSide_of_mem_of_adj_of_edge_ne
    {W : Type*} {F : SimpleGraph W} {p q x y : W}
    (hx : x ∈ DeletedEdgeSide F p q) (hxy : F.Adj x y)
    (hne : s(x, y) ≠ s(p, q)) :
    y ∈ DeletedEdgeSide F p q := by
  change (F.deleteEdges {s(p, q)}).Reachable q x at hx
  change (F.deleteEdges {s(p, q)}).Reachable q y
  exact hx.trans
    (SimpleGraph.deleteEdges_adj.mpr ⟨hxy, by simpa using hne⟩).reachable

/-- Every edge leaving an oriented deleted-edge side is the deleted edge
itself. -/
theorem edge_eq_of_mem_deletedEdgeSide_of_not_mem
    {W : Type*} {F : SimpleGraph W} {p q x y : W}
    (hx : x ∈ DeletedEdgeSide F p q)
    (hy : y ∉ DeletedEdgeSide F p q) (hxy : F.Adj x y) :
    s(x, y) = s(p, q) := by
  by_contra hne
  exact hy (mem_deletedEdgeSide_of_mem_of_adj_of_edge_ne hx hxy hne)

/-- Exact detachment package for a projected edge of a finite genuine
two-color component with an endpoint.  After deleting `pq`, the `q`-side
contains `q`, omits `p`, and has no other boundary edge. -/
theorem PartialEdgeAssignment.edgeSetVertexGraph_detachedSide_of_endpoint
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {C : Type v}
    {a : PartialEdgeAssignment G C} (hvalid : a.Valid)
    {alpha beta : C} {K : Set G.edgeSet}
    (hK : a.IsTwoColorKempeComponent alpha beta K)
    {endpoint : V} (hendpoint : EdgeSetIsEndpoint K endpoint)
    {p q : {w : V // EdgeSetMeetsVertex K w}}
    (hpq : (EdgeSetVertexGraph K).Adj p q) :
    q ∈ DeletedEdgeSide (EdgeSetVertexGraph K) p q ∧
      p ∉ DeletedEdgeSide (EdgeSetVertexGraph K) p q ∧
      ∀ {x y},
        x ∈ DeletedEdgeSide (EdgeSetVertexGraph K) p q →
        y ∉ DeletedEdgeSide (EdgeSetVertexGraph K) p q →
        (EdgeSetVertexGraph K).Adj x y → s(x, y) = s(p, q) := by
  have hbridge : (EdgeSetVertexGraph K).IsBridge s(p, q) :=
    PartialEdgeAssignment.edgeSetVertexGraph_isBridge_of_endpoint
      hvalid hK hendpoint hpq
  refine ⟨right_mem_deletedEdgeSide (EdgeSetVertexGraph K) p q,
    left_not_mem_deletedEdgeSide_of_isBridge hbridge, ?_⟩
  intro x y hx hy hxy
  exact edge_eq_of_mem_deletedEdgeSide_of_not_mem hx hy hxy

end TotalColoring
