import TotalColoring.AuxiliaryTransfer
import TotalColoring.PairSingletonExtension
import Mathlib.Order.Partition.Equipartition

/-!
# Equitable pair/singleton partitions

This module fills the supplied-partition side of the concrete auxiliary
construction.  Its input is an equitable partition into exactly `D` nonempty
independent classes.  Under the explicit numerical hypotheses

* `D ≤ |V|`, and
* `|V| < 2 * D`,

every class has size one or two.  Choosing the unique other member of each
two-element class produces a `PairSingletonWitness`.  The exact singleton and
pair counts then give the exact distinguished-edge count required by the
auxiliary class.

The module deliberately does not prove that the supplied equitable independent
partition exists.  In particular, it contains neither an equitable-coloring
theorem nor a complement-matching existence theorem.  Its high-degree
specialization assumes a nonempty vertex type; the empty graph is a separate
base case because the numerical density inequality alone also holds at order
zero, while a partition into one nonempty class cannot then be supplied.
-/

namespace TotalColoring.Auxiliary

universe u

variable {V : Type u} {G : SimpleGraph V} {D : ℕ}

/-- A partition of all vertices into exactly `D` nonempty independent classes,
with class sizes differing by at most one. -/
structure EquitableIndependentPartition (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] (D : ℕ) where
  classes : Finpartition (Finset.univ : Finset V)
  independent : ∀ c ∈ classes.parts, G.IsIndepSet (c : Set V)
  equitable : classes.IsEquipartition
  card_classes : classes.parts.card = D

namespace EquitableIndependentPartition

variable [Fintype V] [DecidableEq V]

/-- The classes consisting of one vertex. -/
def singletonClasses (Q : EquitableIndependentPartition G D) :
    Finset (Finset V) :=
  Q.classes.parts.filter fun c ↦ c.card = 1

/-- The classes consisting of two vertices. -/
def pairClasses (Q : EquitableIndependentPartition G D) :
    Finset (Finset V) :=
  Q.classes.parts.filter fun c ↦ c.card = 2

/-- In the pair/singleton range, the average class size is one. -/
theorem average_eq_one (_Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) :
    Fintype.card V / D = 1 := by
  exact Nat.div_eq_of_lt_le (by simpa using hDle) (by simpa using hnlt)

/-- Every class in an equitable `D`-partition has size one or two when
`D ≤ |V| < 2D`. -/
theorem class_card_eq_one_or_two
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D)
    {c : Finset V} (hc : c ∈ Q.classes.parts) :
    c.card = 1 ∨ c.card = 2 := by
  simpa [Q.card_classes, Q.average_eq_one hDle hnlt] using
    Q.equitable.card_parts_eq_average hc

/-- A two-element class has a unique member different from a fixed member. -/
private theorem existsUnique_other_of_card_eq_two
    (Q : EquitableIndependentPartition G D) (v : V)
    (hcard : (Q.classes.part v).card = 2) :
    ∃! w, w ∈ Q.classes.part v ∧ w ≠ v := by
  have hv : v ∈ Q.classes.part v := by simp
  have herase : ((Q.classes.part v).erase v).card = 1 := by
    rw [Finset.card_erase_of_mem hv, hcard]
  have hUnique : ∃! w, w ∈ (Q.classes.part v).erase v :=
    Finset.card_eq_one_iff_existsUnique.mp herase
  simpa [Finset.mem_erase, and_comm, and_left_comm, and_assoc] using hUnique

/-- The partner selected by the source partition.  A two-element class chooses
its unique other member; every other class chooses no partner. -/
noncomputable def partner (Q : EquitableIndependentPartition G D) (v : V) :
    Option V :=
  if hcard : (Q.classes.part v).card = 2 then
    some (existsUnique_other_of_card_eq_two Q v hcard).choose
  else
    none

/-- Normal form for the selected partner. -/
theorem partner_eq_some_iff
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D)
    {v w : V} :
    Q.partner v = some w ↔ w ∈ Q.classes.part v ∧ w ≠ v := by
  rw [partner]
  split_ifs with hcard
  · let hUnique := existsUnique_other_of_card_eq_two Q v hcard
    have hchosen : hUnique.choose ∈ Q.classes.part v ∧
        hUnique.choose ≠ v := hUnique.choose_spec.1
    constructor
    · intro h
      have heq : hUnique.choose = w := Option.some.inj h
      subst w
      exact hchosen
    · intro hw
      exact congrArg some (hUnique.unique hchosen hw)
  · constructor
    · intro h
      cases h
    · rintro ⟨hw, hwne⟩
      exfalso
      apply hcard
      rcases Q.class_card_eq_one_or_two hDle hnlt (c := Q.classes.part v)
          (by simp) with hone | htwo
      · have hwv : w = v :=
          (Finset.card_le_one.mp hone.le) w hw v (by simp)
        exact (hwne hwv).elim
      · exact htwo

/-- A vertex has no partner exactly when its source class is a singleton. -/
theorem partner_eq_none_iff
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D)
    (v : V) :
    Q.partner v = none ↔ (Q.classes.part v).card = 1 := by
  rw [partner]
  split_ifs with hcard
  · constructor
    · intro h
      cases h
    · intro hone
      omega
  · constructor
    · intro _
      exact (Q.class_card_eq_one_or_two hDle hnlt
        (c := Q.classes.part v) (by simp)).resolve_right hcard
    · intro _
      rfl

/-- The pair/singleton witness induced by a supplied equitable independent
partition in the range `D ≤ |V| < 2D`. -/
noncomputable def toPairSingletonWitness
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) :
    PairSingletonWitness G where
  partner := Q.partner
  partner_ne := by
    intro v w hpartner
    exact ((Q.partner_eq_some_iff hDle hnlt).mp hpartner).2.symm
  partner_symm := by
    intro v w hpartner
    have hvw := (Q.partner_eq_some_iff hDle hnlt).mp hpartner
    have hparts : Q.classes.part w = Q.classes.part v :=
      (Q.classes.mem_part_iff_part_eq_part (a := w) (b := v)
        (by simp) (by simp)).mp hvw.1
    apply (Q.partner_eq_some_iff hDle hnlt).mpr
    refine ⟨?_, hvw.2.symm⟩
    rw [hparts]
    simp
  partner_nonadjacent := by
    intro v w hpartner
    have hvw := (Q.partner_eq_some_iff hDle hnlt).mp hpartner
    exact (Q.independent (Q.classes.part v) (by simp))
      (by simp) hvw.1 hvw.2.symm

@[simp]
theorem toPairSingletonWitness_partner
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) (v : V) :
    (Q.toPairSingletonWitness hDle hnlt).partner v = Q.partner v :=
  rfl

/-- The exact number of pair classes. -/
theorem pairClasses_card
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) :
    Q.pairClasses.card = Fintype.card V - D := by
  have havg := Q.average_eq_one hDle hnlt
  have hlarge : Q.pairClasses.card = Fintype.card V % D := by
    simpa [pairClasses, Q.card_classes, havg] using
      Q.equitable.card_large_parts_eq_mod
  have hdecomp : D + Fintype.card V % D = Fintype.card V := by
    simpa [havg] using Nat.div_add_mod (Fintype.card V) D
  omega

/-- The exact number of singleton classes. -/
theorem singletonClasses_card
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) :
    Q.singletonClasses.card = 2 * D - Fintype.card V := by
  have havg := Q.average_eq_one hDle hnlt
  have hsmall : Q.singletonClasses.card = D - Fintype.card V % D := by
    simpa [singletonClasses, Q.card_classes, havg] using
      Q.equitable.card_small_parts_eq_mod
  have hdecomp : D + Fintype.card V % D = Fintype.card V := by
    simpa [havg] using Nat.div_add_mod (Fintype.card V) D
  omega

/-- Singleton vertices of the induced witness are in bijection with singleton
classes of the supplied partition. -/
theorem singletonVertices_card_eq_singletonClasses_card
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) :
    (Q.toPairSingletonWitness hDle hnlt).singletonVertices.card =
      Q.singletonClasses.card := by
  let P := Q.toPairSingletonWitness hDle hnlt
  change P.singletonVertices.card = Q.singletonClasses.card
  apply Finset.card_nbij (fun v ↦ Q.classes.part v)
  · intro v hv
    have hvnone := P.mem_singletonVertices.mp hv
    change Q.partner v = none at hvnone
    have hvone := (Q.partner_eq_none_iff hDle hnlt v).mp hvnone
    simp [singletonClasses, hvone]
  · intro v hv w hw heq
    have hvnone := P.mem_singletonVertices.mp hv
    change Q.partner v = none at hvnone
    have hvone := (Q.partner_eq_none_iff hDle hnlt v).mp hvnone
    apply (Finset.card_le_one.mp hvone.le) v (by simp) w
    exact (Q.classes.mem_part_iff_part_eq_part (a := w) (b := v)
      (by simp) (by simp)).mpr heq.symm
  · intro c hc
    have hc' := Finset.mem_filter.mp hc
    obtain ⟨v, hvc⟩ := Q.classes.nonempty_of_mem_parts hc'.1
    have hvpart : Q.classes.part v = c :=
      Q.classes.part_eq_of_mem hc'.1 hvc
    refine ⟨v, ?_, hvpart⟩
    apply P.mem_singletonVertices.mpr
    change Q.partner v = none
    apply (Q.partner_eq_none_iff hDle hnlt v).mpr
    simpa [hvpart] using hc'.2

/-- The exact singleton count for the induced witness. -/
theorem singletonVertices_card
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) :
    (Q.toPairSingletonWitness hDle hnlt).singletonVertices.card =
      2 * D - Fintype.card V := by
  rw [Q.singletonVertices_card_eq_singletonClasses_card hDle hnlt,
    Q.singletonClasses_card hDle hnlt]

/-- The induced distinguished selector family has exactly one member for each
source class. -/
theorem distinguished_card
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D) :
    (Q.toPairSingletonWitness hDle hnlt).distinguished.card = D := by
  let P := Q.toPairSingletonWitness hDle hnlt
  have horbit := P.card_add_singletonVertices_card_eq_two_mul_distinguished_card
  have hsingle : P.singletonVertices.card = 2 * D - Fintype.card V := by
    simpa [P] using Q.singletonVertices_card hDle hnlt
  change P.distinguished.card = D
  omega

/-- Exact center degree inherited from the exact singleton count. -/
theorem auxiliaryGraph_degree_none
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D)
    [DecidableRel
      (Q.toPairSingletonWitness hDle hnlt).auxiliaryGraph.Adj] :
    (Q.toPairSingletonWitness hDle hnlt).auxiliaryGraph.degree none =
      2 * D - Fintype.card V := by
  rw [(Q.toPairSingletonWitness hDle hnlt).degree_none_eq_singletonVertices_card,
    Q.singletonVertices_card hDle hnlt]

/-- The supplied partition and ordinary numerical bounds produce a concrete
member of the structural auxiliary class. -/
theorem isAuxiliaryClassMember_of_bounds
    (Q : EquitableIndependentPartition G D)
    (hDle : D ≤ Fintype.card V)
    (hnlt : Fintype.card V < 2 * D)
    [DecidableRel G.Adj]
    (hG : G.maxDegree + 1 ≤ D)
    (horder : Fintype.card V + 2 ≤ 2 * D) :
    let P := Q.toPairSingletonWitness hDle hnlt
    letI : DecidableRel P.auxiliaryGraph.Adj := Classical.decRel _
    IsAuxiliaryClassMember D P.auxiliaryGraph none P.distinguished
      P.matchingPart := by
  classical
  dsimp only
  let P := Q.toPairSingletonWitness hDle hnlt
  letI : DecidableRel P.auxiliaryGraph.Adj := Classical.decRel _
  exact P.isAuxiliaryClassMember_of_class_count_and_bounds D
    (Q.distinguished_card hDle hnlt) hG horder

section HighDegree

variable [Nonempty V] [DecidableRel G.Adj]

omit [DecidableEq V] in
/-- The parameter `maxDegree + 1` does not exceed the order of a nonempty
finite graph. -/
theorem maxDegree_add_one_le_card :
    G.maxDegree + 1 ≤ Fintype.card V := by
  have hmax := G.maxDegree_lt_card_verts
  omega

omit [DecidableEq V] [Nonempty V] in
/-- The half-order hypothesis places the graph strictly below twice the
parameter `maxDegree + 1`. -/
theorem card_lt_two_mul_maxDegree_add_one
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    Fintype.card V < 2 * (G.maxDegree + 1) := by
  omega

/-- The pair/singleton witness obtained from a supplied high-degree equitable
independent partition. -/
noncomputable def highDegreeWitness
    (Q : EquitableIndependentPartition G (G.maxDegree + 1))
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    PairSingletonWitness G :=
  Q.toPairSingletonWitness maxDegree_add_one_le_card
    (card_lt_two_mul_maxDegree_add_one hdense)

@[simp]
theorem highDegreeWitness_partner
    (Q : EquitableIndependentPartition G (G.maxDegree + 1))
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) (v : V) :
    (Q.highDegreeWitness hdense).partner v = Q.partner v :=
  rfl

/-- Exact distinguished cardinality in the high-degree specialization. -/
theorem highDegreeWitness_distinguished_card
    (Q : EquitableIndependentPartition G (G.maxDegree + 1))
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    (Q.highDegreeWitness hdense).distinguished.card = G.maxDegree + 1 := by
  simpa [highDegreeWitness] using
    Q.distinguished_card maxDegree_add_one_le_card
      (card_lt_two_mul_maxDegree_add_one hdense)

/-- The supplied high-degree partition produces the full structural witness
required by the auxiliary theorem. -/
theorem highDegreeWitness_isAuxiliaryClassMember
    (Q : EquitableIndependentPartition G (G.maxDegree + 1))
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    let P := Q.highDegreeWitness hdense
    letI : DecidableRel P.auxiliaryGraph.Adj := Classical.decRel _
    IsAuxiliaryClassMember (G.maxDegree + 1) P.auxiliaryGraph none
      P.distinguished P.matchingPart := by
  classical
  dsimp only
  let P := Q.highDegreeWitness hdense
  letI : DecidableRel P.auxiliaryGraph.Adj := Classical.decRel _
  exact P.isAuxiliaryClassMember_of_highDegree
    (Q.highDegreeWitness_distinguished_card hdense) hdense

/-- Pair-level auxiliary-class membership from the supplied partition. -/
theorem highDegreeWitness_inAuxiliaryClass
    (Q : EquitableIndependentPartition G (G.maxDegree + 1))
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    let P := Q.highDegreeWitness hdense
    letI : DecidableRel P.auxiliaryGraph.Adj := Classical.decRel _
    InAuxiliaryClass (G.maxDegree + 1) P.auxiliaryGraph P.distinguished := by
  classical
  dsimp only
  exact ⟨none, (Q.highDegreeWitness hdense).matchingPart,
    Q.highDegreeWitness_isAuxiliaryClassMember hdense⟩

/-- Conditional terminal decoding theorem for a supplied high-degree
equitable independent partition.  The result uses exactly the extension
palette attached to the auxiliary parameter `maxDegree + 1`.

This theorem does not assert existence of the supplied partition. -/
theorem exists_valid_assignment_of_highDegreePartition
    (Q : EquitableIndependentPartition G (G.maxDegree + 1))
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ assignment : Assignment G (ExtensionPalette (G.maxDegree + 1)),
      assignment.Valid := by
  classical
  let P := Q.highDegreeWitness hdense
  letI : DecidableRel P.auxiliaryGraph.Adj := Classical.decRel _
  apply Extension.exists_valid_decode_of_inAuxiliaryClass
    (G.maxDegree + 1) P.extension P.distinguished
  · intro v
    exact P.classEdge_mem_distinguishedEdgeSet v
  · exact ⟨none, P.matchingPart,
      Q.highDegreeWitness_isAuxiliaryClassMember hdense⟩

end HighDegree

end EquitableIndependentPartition

end TotalColoring.Auxiliary
