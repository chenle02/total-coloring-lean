# Curated theorem index

This is a small map of public entrypoints, not an exhaustive inventory of
internal lemmas.

## Package terminal theorem

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.exists_valid_assignment_of_highDegree` | `HighDegreeTotalColoring` | Every finite `G` with `Fintype.card V <= 2 * G.maxDegree` has a valid assignment in `ExtensionPalette (G.maxDegree + 1)`; empty and nonempty vertex types are included |
| `TotalColoring.Auxiliary.exists_valid_assignment_of_highDegree_nonempty` | `HighDegreeTotalColoring` | Nonempty specialization using the complement-matching witness and auxiliary decoder |
| `TotalColoring.exists_valid_assignment_of_isEmpty` | `EmptyAssignment` | Every graph on an empty vertex type has a valid assignment for any color type |

`ExtensionPalette (G.maxDegree + 1)` is definitionally
`Fin (G.maxDegree + 3)`. No parity hypothesis appears in the terminal theorem.

The exact proof-development tree
`4624044788ab42c0dc116cfbf7f38c696065263c` passed five separate high-memory
full/Quickstart/`leanchecker` jobs, `5388311` through `5388315`. That is a
receipt for the named proof tree, not yet for a later publication tree.

## Matching construction

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.MatchingLowerBound.IsMatchingGraph` | `MatchingLowerBound` | A spanning graph whose neighbor set at every vertex is subsingleton |
| `TotalColoring.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_ge` | `MatchingLowerBound` | Produces a matching with at least `k` edges from minimum-degree and order bounds |
| `TotalColoring.MatchingLowerBound.IsMatchingGraph.exists_subgraph_edgeFinset_card_eq` | `MatchingExact` | Trims a matching to any prescribed smaller edge count |
| `TotalColoring.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_eq` | `MatchingExact` | Exact-cardinality form of the general matching lower bound |
| `TotalColoring.MatchingLowerBound.card_sub_maxDegree_add_one_le_degree_compl` | `HighDegreeComplementMatching` | Gives the required lower bound on every complement degree |
| `TotalColoring.MatchingLowerBound.twice_card_sub_maxDegree_add_one_le_card` | `HighDegreeComplementMatching` | Derives the matching order bound from the high-degree hypothesis |
| `TotalColoring.MatchingLowerBound.exists_complement_matchingGraph_edgeFinset_card_ge` | `HighDegreeComplementMatching` | Produces a sufficiently large matching in the complement |
| `TotalColoring.MatchingLowerBound.exists_complement_matchingGraph_edgeFinset_card_eq` | `HighDegreeTotalColoring` | Produces the exact complement matching needed for the class count |

## Complement-matching adapter

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.Auxiliary.PairSingletonWitness.ofComplementMatching` | `ComplementMatchingWitness` | Converts a matching subgraph of the complement into a pair/singleton witness |
| `TotalColoring.Auxiliary.PairSingletonWitness.ofComplementMatching_partner_eq_some_iff` | `ComplementMatchingWitness` | Identifies selected partners with matching adjacency |
| `TotalColoring.Auxiliary.PairSingletonWitness.ofComplementMatching_singletonVertices` | `ComplementMatchingWitness` | Identifies singleton vertices with the complement of the matching support |
| `TotalColoring.Auxiliary.PairSingletonWitness.ofComplementMatching_distinguished_card_eq_card_sub` | `ComplementMatchingWitness` | Relates the distinguished count to the complement matching edge count |
| `TotalColoring.Auxiliary.PairSingletonWitness.ofComplementMatching_distinguished_card` | `ComplementMatchingWitness` | Produces an exact prescribed distinguished count from an exact matching count |
| `TotalColoring.Auxiliary.exists_pairSingletonWitness_of_highDegree` | `HighDegreeTotalColoring` | Packages a high-degree witness with `P.distinguished.card = G.maxDegree + 1` |

## Core predicates

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.InAuxiliaryClass` | `AuxiliaryClass` | Pair-level structural predicate for the matching-plus-star class |
| `TotalColoring.ExtensionPalette` | `CriticalState` | The auxiliary palette `Fin (D + 2)` |
| `TotalColoring.HasValidRainbowColoring` | `CriticalState` | Existence of a proper auxiliary edge coloring rainbow on `J` |
| `TotalColoring.Auxiliary.Extension` | `Auxiliary` | Conflict-preserving data for decoding auxiliary edge colors to a total assignment |

## Supplied pair/singleton interface

These declarations remain public for downstream developments that already
have a pair/singleton witness.

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.Auxiliary.PairSingletonWitness` | `PairSingletonExtension` | A fixed partition relation into independent singleton and pair classes |
| `TotalColoring.Auxiliary.PairSingletonWitness.auxiliaryGraph` | `PairSingletonExtension` | The ordinary auxiliary graph on `Option V` |
| `TotalColoring.Auxiliary.PairSingletonWitness.extension` | `PairSingletonExtension` | The conflict-preserving extension into the auxiliary graph |
| `TotalColoring.Auxiliary.PairSingletonWitness.classEdge_mem_distinguishedEdgeSet` | `PairSingletonExtension` | Every decoder selector belongs to the distinguished edge set |
| `TotalColoring.Auxiliary.PairSingletonWitness.distinguished_exact_coverage` | `PairSingletonExtension` | Every copied original vertex lies on exactly one distinguished edge |
| `TotalColoring.Auxiliary.PairSingletonWitness.matchingPart_isEdgeMatching` | `PairSingletonExtension` | The off-center distinguished family is a matching |
| `TotalColoring.Auxiliary.PairSingletonWitness.matchingPart_avoids_center_neighbors` | `PairSingletonExtension` | Matching endpoints are not neighbors of the new center |
| `TotalColoring.Auxiliary.PairSingletonWitness.distinguished_decomposition` | `PairSingletonExtension` | The distinguished family is the matching part union the full center star |
| `TotalColoring.Auxiliary.PairSingletonWitness.degree_none_eq_singletonVertices_card` | `PairSingletonExtension` | Identifies center degree with the singleton-vertex count |
| `TotalColoring.Auxiliary.PairSingletonWitness.degree_some_eq` | `PairSingletonExtension` | Identifies copied-vertex degree with original degree plus one |
| `TotalColoring.Auxiliary.PairSingletonWitness.card_add_degree_none_eq_two_mul_distinguished_card` | `PairSingletonExtension` | Relates graph order, center degree, and class count exactly |
| `TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_class_count_and_bounds` | `PairSingletonExtension` | Produces structural membership from class-count, degree, and order bounds |
| `TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_highDegree` | `PairSingletonExtension` | Produces membership at parameter `G.maxDegree + 1` from exact count and density |

## Supplied equitable-partition interface

The supplied-partition declarations are retained as an alternate entrypoint.
The terminal package theorem does not assume that such a partition is given.

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.Auxiliary.EquitableIndependentPartition` | `EquitablePairSingleton` | Exactly `D` nonempty independent classes with equitable sizes |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.class_card_eq_one_or_two` | `EquitablePairSingleton` | Derives class sizes one or two from `D <= Fintype.card V < 2D` |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.toPairSingletonWitness` | `EquitablePairSingleton` | Constructs the concrete pair/singleton witness |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.distinguished_card` | `EquitablePairSingleton` | Proves the induced distinguished family has cardinality `D` |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.highDegreeWitness_inAuxiliaryClass` | `EquitablePairSingleton` | Packages auxiliary membership for a supplied high-degree partition |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition` | `EquitablePairSingleton` | Produces a valid assignment from a supplied partition and density hypothesis |

## Reusable auxiliary terminal entrypoints

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.IsOutsideEdgeMinimalNoncolorable.false_of_critical_allD` | `CriticalAllDClosure` | A finite outside-edge-minimal noncolorable auxiliary member is impossible |
| `TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass` | `CriticalAllDClosure` | Every finite `InAuxiliaryClass D H J` has `HasValidRainbowColoring D H J` |
| `TotalColoring.Auxiliary.Extension.decode_valid` | `Auxiliary` | A proper selector-rainbow auxiliary assignment decodes to a valid total assignment |
| `TotalColoring.Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` | `AuxiliaryTransfer` | A supplied compatible extension into a finite auxiliary-class member yields a valid assignment with palette `Fin (D + 2)` |

The supplied-extension theorem remains conditional on its explicit extension,
selector-membership, and auxiliary-class inputs. The terminal high-degree
theorem discharges those inputs through the complement-matching route; it does
not weaken or replace the reusable conditional theorem.

## Executable checker soundness

| Declaration | Accepted Boolean implies |
| --- | --- |
| `TotalColoring.Certificate.checkTotal_sound` | The supplied total assignment is semantically valid |
| `TotalColoring.Certificate.checkEdge_sound` | The supplied edge assignment is proper |
| `TotalColoring.Certificate.checkRainbow_sound` | Distinguished selector edges have pairwise distinct colors |
| `TotalColoring.Certificate.checkExtension_sound` | The accepted auxiliary certificate decodes to a valid total assignment |

The checkers operate on already well-typed Lean values. Parsing arbitrary JSON
or proving an external census complete is outside these soundness theorems.

## Copyable inspection

```lean
import TotalColoring

#check TotalColoring.exists_valid_assignment_of_highDegree
#check TotalColoring.Auxiliary
  .exists_valid_assignment_of_highDegree_nonempty
#check TotalColoring.exists_valid_assignment_of_isEmpty
#check TotalColoring.MatchingLowerBound
  .exists_matchingGraph_edgeFinset_card_ge
#check TotalColoring.MatchingLowerBound
  .exists_complement_matchingGraph_edgeFinset_card_eq
#check TotalColoring.Auxiliary
  .exists_pairSingletonWitness_of_highDegree
#check TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.EquitableIndependentPartition
  .exists_valid_assignment_of_highDegreePartition
#check TotalColoring.Certificate.checkExtension_sound
```

The maintained version of this snippet is
[`docs/examples/Quickstart.lean`](https://github.com/chenle02/total-coloring-lean/blob/main/docs/examples/Quickstart.lean)
and is compiled by CI. The package declaration is authoritative; a modified
integration tree still needs its own exact-tree verification before
publication.
