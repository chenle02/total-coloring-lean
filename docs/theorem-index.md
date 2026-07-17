# Curated theorem index

This is a small map of public entrypoints, not an exhaustive inventory of every
internal lemma.

## Core predicates

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.InAuxiliaryClass` | `AuxiliaryClass` | Pair-level structural predicate for the matching-plus-star class |
| `TotalColoring.ExtensionPalette` | `CriticalState` | The auxiliary palette `Fin (D + 2)` |
| `TotalColoring.HasValidRainbowColoring` | `CriticalState` | Existence of a proper auxiliary edge coloring rainbow on `J` |
| `TotalColoring.Auxiliary.Extension` | `Auxiliary` | Conflict-preserving data for decoding auxiliary edge colors to a total assignment |

## Supplied pair/singleton constructor seam

The qualitative structural declarations in this section are commit
`7aa102b…`, exact tree
`4b6440a0df108f47f5c120e7e0187c058a462138`. The numerical declarations were
verified from private source commit `acb08de…`, exact tree
`7207e2a282ff829fba9737e93154f46f385ef879`, and integrated with identical Lean
content at public PR commit `343b7b8…`, tree
`9863f500b2671048f4dc386f497eb6523b065099`. Full/checker gate `5387929` and
independent trust-v3 gate `5387978` passed. PR #8 remains draft; these layers
are not on `main` unless that PR has since merged.

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.Auxiliary.PairSingletonWitness` | `PairSingletonExtension` | A supplied fixed partition relation into independent singleton and pair classes; the finite constructor uses a finite vertex type with decidable equality |
| `TotalColoring.Auxiliary.PairSingletonWitness.auxiliaryGraph` | `PairSingletonExtension` | The ordinary auxiliary graph on `Option V` |
| `TotalColoring.Auxiliary.PairSingletonWitness.extension` | `PairSingletonExtension` | The conflict-preserving extension from the original graph into that auxiliary graph |
| `TotalColoring.Auxiliary.PairSingletonWitness.classEdge_mem_distinguishedEdgeSet` | `PairSingletonExtension` | Every decoder selector belongs to the constructed distinguished edge set |
| `TotalColoring.Auxiliary.PairSingletonWitness.distinguished_exact_coverage` | `PairSingletonExtension` | Every copied original vertex lies on exactly one distinguished edge |
| `TotalColoring.Auxiliary.PairSingletonWitness.matchingPart` | `PairSingletonExtension` | The off-center part of the distinguished family |
| `TotalColoring.Auxiliary.PairSingletonWitness.matchingPart_isEdgeMatching` | `PairSingletonExtension` | The off-center distinguished family is a matching |
| `TotalColoring.Auxiliary.PairSingletonWitness.matchingPart_off_center` | `PairSingletonExtension` | No matching-part edge contains the new center |
| `TotalColoring.Auxiliary.PairSingletonWitness.matchingPart_avoids_center_neighbors` | `PairSingletonExtension` | Matching endpoints are not neighbors of the new center |
| `TotalColoring.Auxiliary.PairSingletonWitness.distinguished_decomposition` | `PairSingletonExtension` | The distinguished family is the matching part union the full center incidence star |
| `TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_numeric` | `PairSingletonExtension` | Produces `IsAuxiliaryClassMember` conditional on exact distinguished cardinality, maximum-degree bound, and center degree in `[2, D]` |
| `TotalColoring.Auxiliary.PairSingletonWitness.degree_none_eq_singletonVertices_card` | `PairSingletonExtension` | Identifies the center degree with the singleton-vertex count |
| `TotalColoring.Auxiliary.PairSingletonWitness.degree_some_eq` | `PairSingletonExtension` | Identifies each copied-vertex degree with its original degree plus one |
| `TotalColoring.Auxiliary.PairSingletonWitness.card_add_degree_none_eq_two_mul_distinguished_card` | `PairSingletonExtension` | Relates graph order, center degree, and the distinguished class count exactly |
| `TotalColoring.Auxiliary.PairSingletonWitness.degree_none_le_card_distinguished` | `PairSingletonExtension` | Bounds the center degree by the distinguished class count |
| `TotalColoring.Auxiliary.PairSingletonWitness.maxDegree_le_of_bounds` | `PairSingletonExtension` | Derives the auxiliary maximum-degree bound from class-count and copied-degree bounds |
| `TotalColoring.Auxiliary.PairSingletonWitness.center_degree_bounds` | `PairSingletonExtension` | Derives the center-degree range from class-count and order bounds |
| `TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_class_count_and_bounds` | `PairSingletonExtension` | Produces `IsAuxiliaryClassMember D` from `J.card = D`, an original-degree bound, and an order bound |
| `TotalColoring.Auxiliary.PairSingletonWitness.isAuxiliaryClassMember_of_highDegree` | `PairSingletonExtension` | Produces structural membership with parameter `G.maxDegree + 1` from the concrete class count and high-degree density inequality |

## Supplied equitable-partition adapter

These declarations are in `EquitablePairSingleton` at commit `a441fbf…`, exact
tree `0e9b04a2acabae0cb0612e5e3cbf0344cc2f94f7`. Full/Quickstart/leanchecker
trust job `5387982` passed with exit `0:0`; PR #8 remains draft.

| Declaration | Purpose |
| --- | --- |
| `TotalColoring.Auxiliary.EquitableIndependentPartition` | Exactly `D` nonempty independent classes with equitable sizes |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.class_card_eq_one_or_two` | Derives class sizes one or two from `D <= |V| < 2D` |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.toPairSingletonWitness` | Constructs the concrete pair/singleton witness |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.distinguished_card` | Proves the induced distinguished family has cardinality `D` |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.highDegreeWitness_inAuxiliaryClass` | Packages pair-level auxiliary membership for a supplied high-degree partition |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition` | Produces a valid total assignment with `ExtensionPalette (G.maxDegree + 1)` from a supplied partition and density |

## Terminal proof entrypoints

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.IsOutsideEdgeMinimalNoncolorable.false_of_critical_allD` | `CriticalAllDClosure` | A finite outside-edge-minimal noncolorable auxiliary member is impossible |
| `TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass` | `CriticalAllDClosure` | Every finite `InAuxiliaryClass D H J` has `HasValidRainbowColoring D H J` |
| `TotalColoring.Auxiliary.Extension.decode_valid` | `Auxiliary` | A proper selector-rainbow auxiliary assignment decodes to a valid total assignment |
| `TotalColoring.Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` | `AuxiliaryTransfer` | A supplied compatible extension into a finite auxiliary-class member yields a valid total assignment with palette `Fin (D + 2)` |
| `TotalColoring.Auxiliary.EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition` | `EquitablePairSingleton` | A supplied equitable independent `G.maxDegree + 1` partition on a nonempty high-degree graph yields a valid total assignment with `G.maxDegree + 3` colors |

The composed transfer theorem remains conditional on a supplied
`Auxiliary.Extension G H`, membership of every selector edge in the
distinguished set, and `InAuxiliaryClass D H J`. A supplied
`PairSingletonWitness` now discharges the first two pieces for its constructed
graph. Its structural layer also discharges every qualitative field of
`IsAuxiliaryClassMember`. Its numerical layer derives the maximum-degree and
center-degree fields from exact degree/count identities; under the concrete
class count and density hypothesis, `isAuxiliaryClassMember_of_highDegree`
uses parameter `G.maxDegree + 1`. `EquitablePairSingleton` now constructs that
witness and proves `J.card = D` from a supplied equitable independent
`D`-partition under `D <= |V| < 2D`. Its terminal high-degree theorem composes
the construction with the decoder.

The remaining missing theorem must produce the required equitable independent
`G.maxDegree + 1` partition for each nonempty graph in the target regime.
Complement matching is a prospective route, and the empty graph is a separate
case. Hence the checked conditional `Delta + 3` result is not yet an
end-to-end arbitrary-graph theorem.

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

#check TotalColoring.InAuxiliaryClass
#check TotalColoring.HasValidRainbowColoring
#check TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.PairSingletonWitness
#check TotalColoring.Auxiliary.PairSingletonWitness.auxiliaryGraph
#check TotalColoring.Auxiliary.PairSingletonWitness.extension
#check TotalColoring.Auxiliary.PairSingletonWitness
  .classEdge_mem_distinguishedEdgeSet
#check TotalColoring.Auxiliary.PairSingletonWitness
  .isAuxiliaryClassMember_of_highDegree
#check TotalColoring.Auxiliary.EquitableIndependentPartition
  .distinguished_card
#check TotalColoring.Auxiliary.EquitableIndependentPartition
  .exists_valid_assignment_of_highDegreePartition
#check TotalColoring.Certificate.checkExtension_sound
```

The maintained version of this snippet is
[`docs/examples/Quickstart.lean`](https://github.com/chenle02/total-coloring-lean/blob/main/docs/examples/Quickstart.lean)
and is compiled by CI.
