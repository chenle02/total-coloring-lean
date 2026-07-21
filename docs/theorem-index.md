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
full/Quickstart/`leanchecker` jobs, `5388311` through `5388315`. The later
publishable commit `06d43af7`, exact tree
`89a32c7a78e294a8b1484092ec79afaa3b4ace5a`, received its own Wave 11 gate:
leaf `5388961`, all 64 distinct matrix roles after narrow repairs, container
`mk_all --check` job `5389029`, and independent host trust jobs
`5389030`--`5389032`. PR #8 merged that exact tree into `main` as `0e938606`;
PR-head and post-merge Lean/docs CI passed.

## Conditional independent-seed endpoint on `main`

The following declarations are present on current `main` commit `61e79bea…`,
tree `cb2d7d06…`. Their historical proof source is branch
`agent/independent-seed-endpoint` at exact source commit
`cc4dd7ae1d858ea0583549f88707952e2414bf60`, tree
`9af6a84e1305aed9a0156dcd59c279de792dea4a`; PR #10 merged them.

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.exists_valid_assignment_of_independentSeedPeel` | `IndependentSeed` | From `0 < q`, a supplied proper `phi : EdgeAssignment G (Fin q)`, a supplied independent seed `A`, and a supplied `IndependentSeedPeelCertificate G A q`, produces `assignment : Assignment G (Fin (q + 1))` with `assignment.Valid` |
| `TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel` | `IndependentSeed` | Direct specialization from a supplied proper `EdgeAssignment G (Fin (G.maxDegree + 1))`, independent seed, and certificate at `G.maxDegree + 1` to a valid `Assignment G (Fin (G.maxDegree + 2))` |

The peel certificate supplies a duplicate-free order covering exactly the
vertices outside `A` and the strict bound

```text
(neighbors of v later in the order).card < q - G.degree v
```

at every deletion step. Setting `q = G.maxDegree + 1` makes the conclusion a
conditional `Fin (G.maxDegree + 2)` palette. The declaration does not prove
Vizing's theorem or construct the proper edge assignment, and it does not
prove existence of the independent seed or peel certificate. It is therefore
not an unrestricted Total Coloring Conjecture theorem and does not change the
`G.maxDegree + 3` palette of the package terminal theorem above.
The maximum-degree wrapper only performs this substitution; all witnesses
remain explicit inputs.

Exact source tree `9af6a84e…` passed two sealed offline Easley trust replays:
job `5389587` on node408 completed in 11m40s with peak RSS `121378968K`, and
job `5389588` on node412 completed in 11m39s with peak RSS `122474236K`.
Both exited `0:0` after strict leaf, umbrella/full, Quickstart, axiom,
`leanchecker`, metadata, and exact-tree gates. The receipts validate the
conditional declarations, not existence of their supplied witnesses.

## Total-independent selector decoder on `main`

The following declarations are present on current `main` commit `61e79bea…`,
tree `cb2d7d06…`. Their historical proof source is branch
`agent/total-independent-selector-decoder` at source commit
`d008514c7a1cf834007bf0bd8de0d10a93926711`, exact tree
`1847934c78da03fe80bb67236868700c79016129`; PR #11 merged them.

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.totalIndependentSelectorAssignment_valid` | `TotalIndependentSelector` | Semantic decoder: a fresh-color independent vertex set and a fresh-color matching of edges avoiding that set combine with a proper allowed old coloring on all remaining vertices to give a valid total assignment in `Fin (q + 1)` |
| `TotalColoring.SelectorCorePeelCertificate` | `TotalIndependentSelector` | Packages `S ⊆ K`, a duplicate-free order covering exactly the complement of `K`, and the exact core-relative peel inequalities |
| `TotalColoring.exists_valid_assignment_of_totalIndependentSelectorPeel` | `TotalIndependentSelector` | Extends a supplied actual-list coloring on `K \ S` along the supplied core-relative peel order and invokes the semantic decoder |
| `TotalColoring.exists_valid_assignment_of_maxDegreeTotalIndependentSelectorPeel` | `TotalIndependentSelector` | Specializes the conditional decoder to a proper `Fin (G.maxDegree + 1)` edge assignment and returns a valid `Fin (G.maxDegree + 2)` total assignment |
| `TotalColoring.AlternatingRainbowPathSelectorCertificate` | `TotalIndependentSelector` | Explicit indexed path, rainbow, spare, alternating matching, start-avoidance, core-color, and peel evidence; it does not assert certificate existence |
| `TotalColoring.exists_valid_assignment_of_alternatingRainbowPathSelector` | `TotalIndependentSelector` | Checks the donor exchange from the supplied alternating rainbow-path certificate and returns a valid assignment in `Fin (q + 1)` |
| `TotalColoring.exists_valid_assignment_of_maxDegreeAlternatingRainbowPathSelector` | `TotalIndependentSelector` | Maximum-degree specialization of the explicit path-certificate wrapper |

The generic peel inequality at a step `v :: tail` is exactly

```text
(G.neighborFinset v ∩ ((K \ S) ∪ tail.toFinset)).card
  < q - G.degree v.
```

No declaration in this section constructs the proper old-palette edge
coloring, the selector matching, the core coloring, the peel certificate, or
the alternating rainbow path. The maximum-degree wrappers are therefore
conditional `G.maxDegree + 2` implications, not an unrestricted Total
Coloring Conjecture theorem.

Exact source tree `1847934c…` passed sealed Easley job `5391803` on node411:
exit `0:0`, elapsed 16m09s, peak RSS `125399676K`, with exact-tree, strict
leaf, target/umbrella/full, Quickstart, axiom, `leanchecker`, JSON/diff, and
cache-archive gates.

## Partial-edge selector normalization on `main`

The following declarations are present on current `main` commit `61e79bea…`,
tree `cb2d7d06…`. Their historical proof source is stacked branch
`agent/partial-edge-selector-normalization` at source commit
`c3dbe69c15f96e3c71d8481ae4e517ee2f4fdbf2`, exact source tree
`11007a4aa381984a8d66aa1db297312cebe8d8b5`; PR #12 merged them.

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.EdgeAssignment.ValidOutside` | `PartialEdgeSelector` | Properness is required only between adjacent edges outside the selected finset; values on selected edges are unrestricted |
| `TotalColoring.partialEdgeSelectorEdgeAssignment_valid` | `PartialEdgeSelector` | Sending a matching to an arbitrarily chosen fresh color preserves edge-color validity when the old assignment is proper outside that matching |
| `TotalColoring.partialEdgeSelectorAssignment_valid` | `PartialEdgeSelector` | Adds an independent fresh vertex class and an avoiding fresh edge matching; old vertex colors only avoid incident edges outside the matching |
| `TotalColoring.totalIndependentSelectorAssignment_valid_of_validOutside` | `PartialEdgeSelector` | Strengthens the earlier last-color decoder by replacing global old-edge validity with validity outside the selected matching |
| `TotalColoring.PartialEdgeSelectorNormalization` | `PartialEdgeSelector` | Packages the selector sets, pulled-back old colors, all forward hypotheses, and literal equality of the decoded assignment with a supplied assignment |
| `TotalColoring.partialEdgeSelectorNormalization_of_valid` | `PartialEdgeSelector` | For a supplied valid `Fin (q + 1)` total assignment, any chosen fresh color and fallback old color produce the exact normalization package |
| `TotalColoring.maxDegreePartialEdgeSelectorNormalization_of_valid` | `PartialEdgeSelector` | Rephrases the reverse construction for a supplied `Fin (G.maxDegree + 2)` total coloring; the coloring is still an explicit input |

The forward theorem does not construct any selector or coloring. The reverse
constructor starts from a supplied valid total coloring, so it cannot be used
as an existence proof for that coloring or for the Total Coloring Conjecture.

## Adapted-spare vertex endpoint (unmerged)

The following declaration is on `agent/donor-global-formalization`, based on
current `main` commit `61e79bea…`, tree `cb2d7d06…`. Until merge, attribute
the declaration only to that branch; any verification claim must cite a
tree-specific external receipt.

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.adaptedSpareVertexColor_proper_iff` | `AdaptedSpareEndpoint` | Assuming `Disjoint A B`, the supplied endpoint coloring (`none` on `A`, `some (head v)` on `B`, `some (missing v)` elsewhere) is proper on `K` exactly when `A` is independent, every equal-missing conflict is covered by `A ∪ B`, head labels are clean against unchanged neighbors, and head labels are proper on adjacent vertices of `B` |

This is an exact vertex-side equivalence. It does not construct `A`, `B`, a
physical donor matching, donor-label transport, seed or matching witnesses,
missing/head data, a proper edge coloring, or a total coloring. It gives no
unrestricted `Delta + 2` theorem and does not prove the Total Coloring
Conjecture.

## Minimum-six typed CNF semantics (unmerged)

These declarations are on `agent/minsix-threshold-formula` and are not part
of current `main`.

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.MinSixCNFCore.Sinz.exists_satisfying_extension_iff` | `MinSixCNFCore` | A Sinz prefix block has an auxiliary extension exactly when its displayed primary inputs are at most one |
| `TotalColoring.MinSixCNFCore.Threshold.extension_satisfies_exactCountCNF` | `MinSixThresholdEncoder` | Exact primary count `k` supplies the canonical threshold auxiliaries satisfying the typed bounded exact-count CNF |
| `TotalColoring.MinSixCNFCore.Threshold.extension_satisfies_exactCountCNF_iff` | `MinSixThresholdEncoder` | On that canonical extension only, satisfaction of the typed exact-count CNF is equivalent to primary count `k` |

This is not a concrete DIMACS correspondence, descriptor enumeration, LRAT
check, UNSAT theorem, blocker composition, or graph-coloring theorem. Every
proposed branch tree requires a tree-specific external receipt before merge.

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
#check TotalColoring.exists_valid_assignment_of_independentSeedPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel
#check TotalColoring.SelectorCorePeelCertificate
#check TotalColoring.exists_valid_assignment_of_totalIndependentSelectorPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeTotalIndependentSelectorPeel
#check TotalColoring.AlternatingRainbowPathSelectorCertificate
#check TotalColoring.exists_valid_assignment_of_alternatingRainbowPathSelector
#check TotalColoring.exists_valid_assignment_of_maxDegreeAlternatingRainbowPathSelector
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

The canonical version of this snippet is maintained in
[`examples/Quickstart.lean`](examples/Quickstart.lean). Current `main` commit
`61e79bea…`, tree `cb2d7d06…`, contains the independent-seed, selector/path,
and partial-edge groups. Their earlier source commits and trees remain
historical proof provenance. The final adapted-spare endpoint `#check` in the
branch Quickstart requires `agent/donor-global-formalization`. Until merge,
attribute it only to that branch; any verification claim must cite a
tree-specific external receipt.
