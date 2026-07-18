# Exact proof status

## Package theorem for the high-degree regime

The package now contains the declaration:

```lean
TotalColoring.exists_valid_assignment_of_highDegree
```

Its full mathematical scope is:

```text
[Fintype V] [DecidableEq V]
G : SimpleGraph V
[DecidableRel G.Adj]
Fintype.card V <= 2 * G.maxDegree
------------------------------------------------------------
exists assignment : Assignment G
    (ExtensionPalette (G.maxDegree + 1)),
  assignment.Valid
```

Since `ExtensionPalette D` is `Fin (D + 2)`, the conclusion uses the palette
`Fin (G.maxDegree + 3)`. The theorem covers empty and nonempty finite vertex
types and has no parity hypothesis.

!!! success "Plain-language reading"

    Every finite graph satisfying the displayed order/maximum-degree
    inequality has a kernel-checked valid total assignment in the displayed
    palette.

This is a theorem of the Lean package. It is not, by itself, a statement that
the manuscript has locked or proved a corresponding paper theorem, and it
makes no novelty claim.

The theorem is propositional: it proves that an assignment exists. It is not
an executable routine for extracting a coloring from an external graph file.

## Checked end-to-end route

### 1. A matching lower bound

`TotalColoring.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_ge`
proves the reusable finite-graph fact

```text
(forall v, k <= H.degree v) -> 2 * k <= Fintype.card V
  -> exists a matching subgraph of H with at least k edges.
```

The proof chooses a maximum-cardinality matching and uses the absence of a
one-edge augmentation and of a length-three augmenting path to obtain the
degree-sum contradiction.

For a nonempty target graph `G`, set

```text
k = Fintype.card V - (G.maxDegree + 1).
```

The complement-degree identity and the high-degree hypothesis give the two
inputs required by the matching theorem. This specialization is

```lean
TotalColoring.MatchingLowerBound
  .exists_complement_matchingGraph_edgeFinset_card_ge
```

in `HighDegreeComplementMatching`.

### 2. Exact-size extraction

`IsMatchingGraph.exists_subgraph_edgeFinset_card_eq` trims a supplied
matching to any smaller prescribed number of edges. The composed declaration

```lean
TotalColoring.MatchingLowerBound
  .exists_complement_matchingGraph_edgeFinset_card_eq
```

therefore returns a matching in `G`'s complement with exactly

```text
Fintype.card V - (G.maxDegree + 1)
```

edges.

### 3. Pair/singleton witness and auxiliary class

`PairSingletonWitness.ofComplementMatching` turns that matching into a fixed
partition relation: matching edges are pair classes and uncovered vertices
are singleton classes. The checked counting lemmas give exactly

```text
P.distinguished.card = G.maxDegree + 1.
```

The declaration

```lean
TotalColoring.Auxiliary.exists_pairSingletonWitness_of_highDegree
```

packages this construction. The existing `PairSingletonWitness` interface
then constructs the ordinary auxiliary graph on `Option V`, supplies the
conflict-preserving decoder, proves selector membership and exact coverage,
and establishes the matching-plus-full-star structural predicate
`InAuxiliaryClass (G.maxDegree + 1)`.

### 4. Auxiliary coloring and decoding

The all-orders auxiliary theorem

```lean
TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
```

proves a proper `Fin (D + 2)` auxiliary edge coloring that is rainbow on the
distinguished edges of every finite `InAuxiliaryClass D H J`. Its proof route
runs through minimal noncolorable extraction, a valid one-hole critical state,
fan and missing-color capacity, global pivots, dominators, crossing, and the
final contradiction.

`Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` composes that
theorem with the semantic decoder. The nonempty high-degree composition is:

```lean
TotalColoring.Auxiliary
  .exists_valid_assignment_of_highDegree_nonempty
```

### 5. Empty vertex type

`TotalColoring.exists_valid_assignment_of_isEmpty` proves that a graph on an
empty vertex type has a vacuously valid assignment for every color type. The
terminal theorem splits on `isEmpty_or_nonempty V`, applies this base case in
the empty branch, and applies the complement-matching route in the nonempty
branch.

## Retained supplied-input interfaces

The end-to-end theorem does not remove the lower-level APIs. They remain
useful when a downstream proof already has more structured input:

- a supplied compatible `Auxiliary.Extension` plus selector membership and
  `InAuxiliaryClass D H J` can use
  `Extension.exists_valid_decode_of_inAuxiliaryClass`;
- a supplied `PairSingletonWitness` can use its concrete auxiliary graph,
  extension, structural, and numerical lemmas directly; and
- a supplied
  `EquitableIndependentPartition G (G.maxDegree + 1)` on a nonempty graph can
  use the theorem below when it also has
  `Fintype.card V <= 2 * G.maxDegree`:
  `EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition`.

The equitable-partition theorem remains a valid conditional interface. It is
no longer a missing premise of
`TotalColoring.exists_valid_assignment_of_highDegree`: the terminal theorem
uses the checked complement-matching construction instead.

## Structural auxiliary hypothesis

`InAuxiliaryClass D H J` existentially supplies a center `x` and an off-center
matching `M`. Its fields require, among other things:

- `J` is exactly `M` together with the full star at `x`;
- `M` is a matching, lies off `x`, and avoids neighbors of `x`;
- every vertex other than `x` is incident with exactly one member of `J`;
- `J.card = D` and the ambient maximum degree is at most `D`; and
- the center degree lies between `2` and `D`.

This structural predicate remains the boundary of the reusable all-orders
auxiliary theorem, even though the high-degree wrapper now constructs its own
witness.

## What the checked package theorem does not establish

The checked declarations do **not** establish:

- the Total Coloring Conjecture;
- a `G.maxDegree + 2` total-coloring conclusion;
- a theorem for graphs outside the displayed high-degree regime;
- a locked or fully proved theorem in the separate research manuscript;
- novelty of the package theorem or of any proposed manuscript result;
- an executable coloring extractor for arbitrary external graph data; or
- publication trust for a later Git integration tree merely because its proof
  source descends from the checked development tree.

!!! warning "Palette warning"

    The checked terminal palette is
    `ExtensionPalette (G.maxDegree + 1)`, definitionally
    `Fin (G.maxDegree + 3)`. Do not shorten this to a stronger palette, and do
    not identify the package result with a manuscript claim without the
    manuscript's independent theorem and novelty gates.

## Exact proof-tree verification receipt

The terminal proof-development source had exact Git tree
`4624044788ab42c0dc116cfbf7f38c696065263c`. Its source archive SHA-256 was
`302bc3f00bf5d8c1ce563d2bc84d1370e627c81d219e8d8085b286a21d530077`.

The exact-tree leaf build passed in Easley job `5388302` (`COMPLETED`, exit
`0:0`). Five separate high-memory replays of that same tree then passed the
full package build, Quickstart checks, and `leanchecker`:

| Job | Node | Requested memory | Elapsed | MaxRSS |
| --- | --- | ---: | ---: | ---: |
| `5388311` | `node417` | `330G` | `00:14:21` | `140371724K` |
| `5388312` | `node506` | `330G` | `00:14:01` | `140162776K` |
| `5388313` | `node922` | `330G` | `00:07:14` | `86165748K` |
| `5388314` | `node924` | `300G` | `00:04:47` | `65441888K` |
| `5388315` | `node510` | `330G` | `00:14:47` | `89498688K` |

Each job ended with its terminal trust success marker naming tree
`4624044788ab42c0dc116cfbf7f38c696065263c`.

This proof-tree receipt is not a publication receipt for any later integrated
Git tree. A final publication gate must also run the repository's canonical
raw-text proof-escape scan. Documentation edits, integration commits, public
CI, and any resulting tree hash must receive their own exact-tree gate before
the public branch is described as verified at that later tree; the receipt is
recorded externally so it does not alter the tree it certifies.

## Earlier public layers

- The all-orders auxiliary theorem was introduced at `310b82c…`; public Lean
  CI run
  [`29588129760`](https://github.com/chenle02/total-coloring-lean/actions/runs/29588129760)
  passed at that commit.
- The conditional auxiliary-to-total transfer was introduced at `9bdcdec…`
  and merged by PR
  [#6](https://github.com/chenle02/total-coloring-lean/pull/6).
- The pair/singleton structural and numerical layers, complement-witness
  adapter, matching lemmas, empty base case, and terminal high-degree wrapper
  were developed subsequently on PR #8's branch. Exact publication status is
  determined by the public branch and CI, not by this prose.
- Release `v0.1.0` predates these result layers. Cite an exact commit or exact
  verified tree until a later release includes the declaration used.

For tools, the public boundary is mirrored in
[`claim-boundary.json`](claim-boundary.json). Lean declarations at the pinned
commit remain authoritative if prose and code disagree.
