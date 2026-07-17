# Exact proof status

## All-orders auxiliary theorem

At commit `310b82c174ab2281581900897d4646875575e89b`, the library proves:

```text
InAuxiliaryClass D H J
  →
HasValidRainbowColoring D H J
```

for every finite vertex type. The declaration is:

```lean
TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
```

`HasValidRainbowColoring D H J` means that there exists an
`EdgeAssignment H (Fin (D + 2))` which is proper and whose colors are pairwise
distinct on the distinguished edge set represented by `J`.

!!! success "Plain-language reading"

    Every finite graph-and-distinguished-set pair satisfying the exact formal
    predicate `InAuxiliaryClass D H J` has the required rainbow auxiliary edge
    coloring from the `D + 2` palette.

## Conditional auxiliary-to-total transfer

At commit `9bdcdec1a872ccef42cfd79e791fe39c22a1beeb`, the library also proves:

```lean
TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
```

Its explicit inputs are:

- a supplied conflict-preserving `Auxiliary.Extension G H`;
- a proof that every `X.classEdge vertex` belongs to
  `distinguishedEdgeSet H J`; and
- `InAuxiliaryClass D H J` on the finite auxiliary graph.

Its conclusion is:

```text
exists assignment : Assignment G (Fin (D + 2)), assignment.Valid.
```

!!! success "Plain-language reading"

    Once a compatible auxiliary extension has been supplied, the all-orders
    rainbow edge-coloring theorem and the semantic decoder compose to give a
    valid total coloring of the supplied original graph.

This is a conditional transfer theorem. It does not itself construct the
extension from an arbitrary graph or prove a relation between `D` and the
original graph's maximum degree.

## Supplied pair/singleton extension seam

At commit `dc2a318be1dd1475b90c492ad460c4180a3fbdec`, on a finite vertex type
with decidable equality, a supplied
`P : TotalColoring.Auxiliary.PairSingletonWitness G` determines:

- the ordinary graph `P.auxiliaryGraph` on `Option V`;
- a conflict-preserving
  `P.extension : Auxiliary.Extension G P.auxiliaryGraph`; and
- `P.classEdge_mem_distinguishedEdgeSet`, proving every selector lies in the
  corresponding distinguished edge set.

!!! success "Plain-language reading"

    Once the singleton/pair relation itself is supplied, Lean has checked the
    graph construction and all three conflict maps needed by the decoder.

The structural layer at commit
`7aa102b0211c36c6d69f03bc051a5c2706f62c9d`, exact Git tree
`4b6440a0df108f47f5c120e7e0187c058a462138`, also kernel-checks:

- `P.distinguished_exact_coverage`: every copied original vertex `some v`
  lies on exactly one member of `P.distinguished`;
- `P.matchingPart_isEdgeMatching` and `P.matchingPart_off_center`: the
  off-center distinguished family `P.matchingPart` is a matching and contains
  no edge through the new center `none`;
- `P.matchingPart_avoids_center_neighbors`: no endpoint of that matching is
  adjacent to the center in `P.auxiliaryGraph`; and
- `P.distinguished_decomposition`: the distinguished family is exactly
  `P.matchingPart` together with the full incidence star at `none`.

The numerical layer further kernel-checks:

- `P.degree_none_eq_singletonVertices_card`: the center degree is exactly the
  number of singleton vertices;
- `P.degree_some_eq`: every copied original vertex has degree
  `G.degree v + 1`;
- `P.card_add_degree_none_eq_two_mul_distinguished_card`: graph order plus
  center degree equals twice the number of distinguished classes;
- `P.degree_none_le_card_distinguished`: the center degree is at most the
  distinguished class count;
- `P.maxDegree_le_of_bounds` and `P.center_degree_bounds`: the numerical class
  fields follow from class-count, original-degree, and order bounds.

The theorem `P.isAuxiliaryClassMember_of_class_count_and_bounds D` proves

```text
IsAuxiliaryClassMember D P.auxiliaryGraph none
  P.distinguished P.matchingPart
```

from

```text
P.distinguished.card = D
G.maxDegree + 1 ≤ D
Fintype.card V + 2 ≤ 2 * D
```

Beyond the ambient `[Fintype V]`, `[DecidableEq V]`,
`[DecidableRel G.Adj]`, and
`[DecidableRel P.auxiliaryGraph.Adj]` requirements, its specialization
`P.isAuxiliaryClassMember_of_highDegree` has only these additional
proposition-valued hypotheses:

```text
P.distinguished.card = G.maxDegree + 1
Fintype.card V ≤ 2 * G.maxDegree
```

It concludes structural membership with parameter `G.maxDegree + 1`.

!!! success "Plain-language reading"

    Maximum-degree and center-degree bounds are no longer independent external
    obligations. Lean derives them from exact degree/count identities. In the
    high-degree specialization, the remaining witness-specific assumption is
    the class count `J.card = G.maxDegree + 1`; the density inequality is the
    explicit graph hypothesis.

## Supplied equitable-partition adapter

At commit `a441fbfa1e404dc7610e0c32c80dd692cd938c20`, exact tree
`0e9b04a2acabae0cb0612e5e3cbf0344cc2f94f7`, the module
`EquitablePairSingleton` closes the adapter seam. The structure
`EquitableIndependentPartition G D` supplies a partition into exactly `D`
nonempty independent classes with sizes differing by at most one. Under

```text
D ≤ Fintype.card V
Fintype.card V < 2 * D,
```

Lean checks `Q.class_card_eq_one_or_two`, constructs
`Q.toPairSingletonWitness`, and proves `Q.distinguished_card`, the exact
`J.card = D` identity.

For the high-degree specialization, the terminal theorem
`Q.exists_valid_assignment_of_highDegreePartition` has the full scope

```text
[Fintype V] [DecidableEq V] [Nonempty V] [DecidableRel G.Adj]
Q : EquitableIndependentPartition G (G.maxDegree + 1)
Fintype.card V ≤ 2 * G.maxDegree
```

and concludes

```text
∃ assignment : Assignment G (ExtensionPalette (G.maxDegree + 1)),
  assignment.Valid.
```

Thus Lean proves a conditional `Delta + 3` total-coloring result from the
explicitly supplied partition. Internally,
`Q.highDegreeWitness_inAuxiliaryClass` establishes the complete auxiliary
hypothesis before the checked decoder is applied.

!!! success "Plain-language reading"

    The adapter, exact class count, auxiliary membership, and terminal decoding
    are checked. What remains is a theorem producing the required partition
    for every nonempty target graph, potentially through complement matching,
    plus the separate empty-graph case.

The pinned Mathlib has no ready Hajnal--Szemerédi-style existence theorem for
this step. Complement matching remains a prospective route, not a checked
existence proof.

## Structural hypothesis

`InAuxiliaryClass D H J` existentially supplies a center `x` and an off-center
matching `M`. Its checked fields require, among other things:

- `J` is exactly `M` together with the full star at `x`;
- `M` is a matching, lies off `x`, and avoids neighbors of `x`;
- every vertex other than `x` is incident with exactly one member of `J`;
- `J.card = D` and the ambient maximum degree is at most `D`;
- the center degree lies between `2` and `D`.

The source of truth is
[`TotalColoring/AuxiliaryClass.lean`](https://github.com/chenle02/total-coloring-lean/blob/310b82c174ab2281581900897d4646875575e89b/TotalColoring/AuxiliaryClass.lean).

## What the checked results do not establish

The checked results do **not** prove:

- the Total Coloring Conjecture;
- an unrestricted total-coloring theorem for all finite graph orders;
- the proposed high-degree `Delta + 2` total-coloring conclusion;
- an end-to-end high-degree `Delta + 3` conclusion from graph hypotheses alone;
- existence, for every nonempty graph in the intended high-degree regime, of
  the equitable independent partition with `D = G.maxDegree + 1`;
- the prospective complement-matching construction that would supply that
  partition;
- the separate empty-graph base case;
- the resulting end-to-end total-coloring corollary from an arbitrary input
  graph;
- the stronger auxiliary `D + 1` palette; or
- novelty of any checked result.

!!! warning "Palette warning"

    `Fin (D + 2)` is the generic auxiliary palette parameter. With
    `D = Delta(G) + 1`, the supplied-partition theorem checks a conditional
    `Delta + 3` total assignment. It does not produce the required partition
    for an arbitrary target graph, so it is not an end-to-end `Delta + 3`
    theorem. No `Delta + 2` conclusion is checked.

## Provenance and distribution status

- The terminal theorem was introduced at `310b82c…`.
- Public Lean CI run
  [`29588129760`](https://github.com/chenle02/total-coloring-lean/actions/runs/29588129760)
  passed at that exact commit.
- The conditional transfer theorem was introduced at `9bdcdec…`; its proof
  source passed the full Easley build and leanchecker gate in Slurm job
  `5387732` (`COMPLETED`, exit `0:0`). The exact merged tree `c332155a…` then
  passed the same complete gate in job `5387751` (`COMPLETED`, exit `0:0`).
- PR [#6](https://github.com/chenle02/total-coloring-lean/pull/6)
  merged the transfer into `main` at `8ec71e7…`. Public Lean CI run
  [`29597109189`](https://github.com/chenle02/total-coloring-lean/actions/runs/29597109189)
  passed at PR head `16fca45…`, whose Git tree is identical to the merge
  commit's tree.
- The supplied pair/singleton seam was introduced at `dc2a318…` on draft PR
  [#8](https://github.com/chenle02/total-coloring-lean/pull/8). Its exact Git
  tree `883b6895…` passed cache refresh, leaf, umbrella, full package,
  Quickstart, forbidden-token, and leanchecker gates in Easley job `5387831`
  (`COMPLETED`, exit `0:0`). It is not on `main` unless PR #8 has since merged.
- The qualitative structural layer is commit `7aa102b…`, exact Git tree
  `4b6440a0df108f47f5c120e7e0187c058a462138`. Exact-tree leaf job `5387867`
  passed. Full Easley job `5387870` then passed cache refresh, umbrella and
  package builds, Quickstart, forbidden-token, and leanchecker gates
  (`COMPLETED`, exit `0:0`, node402); independent trust job `5387882` also
  passed. Earlier job `5387869` was canceled before running because of its
  scheduler delay and is not a verification receipt.
- The numerical layer's private verification source is commit
  `acb08de85f99c7db578e042e67d3f172c5599fcd`, exact Git tree
  `7207e2a282ff829fba9737e93154f46f385ef879`. Its source archive has SHA-256
  `5c3bef3720abeb62d0c437fbc638fe1848059892fbe09fe0c437c942c16baf5c`.
  The numerical Lean content was integrated unchanged at public PR commit
  `343b7b87b82532a9d8eade6d4cd43679eae1f7c9`, tree
  `9863f500b2671048f4dc386f497eb6523b065099`; the repository trees differ
  because the public commit integrates that content onto the PR branch.
- Exact-tree leaf job `5387926` passed (`COMPLETED`, exit `0:0`). Full build and
  leanchecker gate `5387929` passed (`COMPLETED`, exit `0:0`, node417, elapsed
  `00:13:58`, MaxRSS `118904036K`, requested memory `180G`). Its outgoing cache
  SHA-256 is
  `b89abc4f66841c91d6ec7f9d7cc1318267e30c7d8710236222c716067c801770`.
- Independent full/checker trust-v3 job `5387978` passed (`COMPLETED`, exit
  `0:0`, node419, elapsed `00:13:18`, MaxRSS `140835428K`, requested memory
  `330G`). Nova job `5387933` was a separate build-only lane without
  leanchecker and passed (`COMPLETED`, exit `0:0`, node801, elapsed `00:05:49`,
  MaxRSS `1293132K`).
- Diagnostic jobs `5387930` and `5387932` are not receipts and are not proof
  failures: the former omitted `lake exe cache get`; the latter used an older
  cache missing a private Mathlib artifact.
- At public integration commit `343b7b8…`, GitHub
  [Lean CI run 29612994477](https://github.com/chenle02/total-coloring-lean/actions/runs/29612994477)
  and [docs run 29612994502](https://github.com/chenle02/total-coloring-lean/actions/runs/29612994502)
  both succeeded. PR #8 remains draft.
- The supplied equitable-partition adapter is commit
  `a441fbfa1e404dc7610e0c32c80dd692cd938c20`, exact tree
  `0e9b04a2acabae0cb0612e5e3cbf0344cc2f94f7`. The source archive SHA-256 is
  `736db25ca7d25fb0eed8431e435e80bc94287e1ae88f9dea806ddba2c1b544f4`.
  Leaf job `5387980` passed (`COMPLETED`, exit `0:0`, node801, elapsed
  `00:00:49`, MaxRSS `1811196K`). Nova full build job `5387981` passed
  (`COMPLETED`, exit `0:0`, node801, elapsed `00:01:47`, MaxRSS `1962516K`).
  High-memory full/Quickstart/leanchecker trust job `5387982` passed
  (`COMPLETED`, exit `0:0`, node422, elapsed `00:14:09`, MaxRSS `144777340K`,
  requested memory `330G`). The outgoing cache SHA-256 is
  `94456901604a3b6ecde49368a4ba285fda03ecdca856b0c37f207624527e037a`.
- Release `v0.1.0` predates these result layers. Cite an exact commit or
  verified source tree until a later release includes the result used.

For tools, the same boundary is mirrored in
[`claim-boundary.json`](claim-boundary.json). The Lean declarations at the
pinned commit remain authoritative if prose and code ever disagree.
