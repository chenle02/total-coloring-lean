<div align="center">
  <img src="docs/assets/logo.svg" width="150" alt="Total Coloring Lean graph logo">
  <h1>Total Coloring Lean</h1>
  <p><strong>Kernel-checked Lean 4 foundations for total coloring and auxiliary rainbow edge coloring.</strong></p>

  <p>
    <a href="https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml"><img alt="Lean CI status" src="https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml/badge.svg"></a>
    <a href="https://chenle02.github.io/total-coloring-lean/"><img alt="Project documentation" src="https://img.shields.io/badge/docs-GitHub%20Pages-4051b5?logo=materialformkdocs&logoColor=white"></a>
    <a href="https://github.com/chenle02/total-coloring-lean/releases"><img alt="Latest release" src="https://img.shields.io/github/v/release/chenle02/total-coloring-lean?display_name=tag"></a>
    <a href="https://doi.org/10.5281/zenodo.23452514"><img alt="DOI 10.5281/zenodo.23452514" src="https://zenodo.org/badge/DOI/10.5281/zenodo.23452514.svg"></a>
    <a href="lean-toolchain"><img alt="Lean version 4.32.0" src="https://img.shields.io/badge/Lean-4.32.0-0f766e"></a>
    <a href="LICENSE"><img alt="Apache-2.0 license" src="https://img.shields.io/badge/license-Apache--2.0-4338ca"></a>
    <a href="https://github.com/sponsors/chenle02"><img alt="Sponsor on GitHub" src="https://img.shields.io/badge/sponsor-GitHub-e11d48?logo=githubsponsors&logoColor=white"></a>
  </p>

  <p>
    <a href="https://chenle02.github.io/total-coloring-lean/"><strong>Documentation</strong></a>
    · <a href="docs/getting-started.md">Get started</a>
    · <a href="docs/proof-status.md">Exact proof status</a>
    · <a href="docs/theorem-index.md">Theorem index</a>
    · <a href="llms.txt">LLM index</a>
  </p>
</div>

> [!IMPORTANT]
> The default branch proves an all-orders **auxiliary edge-coloring theorem**,
> a **conditional auxiliary-to-total transfer**, and the formal high-degree
> theorem `TotalColoring.exists_valid_assignment_of_highDegree`. Current
> `main` commit `da0595da1fa93c51a00be78193071bdea74aeb02`, tree
> `34824cd54afb9a244a3fb58608a8d4da9bd6cfa6`, also contains the declarations
> first checked on proof branch `agent/independent-seed-endpoint`, at exact
> source commit
> `cc4dd7ae1d858ea0583549f88707952e2414bf60` and tree
> `9af6a84e1305aed9a0156dcd59c279de792dea4a`: the conditional endpoint
> `TotalColoring.exists_valid_assignment_of_independentSeedPeel` and its
> maximum-degree wrapper
> `TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel`.
> The high-degree theorem produces a valid total assignment with
> `G.maxDegree + 3` colors from
> `Fintype.card V ≤ 2 * G.maxDegree`. The endpoint produces an assignment in
> `Fin (q + 1)` only from a supplied proper `Fin q` edge coloring, a supplied
> independent seed, and a supplied peel certificate, with `0 < q`. Setting
> `q = G.maxDegree + 1` therefore gives a conditional `Delta + 2` palette, but
> the library does not prove Vizing's theorem or existence of the required
> seed/certificate. Current `main` also contains the later selector layer,
> whose historical proof source was branch
> `agent/total-independent-selector-decoder` at commit
> `d008514c7a1cf834007bf0bd8de0d10a93926711` and tree
> `1847934c78da03fe80bb67236868700c79016129`. This layer checks a more general decoder:
> an independent fresh-color vertex set may be combined with a matching of
> fresh-color edges avoiding that set. It also checks the donor exchange from
> an explicitly supplied alternating rainbow-path certificate. These results
> remain conditional on their edge coloring, selector/core, path, and peel
> inputs, and the merged partial-edge normalization likewise begins its
> reverse direction with a supplied valid coloring. The adapted-spare layer,
> merged into `main` by PR #13, adds only an exact vertex-side endpoint
> properness equivalence; it does not construct donors or a coloring. The
> library does not prove the unrestricted Total Coloring
> Conjecture, the manuscript's still-unlocked main theorem, or novelty.

## The checked results

For every finite formal member of the matching-plus-star auxiliary class, Lean
proves the implication

```text
InAuxiliaryClass D H J
  →
HasValidRainbowColoring D H J.
```

The terminal declaration is
[`TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass`](https://github.com/chenle02/total-coloring-lean/blob/310b82c174ab2281581900897d4646875575e89b/TotalColoring/CriticalAllDClosure.lean).
It produces a propositional existence result: a proper auxiliary edge
assignment with palette `Fin (D + 2)` whose colors are pairwise distinct on
the distinguished set `J`.

The library now also proves the exact composition theorem
[`TotalColoring.Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass`](https://github.com/chenle02/total-coloring-lean/blob/9bdcdec1a872ccef42cfd79e791fe39c22a1beeb/TotalColoring/AuxiliaryTransfer.lean).
Given a supplied conflict-preserving `Auxiliary.Extension G H`, proof that
every vertex selector edge lies in the distinguished set, and
`InAuxiliaryClass D H J`, it yields

```text
exists assignment : Assignment G (Fin (D + 2)), assignment.Valid.
```

This closes the abstract auxiliary-existence-theorem-to-decoder composition.
The transfer theorem itself does not construct the extension from an arbitrary
graph or relate `D` to that graph's maximum degree.

The supplied-witness seam is now also checked. On a finite vertex type with
decidable equality, given
`P : TotalColoring.Auxiliary.PairSingletonWitness G`, Lean defines the ordinary
graph `P.auxiliaryGraph` on `Option V`, packages
`P.extension : Auxiliary.Extension G P.auxiliaryGraph`, and proves
`P.classEdge_mem_distinguishedEdgeSet`. The structural layer at
[`7aa102b`](https://github.com/chenle02/total-coloring-lean/commit/7aa102b0211c36c6d69f03bc051a5c2706f62c9d)
additionally proves exact distinguished-edge coverage of every copied
original vertex,
defines the off-center `P.matchingPart`, proves that it is a matching whose
endpoints avoid the center and all center neighbors, and proves

```text
P.distinguished =
  P.matchingPart ∪ P.auxiliaryGraph.incidenceFinset none.
```

The numerical bridge at public PR integration commit
[`343b7b8`](https://github.com/chenle02/total-coloring-lean/commit/343b7b87b82532a9d8eade6d4cd43679eae1f7c9)
additionally proves the exact identities

```text
P.auxiliaryGraph.degree (some v) = G.degree v + 1
Fintype.card V + P.auxiliaryGraph.degree none =
  2 * P.distinguished.card.
```

Thus `P.isAuxiliaryClassMember_of_class_count_and_bounds D` derives the former
maximum-degree and center-degree obligations from

```text
P.distinguished.card = D
G.maxDegree + 1 ≤ D
Fintype.card V + 2 ≤ 2 * D.
```

Beyond the ambient `[Fintype V]`, `[DecidableEq V]`,
`[DecidableRel G.Adj]`, and
`[DecidableRel P.auxiliaryGraph.Adj]` typeclass requirements, the specialization
`P.isAuxiliaryClassMember_of_highDegree` has only these additional
proposition-valued hypotheses:

```text
P.distinguished.card = G.maxDegree + 1
Fintype.card V ≤ 2 * G.maxDegree
```

It concludes `IsAuxiliaryClassMember (G.maxDegree + 1)` for the constructed
auxiliary graph and distinguished family.

The supplied-partition adapter is also checked. An
`EquitableIndependentPartition G D` packages exactly `D` nonempty independent
classes whose sizes differ by at most one. Given

```text
D ≤ Fintype.card V
Fintype.card V < 2 * D,
```

`Q.toPairSingletonWitness` constructs the witness and `Q.distinguished_card`
proves its concrete `J.card = D` identity. For a nonempty finite graph with
decidable vertex equality and adjacency, the terminal theorem
`Q.exists_valid_assignment_of_highDegreePartition` has the explicit inputs

```text
Q : EquitableIndependentPartition G (G.maxDegree + 1)
Fintype.card V ≤ 2 * G.maxDegree
```

and produces a valid total assignment with palette
`ExtensionPalette (G.maxDegree + 1)`, hence `G.maxDegree + 3` colors.

The complement-matching route and empty-vertex case are now checked as well.
The terminal declaration

```text
TotalColoring.exists_valid_assignment_of_highDegree
```

has only the finite/decidable graph structure and the explicit density
hypothesis

```text
Fintype.card V ≤ 2 * G.maxDegree.
```

It constructs the required complement matching, trims it to the exact size,
builds the pair/singleton witness, invokes the auxiliary theorem and decoder,
and produces

```text
∃ assignment : Assignment G (ExtensionPalette (G.maxDegree + 1)),
  assignment.Valid.
```

Here `ExtensionPalette (G.maxDegree + 1)` has cardinality
`G.maxDegree + 3`. The theorem covers both empty and nonempty finite vertex
types and assumes neither even order nor any other parity condition.

### Conditional independent-seed endpoint on `main`

The declarations are available on current `main` commit `da0595da…`, tree
`34824cd5…`. Their historical proof source is commit
[`cc4dd7ae`](https://github.com/chenle02/total-coloring-lean/commit/cc4dd7ae1d858ea0583549f88707952e2414bf60),
exact tree `9af6a84e1305aed9a0156dcd59c279de792dea4a`. The separate declaration
`TotalColoring.exists_valid_assignment_of_independentSeedPeel` has the
following explicit supplied-input boundary on a finite graph with decidable
vertex equality and adjacency:

```text
0 < q
phi : EdgeAssignment G (Fin q)
phi.Valid
A : Finset V
G.IsIndepSet (A : Set V)
cert : IndependentSeedPeelCertificate G A q
------------------------------------------------------------
exists assignment : Assignment G (Fin (q + 1)), assignment.Valid
```

The certificate gives a duplicate-free deletion order covering exactly the
vertices outside `A`; at each step, the number of neighbors later in the order
is strictly less than `q - G.degree v`. Lean checks the reverse greedy
construction: vertices in `A` use the one fresh color, while every other
vertex receives an old-palette color missing from its incident edges and not
used by its already colored neighbors.

If `q = G.maxDegree + 1`, the conclusion has palette
`Fin (G.maxDegree + 2)`. This is a conditional `Delta + 2` implication, not an
unrestricted theorem: the declaration does not construct the proper
`(Delta + 1)`-edge coloring (the Vizing seam), the independent seed, or its
peel certificate. It therefore does not prove the Total Coloring Conjecture
and does not strengthen the unconditional scope of the high-degree
`Delta + 3` theorem.

For copyable downstream use, the direct wrapper
`TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel`
specializes the same implication without a separate `q` argument:

```text
phi : EdgeAssignment G (Fin (G.maxDegree + 1))
phi.Valid
A : Finset V
G.IsIndepSet (A : Set V)
cert : IndependentSeedPeelCertificate G A (G.maxDegree + 1)
------------------------------------------------------------
exists assignment : Assignment G (Fin (G.maxDegree + 2)), assignment.Valid
```

This wrapper only performs the maximum-degree substitution. It still does not
construct `phi`, `A`, or `cert`.

The immutable proof source was independently replayed twice on Easley using a
sealed offline cache. Jobs `5389587` (node408, 11m40s, peak RSS `121378968K`)
and `5389588` (node412, 11m39s, peak RSS `122474236K`) both completed `0:0` and
passed exact-tree reconstruction, strict leaf compilation, umbrella and full
builds, Quickstart, the declaration/axiom audit, `leanchecker`, and metadata
gates. These receipts verify the displayed conditional declarations at source
tree `9af6a84e…`; they do not discharge any mathematical hypothesis.

### Total-independent selector decoder on `main`

The declarations are available on current `main` commit `da0595da…`, tree
`34824cd5…`. Historical proof branch
[`agent/total-independent-selector-decoder`](https://github.com/chenle02/total-coloring-lean/tree/agent/total-independent-selector-decoder)
introduced `TotalColoring.exists_valid_assignment_of_totalIndependentSelectorPeel`
at source commit
[`d008514`](https://github.com/chenle02/total-coloring-lean/commit/d008514c7a1cf834007bf0bd8de0d10a93926711),
exact tree `1847934c78da03fe80bb67236868700c79016129`. In addition to finite and
decidable graph structure, its explicit inputs are:

```text
phi : EdgeAssignment G (Fin q), with phi.Valid
S : Finset V, with G.IsIndepSet (S : Set V)
F : Finset G.edgeSet, a matching whose edges avoid S
K : Finset V
g0 : V -> Fin q
SelectorOldColoringGoodOn G phi S F K g0
SelectorCorePeelCertificate G S K q
------------------------------------------------------------
exists assignment : Assignment G (Fin (q + 1)), assignment.Valid
```

The selected vertices `S` and selected edges `F` receive the one fresh color.
The supplied core coloring uses old colors that avoid every incident edge
retaining its old color. The peel certificate covers exactly the vertices
outside `K` and uses the core-relative strict inequality

```text
(G.neighborFinset v ∩ ((K \ S) ∪ tail.toFinset)).card
  < q - G.degree v.
```

The same module defines
`AlternatingRainbowPathSelectorCertificate`. Given that certificate, the
wrapper `exists_valid_assignment_of_alternatingRainbowPathSelector` checks the
old-spare/fresh-edge donor exchange along the indexed rainbow path and then
invokes the general decoder. The certificate explicitly carries the path,
rainbow, unused-spare, matching, seed-avoidance, core-color, and peel facts;
the wrapper does not prove that such a path or certificate exists. Its
maximum-degree specialization concludes a valid assignment in
`Fin (G.maxDegree + 2)`, while the proper `(Delta + 1)` edge coloring and every
selector/path/core/peel witness remain inputs.

Sealed Easley job `5391803` checked the exact source tree on node411 and
completed `0:0` in 16m09s with peak RSS `125399676K`. It passed exact-tree
reconstruction, strict leaf compilation, target/umbrella/full builds,
Quickstart, the axiom audit, `leanchecker`, JSON/diff checks, and cache
archiving. The source archive SHA-256 is
`9ba0103e358cd761c6e591cfa00b13352236ff2b1774df1fd2f75cba8215561c`.
This receipt verifies the conditional decoder, not existence of its supplied
witnesses.

### Partial-edge selector normalization on `main`

The declarations are available on current `main` commit `da0595da…`, tree
`34824cd5…`. Historical stacked proof branch
[`agent/partial-edge-selector-normalization`](https://github.com/chenle02/total-coloring-lean/tree/agent/partial-edge-selector-normalization)
introduced a strictly weaker old-edge hypothesis at source commit
`c3dbe69c15f96e3c71d8481ae4e517ee2f4fdbf2`, exact source tree
`11007a4aa381984a8d66aa1db297312cebe8d8b5`. For a selected edge finset `F`,
`EdgeAssignment.ValidOutside F` requires distinct old colors only for adjacent
edges in `E(G) \ F`; values stored on `F` are ignored. If `F` is a matching,
`S` is independent, `F` avoids `S`, and every old vertex color avoids its
incident edges outside `F`, then

```lean
TotalColoring.partialEdgeSelectorAssignment_valid
```

sends both `S` and `F` to any chosen fresh color and returns a valid total
assignment. The last-color corollary
`totalIndependentSelectorAssignment_valid_of_validOutside` strengthens the
earlier decoder without changing its output format.

The same module formalizes the exact reverse bookkeeping. Given a *supplied*
valid `a : Assignment G (Fin (q + 1))`, a chosen fresh color, and an irrelevant
fallback in `Fin q`,

```lean
TotalColoring.partialEdgeSelectorNormalization_of_valid
```

takes `S` and `F` to be the corresponding vertex and edge color classes,
pulls every other color back through `fresh.succAbove`, proves all forward
hypotheses, and records literal equality `decodes = a`. The maximum-degree
notation wrapper starts from a supplied `Fin (G.maxDegree + 2)` coloring. This
reverse normalization does not construct such a coloring and is not a proof
of an unconditional `Delta + 2` result or the Total Coloring Conjecture.

All independent-seed, selector/path, partial-edge, and normalization
declarations displayed below are present on current `main` commit
`da0595da1fa93c51a00be78193071bdea74aeb02`, tree
`34824cd54afb9a244a3fb58608a8d4da9bd6cfa6`. Their earlier source
commits and trees above remain the provenance of the individual proof layers;
PRs #10, #11, and #12 merged the three layers into `main`.

```lean
import TotalColoring

#check TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.PairSingletonWitness.extension
#check TotalColoring.Auxiliary.PairSingletonWitness
  .classEdge_mem_distinguishedEdgeSet
#check TotalColoring.Auxiliary.PairSingletonWitness
  .isAuxiliaryClassMember_of_highDegree
#check TotalColoring.Auxiliary.EquitableIndependentPartition
  .distinguished_card
#check TotalColoring.Auxiliary.EquitableIndependentPartition
  .exists_valid_assignment_of_highDegreePartition
#check TotalColoring.exists_valid_assignment_of_highDegree
#check TotalColoring.exists_valid_assignment_of_independentSeedPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel
#check TotalColoring.SelectorCorePeelCertificate
#check TotalColoring.exists_valid_assignment_of_totalIndependentSelectorPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeTotalIndependentSelectorPeel
#check TotalColoring.AlternatingRainbowPathSelectorCertificate
#check TotalColoring.exists_valid_assignment_of_alternatingRainbowPathSelector
#check TotalColoring.exists_valid_assignment_of_maxDegreeAlternatingRainbowPathSelector
#check TotalColoring.EdgeAssignment.ValidOutside
#check TotalColoring.partialEdgeSelectorEdgeAssignment_valid
#check TotalColoring.partialEdgeSelectorAssignment_valid
#check TotalColoring.totalIndependentSelectorAssignment_valid_of_validOutside
#check TotalColoring.PartialEdgeSelectorNormalization
#check TotalColoring.partialEdgeSelectorNormalization_of_valid
#check TotalColoring.maxDegreePartialEdgeSelectorNormalization_of_valid
```

### Adapted-spare vertex endpoint on `main`

Historical proof branch `agent/donor-global-formalization` added
`TotalColoring.adaptedSpareVertexColor_proper_iff`. For a graph `K`, color
functions `missing head : V -> C`, finite sets `A B`, and supplied
`Disjoint A B`, the endpoint assignment gives `none` to `A`, `some (head v)`
to `B`, and `some (missing v)` elsewhere. The theorem proves that this vertex
assignment is proper on every edge of `K` if and only if all four conditions
hold:

1. `A` is independent in `K`;
2. every adjacent equal-`missing` pair has an endpoint in `A ∪ B`;
3. every head label differs from the missing color of each unchanged
   neighbor; and
4. donor labels are proper on the graph induced by `B`.

This is an exact vertex-side equivalence only. It does not construct `A` or
`B`, a physical donor matching, the `missing` or `head` data, a compatible
seed or matching, a proper edge coloring, or a total coloring. It proves
neither an unrestricted `Delta + 2` result nor the Total Coloring Conjecture.
PR #13 merged the declaration into `main` as commit `dc6e3a4b…` on
2026-07-20; it is part of current `main` commit `da0595da…`, tree
`34824cd5…`.

The all-orders theorem was introduced at commit
[`310b82c`](https://github.com/chenle02/total-coloring-lean/commit/310b82c174ab2281581900897d4646875575e89b)
and passed [public Lean CI at that exact
commit](https://github.com/chenle02/total-coloring-lean/actions/runs/29588129760).
The conditional transfer was introduced at
[`9bdcdec`](https://github.com/chenle02/total-coloring-lean/commit/9bdcdec1a872ccef42cfd79e791fe39c22a1beeb).
The supplied-witness extension seam was introduced at
[`dc2a318`](https://github.com/chenle02/total-coloring-lean/commit/dc2a318be1dd1475b90c492ad460c4180a3fbdec)
on PR [#8](https://github.com/chenle02/total-coloring-lean/pull/8). The
qualitative structural layer is commit `7aa102b…`, exact Git tree
`4b6440a0df108f47f5c120e7e0187c058a462138`. Its full cache-refresh, build,
Quickstart, forbidden-token, and leanchecker gate passed on Easley in job
`5387870` (`COMPLETED`, exit `0:0`); independent trust job `5387882` also
passed. The numerical layer was gated from private source commit
`acb08de85f99c7db578e042e67d3f172c5599fcd`, exact tree
`7207e2a282ff829fba9737e93154f46f385ef879`, then integrated with identical
numerical Lean content at public PR commit `343b7b8…`, tree
`9863f500b2671048f4dc386f497eb6523b065099`. Exact leaf job `5387926`, full
build/checker job `5387929`, and independent trust-v3 job `5387978` all
completed with exit `0:0`; Nova build-only job `5387933` also completed with
exit `0:0`. Public [Lean CI](https://github.com/chenle02/total-coloring-lean/actions/runs/29612994477)
and [docs](https://github.com/chenle02/total-coloring-lean/actions/runs/29612994502)
passed at `343b7b8…`. Jobs `5387930` and `5387932` were diagnostic
infrastructure failures, not verification receipts or proof failures. The
supplied-partition adapter is commit `a441fbf…`, exact code tree
`0e9b04a2acabae0cb0612e5e3cbf0344cc2f94f7`; its source-archive SHA-256 is
`736db25ca7d25fb0eed8431e435e80bc94287e1ae88f9dea806ddba2c1b544f4`.
Leaf job `5387980`, Nova full build job `5387981`, and high-memory
full/Quickstart/leanchecker trust job `5387982` all completed with exit `0:0`.
The outgoing-cache SHA-256 is
`94456901604a3b6ecde49368a4ba285fda03ecdca856b0c37f207624527e037a`.
The completed terminal proof tree is
`4624044788ab42c0dc116cfbf7f38c696065263c`; its source archive has SHA-256
`302bc3f00bf5d8c1ce563d2bc84d1370e627c81d219e8d8085b286a21d530077`.
Five separate terminal full-build, Quickstart, and leanchecker replays
(`5388311`--`5388315`) completed with exit `0:0` and empty stderr. These jobs
certify that exact proof tree only.

The publishable proof commit is
[`06d43af`](https://github.com/chenle02/total-coloring-lean/commit/06d43af7f4ea8fefea9e07e2bc29bdc960548171),
with exact Git tree `89a32c7a78e294a8b1484092ec79afaa3b4ace5a` and
source-archive SHA-256
`c9950b9e8af364a0d2ef3c08d80f06786ea36d3e6a5bf728054f7824612b4331`.
Wave 11 leaf job `5388961` passed, and the union of the original matrix plus
narrow harness/runtime repairs covered all 64 distinct verification roles.
Container job `5389029` passed `mk_all --check`; independent host trust jobs
`5389030`, `5389031`, and `5389032` passed cache refresh, the terminal target,
umbrella and full builds, Quickstart/API checks, the proof-escape scan, and
`leanchecker` on that exact tree. PR-head Lean/docs runs
[`29622668742`](https://github.com/chenle02/total-coloring-lean/actions/runs/29622668742)
and
[`29622668714`](https://github.com/chenle02/total-coloring-lean/actions/runs/29622668714)
passed. PR #8 merged as
[`0e93860`](https://github.com/chenle02/total-coloring-lean/commit/0e938606f81e7a27a5925987824e7152f7dbb4c6),
whose tree is exactly the verified tree; post-merge main Lean/docs runs
[`29622728654`](https://github.com/chenle02/total-coloring-lean/actions/runs/29622728654)
and
[`29622728662`](https://github.com/chenle02/total-coloring-lean/actions/runs/29622728662)
also passed.
Release `v0.1.0` predates these result layers; cite the exact commit or a later
release that actually contains them.

### Exact boundary

The current default branch, including the adapted-spare endpoint, does not
establish:

- the Total Coloring Conjecture;
- an unconditional high-degree or all-graphs `Delta + 2` total-coloring
  conclusion;
- an unconditional total-coloring conclusion from graph hypotheses alone for
  graphs outside the explicit high-degree regime
  `Fintype.card V ≤ 2 * G.maxDegree`;
- Vizing's theorem or existence of the proper edge-coloring witness required
  by the conditional independent-seed endpoint;
- existence of an independent seed and peel certificate for every graph;
- existence of a total-independent selector, an actual-list coloring of its
  core, a core-relative peel certificate, or the alternating rainbow-path
  certificate used by the newer decoder;
- construction of the adapted-spare sets, a physical donor matching,
  compatible seed or matching data, missing/head labels, or a proper edge
  coloring needed before the vertex endpoint can apply;
- the stronger auxiliary `D + 1` palette;
- an identification of the checked declaration with a final, author-approved
  manuscript theorem; or
- a novelty claim.

In the all-orders theorem, `Fin (D + 2)` is the auxiliary edge-coloring
palette; in the generic conditional transfer, the same type colors the
supplied original graph while `D` remains abstract. The terminal high-degree
theorem sets `D = Delta(G) + 1`, constructs the required witness from a
complement matching, and checks a `Delta + 3` conclusion directly from
`|V(G)| ≤ 2 Delta(G)`. It also handles the empty vertex type and has no parity
hypothesis. This terminal high-degree statement must not be broadened into an
unconditional `Delta + 2` result, the Total Coloring Conjecture, or an
author-approved manuscript or novelty claim.
The separate independent-seed endpoint reaches a `Delta + 2` palette only
after its proper edge coloring, independent seed, and peel certificate have
all been supplied; it does not discharge those hypotheses.
The total-independent selector decoder permits both fresh-color vertices and
fresh-color matching edges, but likewise reaches that palette only after its
proper edge coloring, selector/core data, and peel certificate have been
supplied. Its alternating-path wrapper proves the donor exchange from the
explicit certificate; it does not prove the certificate exists.
The adapted-spare theorem is an exact vertex-properness equivalence
for supplied data. It constructs no donor matching, proper edge coloring, or
total coloring and therefore does not close the unrestricted route.
See the
[human-readable boundary](docs/proof-status.md) or its
[machine-readable mirror](docs/claim-boundary.json).

## Build in three commands

The repository pins Lean and mathlib to `v4.32.0`.

```sh
lake exe cache get
lake build
lake env lean docs/examples/Quickstart.lean
```

For a fresh machine, first install
[`elan`](https://lean-lang.org/lean4/doc/setup.html). The
[getting-started guide](docs/getting-started.md) covers downstream imports,
documentation builds, and the complete contribution gate.

## Proof route

```text
auxiliary member
  → finite minimal counterexample
  → maximal valid rainbow one-hole state
  → fans, pivots, dominators, and robust columns
  → k = 1 / 2 / 3 external-source exhaustion
  → crossing and detachment contradiction
  → rainbow auxiliary coloring
  → conditional decode through a supplied compatible extension
  → valid total assignment

high-degree finite graph
  → large complement matching
  → exact-size complement matching
  → pair/singleton witness in the auxiliary class
  → auxiliary coloring and conditional decode
  → valid total assignment with Delta(G) + 3 colors
```

The [proof architecture](docs/architecture.md) maps these stages to Lean
modules. The [curated theorem index](docs/theorem-index.md) lists the public
definitions, terminal theorems, decoder, and checker soundness entrypoints.

## Trust and reproducibility

- Production Lean modules contain no `sorry`, `admit`, custom `axiom`, or
  `native_decide`.
- Executable certificate checkers are connected to semantic predicates by
  soundness theorems.
- External solver output is untrusted until a checker accepts a well-typed
  assignment.
- A verified positive assignment does not establish completeness of an
  external graph enumeration.
- The umbrella `TotalColoring.lean` directly imports every production module.

Read [Trust and reproduction](docs/trust.md) for the full gate and parser
boundary.

## Find your way

| If you want to… | Start here |
| --- | --- |
| understand exactly what is proved | [Exact proof status](docs/proof-status.md) |
| use a declaration in Lean | [Theorem index](docs/theorem-index.md) |
| audit the module-level proof | [Proof architecture](docs/architecture.md) |
| contribute a proof or checker | [CONTRIBUTING.md](CONTRIBUTING.md) and [AGENTS.md](AGENTS.md) |
| use a coding agent safely | [Agent guide](docs/for-agents.md) and [`llms.txt`](llms.txt) |
| cite the software precisely | [Citation guide](docs/citation.md) and [CITATION.cff](CITATION.cff) |

## Companion repositories

- [`total-coloring-toolkit`](https://github.com/chenle02/total-coloring-toolkit)
  owns search algorithms, external schemas, and certificate generation.
- [`total-coloring-data`](https://github.com/chenle02/total-coloring-data)
  owns reviewed finite artifacts and release manifests.

Raw runs, private drafts, manuscript source, and generated census output do
not belong in this repository.

## Contribute, cite, and support

Small, reviewable contributions are welcome. Open an issue before changing a
mathematical interface or theorem claim, preserve the trust boundary, and run
the complete gate in `AGENTS.md`.

If you use the project, cite the exact release or commit you used. GitHub reads
the included `CITATION.cff` and exposes a **Cite this repository** menu.
Release `v0.2.0` is archived on Zenodo as
[doi:10.5281/zenodo.23452514](https://doi.org/10.5281/zenodo.23452514)
(all versions: [doi:10.5281/zenodo.23452513](https://doi.org/10.5281/zenodo.23452513)).

[GitHub Sponsors](https://github.com/sponsors/chenle02) supports formalization
maintenance, documentation, CI and cluster verification, and reproducible
releases. Sponsorship does not affect theorem claims or proof-review standards.

## Acknowledgments

The receipts of release v0.2.0 (commit `c025d20a1826`, lower tier and
comparator) were produced on a lab workstation.
Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg)
([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

## License

Copyright © 2026 Le Chen and contributors. Distributed under the
[Apache License 2.0](LICENSE) (see also `NOTICE`); every Lean file carries the
standard Apache header, and contributions are accepted under the same license.


<!-- lean-pkg:page:begin -->
<!-- Generated by `lean-pkg page total-coloring-lean` from coverage.yaml, claims.yaml, the claims ledger and the receipts committed under .lean-receipts/. Do not edit between the markers: change the data and run `lean-pkg page total-coloring-lean --write`. -->

## Verification at a glance

**How to read this page.** Lean has checked every step of the proofs listed here. Each result is exactly its Lean statement: read the statements below to see what is proved. The titles, the words and the notes are the authors' description, which Lean does not check.

Unconditionally, every finite graph with \|V\| &lt;= 2 \* maxDegree has a total coloring with maxDegree + 3 colors, and every finite auxiliary-class member has a (D + 2)-edge coloring rainbow on J; the D + 2 transfer, the partition entry point and the (q + 1)-color endpoints are conditional on supplied inputs, and the Total Coloring Conjecture is not proved.

- Main results: 13; verified: 13 of 13 (for 8 of them a second checker also compared the statement).

## Main results

### Total coloring with maxDegree + 3 colors when \|V\| &lt;= 2 \* maxDegree

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $G$ be a finite simple graph on the vertex set $V$ with
$|V| \le 2\Delta(G)$. Then $G$ has a total coloring with the
$\Delta(G)+3$ colors $\{0,1,\dots,\Delta(G)+2\}$: adjacent vertices get
distinct colors, two distinct edges sharing an endpoint get distinct
colors, and every vertex gets a color different from each edge
incident with it.
```

**In Lean.** `TotalColoringAudit.HighDegree.exists_total_coloring_of_card_le_two_mul_maxDegree` in [Audit/HighDegree/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/HighDegree/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_total_coloring_of_card_le_two_mul_maxDegree
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ (vertexColor : V → Fin (G.maxDegree + 1 + 2))
      (edgeColor : G.edgeSet → Fin (G.maxDegree + 1 + 2)),
      (∀ v w, G.Adj v w → vertexColor v ≠ vertexColor w) ∧
      (∀ e f, G.lineGraph.Adj e f → edgeColor e ≠ edgeColor f) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) → vertexColor v ≠ edgeColor e)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Unconditional: the only hypotheses are a finite vertex type, decidable adjacency and the order bound; the empty vertex type is included and there is no parity hypothesis. ExtensionPalette (maxDegree + 1) is Fin (maxDegree + 3).

### Every finite auxiliary-class member has a (D + 2)-edge coloring rainbow on its distinguished set

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $H$ be a finite simple graph and $J$ a finite set of unordered pairs
of vertices such that $(H,J)$ is in the auxiliary class
$\mathcal{A}_D$: there are a vertex $x$ and a set $M$ of pairwise
disjoint pairs with $J = M \cup \{\text{edges of } H \text{ at } x\}$,
every pair of $J$ an edge of $H$, no pair of $M$ containing $x$ or a
neighbor of $x$, every vertex other than $x$ in exactly one pair of $J$,
$|J| = D$, $\Delta(H) \le D$ and $2 \le \deg_H(x) \le D$. Then $H$ has a
proper edge coloring with $D+2$ colors in which the edges of $J$ get
pairwise distinct colors.
```

**In Lean.** `TotalColoringAudit.AuxiliaryClass.exists_rainbow_edge_coloring_of_auxiliaryClass` in [Audit/AuxiliaryClass/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/AuxiliaryClass/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_rainbow_edge_coloring_of_auxiliaryClass
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj]
    (J : Finset (Sym2 V)) (x : V) (M : Finset (Sym2 V))
    (distinguished_edges : ∀ ⦃e⦄, e ∈ J → e ∈ H.edgeSet)
    (matching : ∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f)
    (matching_off_center : ∀ ⦃e⦄, e ∈ M → x ∉ e)
    (matching_avoids_center_neighbors : ∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H.Adj x v)
    (decomposition : J = M ∪ H.incidenceFinset x)
    (exact_coverage : ∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e)
    (card_distinguished : J.card = D)
    (maxDegree_bound : H.maxDegree ≤ D)
    (center_degree : 2 ≤ H.degree x ∧ H.degree x ≤ D) :
    ∃ color : H.edgeSet → Fin (D + 2),
      (∀ e f, H.lineGraph.Adj e f → color e ≠ color f) ∧
      (∀ e f : H.edgeSet, (e : Sym2 V) ∈ J → (f : Sym2 V) ∈ J → e ≠ f →
        color e ≠ color f)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Unconditional for every D and every finite member; proved by contradiction from the minimal-counterexample theorem below.

### No auxiliary-class member is noncolorable and minimal in the number of edges outside J

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
There is no finite $(H,J) \in \mathcal{A}_D$ such that $H$ has no proper
$(D+2)$-edge coloring rainbow on $J$, while every $(H',J) \in
\mathcal{A}_D$ on the same vertex set, with the same $J$ and with no such
coloring, has at least as many edges outside $J$ as $H$.
```

**In Lean.** `TotalColoringAudit.CriticalAllD.false_of_critical_allD` in [Audit/CriticalAllD/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/CriticalAllD/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem false_of_critical_allD
    {V : Type*} [Fintype V] [DecidableEq V]
    (D : ℕ) (H : SimpleGraph V) [DecidableRel H.Adj] (J : Finset (Sym2 V))
    (member : ∃ (x : V) (M : Finset (Sym2 V)),
      (∀ ⦃e⦄, e ∈ J → e ∈ H.edgeSet) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f) ∧
      (∀ ⦃e⦄, e ∈ M → x ∉ e) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H.Adj x v) ∧
      J = M ∪ H.incidenceFinset x ∧
      (∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e) ∧
      J.card = D ∧
      H.maxDegree ≤ D ∧
      (2 ≤ H.degree x ∧ H.degree x ≤ D))
    (noncolorable : ¬∃ color : H.edgeSet → Fin (D + 2),
      (∀ e f, H.lineGraph.Adj e f → color e ≠ color f) ∧
      (∀ e f : H.edgeSet, (e : Sym2 V) ∈ J → (f : Sym2 V) ∈ J → e ≠ f →
        color e ≠ color f))
    (minimal : ∀ (H₁ : SimpleGraph V) [DecidableRel H₁.Adj],
      (∃ (x : V) (M : Finset (Sym2 V)),
        (∀ ⦃e⦄, e ∈ J → e ∈ H₁.edgeSet) ∧
        (∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f) ∧
        (∀ ⦃e⦄, e ∈ M → x ∉ e) ∧
        (∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬H₁.Adj x v) ∧
        J = M ∪ H₁.incidenceFinset x ∧
        (∀ v, v ≠ x → ∃! e : Sym2 V, e ∈ J ∧ v ∈ e) ∧
        J.card = D ∧
        H₁.maxDegree ≤ D ∧
        (2 ≤ H₁.degree x ∧ H₁.degree x ≤ D)) →
      (¬∃ color : H₁.edgeSet → Fin (D + 2),
        (∀ e f, H₁.lineGraph.Adj e f → color e ≠ color f) ∧
        (∀ e f : H₁.edgeSet, (e : Sym2 V) ∈ J → (f : Sym2 V) ∈ J → e ≠ f →
          color e ≠ color f)) →
      (H.edgeSet \ (J : Set (Sym2 V))).ncard ≤ (H₁.edgeSet \ (J : Set (Sym2 V))).ncard) :
    False
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** The minimal-counterexample step behind the rainbow theorem above; the minimality ranges over members on the same vertex type with the same J.

### A proper selector-rainbow auxiliary edge coloring decodes to a valid total coloring

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $G$ and $H$ be simple graphs with an extension datum: a selector
edge $s(v)$ of $H$ for each vertex $v$ of $G$ and an edge $\iota(e)$ of
$H$ for each edge $e$ of $G$, such that adjacent vertices have distinct
selectors, distinct edges of $G$ sharing an endpoint go to distinct edges
of $H$ sharing an endpoint, and $s(v)$ and $\iota(e)$ are distinct and
share an endpoint whenever $v$ is an endpoint of $e$. If $c$ is a proper
edge coloring of $H$ that gives distinct selector edges distinct colors,
then coloring each vertex $v$ by $c(s(v))$ and each edge $e$ by
$c(\iota(e))$ is a valid total coloring of $G$.
```

**In Lean.** `TotalColoringAudit.Decode.decode_valid` in [Audit/Decode/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/Decode/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem decode_valid
    {V : Type*} {W : Type*} {C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (classEdge : V → H.edgeSet) (originalEdge : G.edgeSet → H.edgeSet)
    (classEdge_ne_of_adj : ∀ {v w : V}, G.Adj v w → classEdge v ≠ classEdge w)
    (originalEdge_adj : ∀ {e f : G.edgeSet}, G.lineGraph.Adj e f →
      H.lineGraph.Adj (originalEdge e) (originalEdge f))
    (classEdge_adj_original : ∀ {v : V} {e : G.edgeSet}, v ∈ (e : Sym2 V) →
      H.lineGraph.Adj (classEdge v) (originalEdge e))
    (color : H.edgeSet → C)
    (hvalid : ∀ e f, H.lineGraph.Adj e f → color e ≠ color f)
    (hrainbow : ∀ v w, classEdge v ≠ classEdge w →
      color (classEdge v) ≠ color (classEdge w)) :
    (∀ v w, G.Adj v w → color (classEdge v) ≠ color (classEdge w)) ∧
      (∀ e f, G.lineGraph.Adj e f → color (originalEdge e) ≠ color (originalEdge f)) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) →
        color (classEdge v) ≠ color (originalEdge e))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** No finiteness and any color type; the extension data are hypotheses.

### Conditional transfer: a supplied extension into an auxiliary-class member gives a total coloring with D + 2 colors

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check that applies to this result passed (the build; its statement was not compared by a second checker).

**In words.**

```latex
Let $G$ be a simple graph and $H$ a finite simple graph with
$(H,J) \in \mathcal{A}_D$. If there is an extension datum from $G$ to $H$
(as in the decoding theorem) every selector edge of which belongs to
$J$, then $G$ has a valid total coloring with $D+2$ colors.
```

**In Lean.** `TotalColoring.Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` in [TotalColoring/AuxiliaryTransfer.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/TotalColoring/AuxiliaryTransfer.lean).

```lean
theorem exists_valid_decode_of_inAuxiliaryClass
    [Fintype W] [DecidableEq W]
    (D : ℕ) (X : Extension G H) [DecidableRel H.Adj]
    (J : Finset (Sym2 W))
    (hclassEdge : ∀ vertex, X.classEdge vertex ∈ distinguishedEdgeSet H J)
    (hmember : InAuxiliaryClass D H J) :
    ∃ assignment : Assignment G (ExtensionPalette D), assignment.Valid
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Conditional on the supplied extension datum, selector membership in J and the auxiliary-class membership; nothing relates D to the maximum degree of G.

### A matching with at least k edges from minimum degree k and order at least 2k

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $H$ be a finite simple graph on $V$ and $k \ge 0$. If every vertex
has degree at least $k$ in $H$ and $2k \le |V|$, then $H$ has a subgraph
in which every vertex has at most one neighbor (a matching) with at
least $k$ edges.
```

**In Lean.** `TotalColoringAudit.MatchingLowerBound.exists_matchingGraph_edgeFinset_card_ge` in [Audit/MatchingLowerBound/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/MatchingLowerBound/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem exists_matchingGraph_edgeFinset_card_ge
    {V : Type*} [Fintype V]
    (H : SimpleGraph V) [DecidableRel H.Adj] (k : ℕ)
    (hdegree : ∀ v, k ≤ H.degree v) (horder : 2 * k ≤ Fintype.card V) :
    ∃ (M : SimpleGraph V) (_ : DecidableRel M.Adj),
      M ≤ H ∧ (∀ v, (M.neighborSet v).Subsingleton) ∧ k ≤ M.edgeFinset.card
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

### A pair/singleton partition with maxDegree + 1 classes gives auxiliary-class membership when \|V\| &lt;= 2 \* maxDegree

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $G$ be a finite simple graph on $V$ and fix a partition of $V$ into
singletons and pairs of nonadjacent vertices. On $V \cup \{\ast\}$ take
a copy of $G$ together with one selector edge per class: $\ast v$ for a
singleton $\{v\}$ and $vw$ for a pair $\{v,w\}$. Let $J$ be the set of
selector edges and $M$ the pair selectors. If $|J| = \Delta(G)+1$ and
$|V| \le 2\Delta(G)$, then this graph is a member of
$\mathcal{A}_{\Delta(G)+1}$ with center $\ast$, distinguished set $J$
and matching part $M$.
```

**In Lean.** `TotalColoringAudit.PairSingleton.isAuxiliaryClassMember_of_highDegree` in [Audit/PairSingleton/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/PairSingleton/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem isAuxiliaryClassMember_of_highDegree
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (partner : V → Option V)
    (partner_ne : ∀ {v w : V}, partner v = some w → v ≠ w)
    (partner_symm : ∀ {v w : V}, partner v = some w → partner w = some v)
    (partner_nonadjacent : ∀ {v w : V}, partner v = some w → ¬G.Adj v w)
    (selector : V → Sym2 (Option V))
    (hselector : ∀ v, selector v = (partner v).elim s(none, some v) (fun w ↦ s(some v, some w)))
    (J : Finset (Sym2 (Option V))) (hJ : J = Finset.univ.image selector)
    (M : Finset (Sym2 (Option V))) (hM : M = J.filter (fun e ↦ (none : Option V) ∉ e))
    (A : SimpleGraph (Option V))
    (hA : A = G.map Function.Embedding.some ⊔ SimpleGraph.fromEdgeSet (J : Set (Sym2 (Option V))))
    [DecidableRel G.Adj] [DecidableRel A.Adj]
    (hclasses : J.card = G.maxDegree + 1)
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    (∀ ⦃e⦄, e ∈ J → e ∈ A.edgeSet) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃f⦄, f ∈ M → e ≠ f → ∀ ⦃v⦄, v ∈ e → v ∉ f) ∧
      (∀ ⦃e⦄, e ∈ M → (none : Option V) ∉ e) ∧
      (∀ ⦃e⦄, e ∈ M → ∀ ⦃v⦄, v ∈ e → ¬A.Adj none v) ∧
      J = M ∪ A.incidenceFinset none ∧
      (∀ v, v ≠ none → ∃! e : Sym2 (Option V), e ∈ J ∧ v ∈ e) ∧
      J.card = G.maxDegree + 1 ∧
      A.maxDegree ≤ G.maxDegree + 1 ∧
      (2 ≤ A.degree none ∧ A.degree none ≤ G.maxDegree + 1)
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** The pair/singleton witness is a hypothesis here; the high-degree theorem above constructs one from a matching in the complement of G.

### Conditional: a supplied equitable independent partition gives a total coloring with maxDegree + 3 colors

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check that applies to this result passed (the build; its statement was not compared by a second checker).

**In words.**

```latex
Let $G$ be a finite simple graph on a nonempty vertex set $V$ with
$|V| \le 2\Delta(G)$. If $V$ is partitioned into exactly $\Delta(G)+1$
nonempty independent sets whose sizes differ by at most one, then $G$
has a valid total coloring with $\Delta(G)+3$ colors.
```

**In Lean.** `TotalColoring.Auxiliary.EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition` in [TotalColoring/EquitablePairSingleton.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/TotalColoring/EquitablePairSingleton.lean).

```lean
theorem exists_valid_assignment_of_highDegreePartition
    (Q : EquitableIndependentPartition G (G.maxDegree + 1))
    (hdense : Fintype.card V ≤ 2 * G.maxDegree) :
    ∃ assignment : Assignment G (ExtensionPalette (G.maxDegree + 1)),
      assignment.Valid
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Conditional on the supplied partition and a nonempty vertex type; retained as an alternate entry point. The high-degree theorem above assumes no partition.

### Conditional independent-seed endpoint: q + 1 colors from a proper q-edge coloring, an independent seed and a peel order

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check that applies to this result passed (the build; its statement was not compared by a second checker).

**In words.**

```latex
Let $G$ be a finite simple graph and $q > 0$. Suppose $G$ has a proper
edge coloring with $q$ colors, $A$ is an independent set of vertices,
and the vertices outside $A$ are listed without repetition as
$v_1,\dots,v_m$ (exactly the vertices outside $A$) so that for every $i$
the number of neighbors of $v_i$ among $v_{i+1},\dots,v_m$ is less than
$q - \deg_G(v_i)$ (truncated subtraction). Then $G$ has a valid total
coloring with $q+1$ colors. For $q = \Delta(G)+1$ this is
$\Delta(G)+2$ colors.
```

**In Lean.** `TotalColoring.exists_valid_assignment_of_independentSeedPeel` in [TotalColoring/IndependentSeed.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/TotalColoring/IndependentSeed.lean).

```lean
theorem exists_valid_assignment_of_independentSeedPeel {q : ℕ}
    (hq : 0 < q) (phi : EdgeAssignment G (Fin q)) (hphi : phi.Valid)
    (A : Finset V) (hA : G.IsIndepSet (A : Set V))
    (cert : IndependentSeedPeelCertificate G A q) :
    ∃ a : Assignment G (Fin (q + 1)), a.Valid
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Conditional: the edge coloring, the seed and the peel order are hypotheses. Vizing's theorem and the existence of the seed and order are not proved, so the maxDegree + 2 case is not the Total Coloring Conjecture.

### Conditional selector decoder: a fresh-color independent set and matching with a peeled core coloring give q + 1 colors

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check that applies to this result passed (the build; its statement was not compared by a second checker).

**In words.**

```latex
Let $G$ be a finite simple graph with a proper edge coloring $\varphi$
with $q$ colors. Let $S$ be an independent set, $F$ a matching none of
whose edges has an endpoint in $S$, and $K \supseteq S$ a vertex set
with $g_0 \colon V \to \{0,\dots,q-1\}$ such that for all
$v, w \in K \setminus S$: $g_0(v) \ne \varphi(e)$ for every edge
$e \notin F$ at $v$, and $g_0(v) \ne g_0(w)$ when $v$ and $w$ are
adjacent. Suppose the vertices outside $K$ are listed without repetition
as $v_1,\dots,v_m$ (exactly the vertices outside $K$) so that
$|N(v_i) \cap ((K \setminus S) \cup \{v_{i+1},\dots,v_m\})| <
q - \deg_G(v_i)$ (truncated subtraction) for every $i$. Then $G$ has a
valid total coloring with $q+1$ colors.
```

**In Lean.** `TotalColoring.exists_valid_assignment_of_totalIndependentSelectorPeel` in [TotalColoring/TotalIndependentSelector.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/TotalColoring/TotalIndependentSelector.lean).

```lean
theorem exists_valid_assignment_of_totalIndependentSelectorPeel
    (phi : EdgeAssignment G (Fin q)) (hphi : phi.Valid)
    (S : Finset V) (hS : G.IsIndepSet (S : Set V))
    (F : Finset G.edgeSet) (hF : EdgeFinsetIsMatching (G := G) F)
    (havoid : EdgeFinsetAvoids (G := G) F S)
    (K : Finset V) (g₀ : V → Fin q)
    (hcore : SelectorOldColoringGoodOn G phi S F K g₀)
    (cert : SelectorCorePeelCertificate G S K q) :
    ∃ a : Assignment G (Fin (q + 1)), a.Valid
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Conditional: the edge coloring, S, F, the core K, the core coloring g0 and the peel order are hypotheses; none of them is constructed.

### Partial-edge selector decoder: old edge colors need only be proper outside the fresh matching

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $G$ be a simple graph, $f \in \{0,\dots,q\}$ a fresh color, $S$
an independent set, $F$ a matching none of whose edges has an endpoint
in $S$, and $\varphi$ an edge coloring with $q$ colors in which two
distinct edges outside $F$ sharing an endpoint get distinct colors. Let
$g \colon V \to \{0,\dots,q-1\}$ satisfy, for $v, w \notin S$:
$g(v) \ne \varphi(e)$ for every edge $e \notin F$ at $v$, and
$g(v) \ne g(w)$ when $v$ and $w$ are adjacent. Color the vertices of $S$
and the edges of $F$ with $f$, and every other vertex $v$ and edge $e$
with the image of $g(v)$, resp. $\varphi(e)$, under the order-preserving
bijection from $q$ colors onto the $q+1$ colors other than $f$. This is
a valid total coloring with $q+1$ colors.
```

**In Lean.** `TotalColoringAudit.PartialEdgeSelector.partialEdgeSelectorAssignment_valid` in [Audit/PartialEdgeSelector/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/PartialEdgeSelector/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem partialEdgeSelectorAssignment_valid
    {V : Type*} [DecidableEq V] {G : SimpleGraph V} {q : ℕ}
    (fresh : Fin (q + 1)) (phi : G.edgeSet → Fin q)
    (S : Finset V) (F : Finset G.edgeSet) (g : V → Fin q)
    (hphi : ∀ e f : G.edgeSet, e ∉ F → f ∉ F → G.lineGraph.Adj e f → phi e ≠ phi f)
    (hS : G.IsIndepSet (S : Set V))
    (hF : ∀ ⦃e f : G.edgeSet⦄, e ∈ F → f ∈ F → ¬G.lineGraph.Adj e f)
    (havoid : ∀ ⦃v : V⦄, v ∈ S → ∀ ⦃e : G.edgeSet⦄, e ∈ F → v ∉ (e : Sym2 V))
    (hallowed : ∀ v, v ∉ S → ∀ e : G.edgeSet, v ∈ (e : Sym2 V) → e ∉ F → phi e ≠ g v)
    (hproper : ∀ v, v ∉ S → ∀ w, w ∉ S → G.Adj v w → g v ≠ g w) :
    (∀ v w, G.Adj v w →
        (if v ∈ S then fresh else fresh.succAbove (g v)) ≠
          (if w ∈ S then fresh else fresh.succAbove (g w))) ∧
      (∀ e f, G.lineGraph.Adj e f →
        (if e ∈ F then fresh else fresh.succAbove (phi e)) ≠
          (if f ∈ F then fresh else fresh.succAbove (phi f))) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) →
        (if v ∈ S then fresh else fresh.succAbove (g v)) ≠
          (if e ∈ F then fresh else fresh.succAbove (phi e)))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Every input is a hypothesis; no finiteness is assumed.

### Conditional alternating rainbow-path selector: a supplied path certificate gives q + 1 colors

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check that applies to this result passed (the build; its statement was not compared by a second checker).

**In words.**

```latex
Let $G$ be a finite simple graph with a proper edge coloring $\varphi_0$
with $q$ colors, and $K$ a vertex set. Suppose there are distinct
vertices $u_0,\dots,u_k$, exactly the vertices of $K$, with path edges
$e_i = u_i u_{i+1}$ ($0 \le i < k$) whose $\varphi_0$-colors are pairwise
distinct; a color $\sigma \in \{0,\dots,q-1\}$ of the same palette
that no edge receives under $\varphi_0$; edge sets $L$ and $F$ of $G$,
each a matching, such that the path edge $e_i$ lies in $L$ exactly for
even $i$ and in $F$ exactly for odd $i$ ($L$ and $F$ may also contain
edges off the path), with no edge of $F$ at $u_0$; a function
$c \colon V \to \{0,\dots,q-1\}$ with $c(u_{i+1}) = \varphi_0(e_i)$;
and a list without repetition of exactly
the vertices outside $K$ satisfying the core peel inequality of the
selector decoder for $S = \{u_0\}$ and $K$. Then $G$ has a valid total
coloring with $q+1$ colors.
```

**In Lean.** `TotalColoring.exists_valid_assignment_of_alternatingRainbowPathSelector` in [TotalColoring/TotalIndependentSelector.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/TotalColoring/TotalIndependentSelector.lean).

```lean
theorem exists_valid_assignment_of_alternatingRainbowPathSelector
    (phi₀ : EdgeAssignment G (Fin q)) (hphi₀ : phi₀.Valid)
    (K : Finset V) (k : ℕ)
    (cert : AlternatingRainbowPathSelectorCertificate G phi₀ K k) :
    ∃ a : Assignment G (Fin (q + 1)), a.Valid
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Conditional: the proper edge coloring and the whole certificate (path, rainbow, spare color, matchings, core colors, peel order) are hypotheses; the existence of the path is not proved.

### Soundness of the executable extension checker

**Verified.** Lean accepts the proof, and lean-pkg's record shows every check of this result passed (the build, and the statement comparison).

**In words.**

```latex
Let $X$ be an extension datum from a finite graph $G$ to a finite graph
$H$ and $c$ an edge coloring of $H$ with a color type with decidable
equality. If the Boolean checker checkExtension accepts $(X, c)$, then
decoding $c$ through $X$ gives a valid total coloring of $G$. (The
checker accepts exactly when $c$ is proper and gives distinct selector
edges distinct colors; that equivalence is the separate lemma
checkExtension_eq_true_iff, not part of this claim.)
```

**In Lean.** `TotalColoringAudit.Certificate.checkExtension_sound` in [Audit/Certificate/Challenge.lean](https://github.com/chenle02/total-coloring-lean/blob/c025d20a182644bbacdd96165c93e1b8b2a403c6/Audit/Certificate/Challenge.lean): the statement the proof was checked against (the proof is in a separate file, and a second checker confirmed it proves exactly this).

```lean
theorem checkExtension_sound
    {V : Type*} {W : Type*} {C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (classEdge : V → H.edgeSet) (originalEdge : G.edgeSet → H.edgeSet)
    (classEdge_ne_of_adj : ∀ {v w : V}, G.Adj v w → classEdge v ≠ classEdge w)
    (originalEdge_adj : ∀ {e f : G.edgeSet}, G.lineGraph.Adj e f →
      H.lineGraph.Adj (originalEdge e) (originalEdge f))
    (classEdge_adj_original : ∀ {v : V} {e : G.edgeSet}, v ∈ (e : Sym2 V) →
      H.lineGraph.Adj (classEdge v) (originalEdge e))
    (color : H.edgeSet → C)
    [Fintype V] [Fintype W] [DecidableEq W] [DecidableRel H.Adj] [DecidableEq C]
    (h : (decide (∀ e f : H.edgeSet,
            (e ≠ f ∧ ∃ x : W, x ∈ (e : Sym2 W) ∧ x ∈ (f : Sym2 W)) → color e ≠ color f) &&
          decide (∀ v w : V, classEdge v ≠ classEdge w →
            color (classEdge v) ≠ color (classEdge w))) = true) :
    (∀ v w, G.Adj v w → color (classEdge v) ≠ color (classEdge w)) ∧
      (∀ e f, G.lineGraph.Adj e f → color (originalEdge e) ≠ color (originalEdge f)) ∧
      (∀ (v : V) (e : G.edgeSet), v ∈ (e : Sym2 V) →
        color (classEdge v) ≠ color (originalEdge e))
```

**Axioms.** At most `Classical.choice`, `Quot.sound`, `propext` (what the build check records for the whole package).

**Note.** Concerns well-typed Lean values only; parsing external data is outside the theorem.

## What the checks establish

- **Every proof is checked by Lean.** The package builds; no `sorry` (an unfinished proof) remains; the only axioms used are `Classical.choice`, `Quot.sound`, `propext` (allowed: `propext`, `Quot.sound`, `Classical.choice`).
- **The statements shown are the ones proved.** For 8 statement(s), a second checker (comparator) confirmed that the proof proves exactly the statement shown, with only the permitted axioms, and independent Lean kernels replayed the proof.
- **Not checked by any tool:** that a title or note describes its Lean statement. A definition listed under *Definitions checked by a person* is compared by name and type only.

The full account of what each check covers and what it takes on trust is lean-pkg's [trust model](https://github.com/lean-pkg/lean-pkg/blob/main/docs/trust-model.md).

## How this was checked

- lean-pkg's claims ledger: **ready**, every required claim is closed by the recorded receipts; 8 of 8 required claim(s) verified (`sha256:23f4baa46a3fc93d…`).
- Build check (`lean-pkg gate`) at commit `c025d20a1826`: `sorry` count 0; axioms used: `Classical.choice`, `Quot.sound`, `propext`.
- Axioms of every claim: read from the built environment (Lean's `collectAxioms`) for all 13 claim(s) in `claims.yaml`, not only the theorems the build prints; none uses an axiom beyond `propext`, `Quot.sound` and `Classical.choice`.
- Toolchain advisory: the build check ran on Lean `leanprover/lean4:v4.32.0`, which has a known soundness bug fixed in `v4.32.1` ([lean-v4.32.1-kernel-opaque-fvars](https://lean-lang.org/doc/reference/latest/releases/v4.32.1/); lean-pkg's [toolchain advisories](https://github.com/lean-pkg/lean-pkg/blob/main/src/lean_pkg/data/toolchain-advisories.yaml)).
- Toolchain advisory: the build check ran on Lean `leanprover/lean4:v4.32.0`, which has a known soundness bug fixed in `v4.32.2` ([lean-v4.32.2-kernel-nested-inductive](https://lean-lang.org/doc/reference/latest/releases/v4.32.2/); lean-pkg's [toolchain advisories](https://github.com/lean-pkg/lean-pkg/blob/main/src/lean_pkg/data/toolchain-advisories.yaml)).
- Toolchain advisory: the build check ran on Lean `leanprover/lean4:v4.32.0`, which has a known soundness bug fixed in `v4.33.1` ([lean-v4.33.1-kernel-and-runtime](https://lean-lang.org/doc/reference/latest/releases/v4.33.1/); lean-pkg's [toolchain advisories](https://github.com/lean-pkg/lean-pkg/blob/main/src/lean_pkg/data/toolchain-advisories.yaml)).
- Toolchain advisory: the build check ran on Lean `leanprover/lean4:v4.32.0`, which has a known soundness bug fixed in `v4.34.1` ([lean-v4.34.1-runtime-refcounts](https://lean-lang.org/doc/reference/latest/releases/v4.34.1/); lean-pkg's [toolchain advisories](https://github.com/lean-pkg/lean-pkg/blob/main/src/lean_pkg/data/toolchain-advisories.yaml)).
- Statement comparison (comparator) at commit `c025d20a1826`: 8 configuration(s), 8 theorem(s) compared (each Challenge statement against its Solution proof); permitted axioms: `Classical.choice`, `Quot.sound`, `propext`; definitions compared by name only: none.

### Receipts

| Receipt | Check | Commit | Date | Job | SHA-256 |
|---|---|---|---|---|---|
| `.lean-receipts/3f364b51d2c7-comparator.json` | statement comparison | `3f364b51d2c7` | 2026-10-18 | — | `a248b4d7ceeb034d0fb0a3700670e7b59ca7574aa84287f0e2d1589ddd2eeb1e` |
| `.lean-receipts/3f364b51d2c7-systemd-user-total-coloring-lean-verify.service-26f87e9fdae2438cb4ab302aa085cb30-h-2db2e0fa6029.json` | build | `3f364b51d2c7` | 2026-10-18 | — | `732ee12803528338b33d21df1482fdc51fd2ed169b579a61b589e5e9e0e0ba84` |
| `.lean-receipts/533f9430cb45-comparator.json` | statement comparison | `533f9430cb45` | 2026-10-08 | — | `c3c1f5d65707f99f56a870714d12541fb7b7c1abd60f3358d4f25bd0bbf907bd` |
| `.lean-receipts/533f9430cb45-home-workstation-2026-10-08-total-coloring.json` | build | `533f9430cb45` | 2026-10-08 | — | `4ea44f7efdc1ba712e79bf2e9d5f6f2f0e41a350f4c5920197f43e91a16dc966` |
| `.lean-receipts/55edc8145228-home-workstation-2026-10-06-total-coloring.json` | build | `55edc8145228` | 2026-10-06 | — | `14d42549e43e9fc24cd17655f207a60a901ed0c4e31ec83c379fe871cbb3b66d` |
| `.lean-receipts/c025d20a1826-comparator.json` (used here) | statement comparison | `c025d20a1826` | 2026-10-18 | — | `120f4a7878339120dbb684b778daa944e2c7241d48d0fee3c99b0fde2f28f09b` |
| `.lean-receipts/c025d20a1826-systemd-user-total-coloring-lean-verify.service-eff861bf68744993b3eaff1c5e6b37fc-h-2db2e0fa6029.json` (used here) | build | `c025d20a1826` | 2026-10-18 | — | `586b45670d5cfb97a03fa573d036b1c7b2f1bb03d0dd09d5d24488fa1df1d4cd` |

*(used here)*: the receipt the lean-pkg registry holds for this package, which the lines above read. SHA-256 is of the file as committed.

### Reproduce

- Lean toolchain: `leanprover/lean4:v4.32.0`.
- Mathlib: `81a5d257c8e410db227a6665ed08f64fea08e997` (lake-manifest.json).

```bash
git clone https://github.com/chenle02/total-coloring-lean
cd total-coloring-lean
git checkout c025d20a182644bbacdd96165c93e1b8b2a403c6   # the commit the build check binds
lake exe cache get
lake build
```

Expected: `#print axioms` on any declaration above reports a subset of {`Classical.choice`, `Quot.sound`, `propext`} (the union the build check records); `sorryAx` never appears.

## Citation

Le Chen and Songling Shan. *Total Coloring Lean*. Version 0.2.0. [doi:10.5281/zenodo.23452513](https://doi.org/10.5281/zenodo.23452513).

See [CITATION.cff](CITATION.cff).

## License

Released under `Apache-2.0`; see [LICENSE](LICENSE).

## Acknowledgments

Developed and verified with [lean-pkg](https://github.com/lean-pkg/lean-pkg) ([doi:10.5281/zenodo.23272098](https://doi.org/10.5281/zenodo.23272098)).

<!-- lean-pkg:page:end -->
