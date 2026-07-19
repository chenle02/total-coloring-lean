<div align="center">
  <img src="docs/assets/logo.svg" width="150" alt="Total Coloring Lean graph logo">
  <h1>Total Coloring Lean</h1>
  <p><strong>Kernel-checked Lean 4 foundations for total coloring and auxiliary rainbow edge coloring.</strong></p>

  <p>
    <a href="https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml"><img alt="Lean CI status" src="https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml/badge.svg"></a>
    <a href="https://chenle02.github.io/total-coloring-lean/"><img alt="Project documentation" src="https://img.shields.io/badge/docs-GitHub%20Pages-4051b5?logo=materialformkdocs&logoColor=white"></a>
    <a href="https://github.com/chenle02/total-coloring-lean/releases"><img alt="Latest release" src="https://img.shields.io/github/v/release/chenle02/total-coloring-lean?display_name=tag"></a>
    <a href="lean-toolchain"><img alt="Lean version 4.32.0" src="https://img.shields.io/badge/Lean-4.32.0-0f766e"></a>
    <a href="LICENSE"><img alt="MIT license" src="https://img.shields.io/badge/license-MIT-4338ca"></a>
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
> theorem `TotalColoring.exists_valid_assignment_of_highDegree`. The
> proof branch `agent/independent-seed-endpoint`, at exact source commit
> `cc4dd7ae1d858ea0583549f88707952e2414bf60` and tree
> `9af6a84e1305aed9a0156dcd59c279de792dea4a`, additionally contains the
> conditional endpoint
> `TotalColoring.exists_valid_assignment_of_independentSeedPeel` and its
> maximum-degree wrapper
> `TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel`.
> These two declarations are not yet on the default branch. The high-degree
> theorem produces a valid total assignment with
> `G.maxDegree + 3` colors from
> `Fintype.card V ≤ 2 * G.maxDegree`. The endpoint produces an assignment in
> `Fin (q + 1)` only from a supplied proper `Fin q` edge coloring, a supplied
> independent seed, and a supplied peel certificate, with `0 < q`. Setting
> `q = G.maxDegree + 1` therefore gives a conditional `Delta + 2` palette, but
> the library does not prove Vizing's theorem or existence of the required
> seed/certificate. It does not prove the unrestricted Total Coloring
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

### Proof-branch conditional independent-seed endpoint

At proof-branch source commit
[`cc4dd7ae`](https://github.com/chenle02/total-coloring-lean/commit/cc4dd7ae1d858ea0583549f88707952e2414bf60),
exact tree `9af6a84e1305aed9a0156dcd59c279de792dea4a`, the separate declaration
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

These declarations and the final two `#check` lines below require the named
proof branch; `main` does not contain them before merge.

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
```

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

Neither the current default branch nor the independent-seed proof branch
establishes:

- the Total Coloring Conjecture;
- an unconditional high-degree or all-graphs `Delta + 2` total-coloring
  conclusion;
- an unconditional total-coloring conclusion from graph hypotheses alone for
  graphs outside the explicit high-degree regime
  `Fintype.card V ≤ 2 * G.maxDegree`;
- Vizing's theorem or existence of the proper edge-coloring witness required
  by the conditional independent-seed endpoint;
- existence of an independent seed and peel certificate for every graph;
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

[GitHub Sponsors](https://github.com/sponsors/chenle02) supports formalization
maintenance, documentation, CI and cluster verification, and reproducible
releases. Sponsorship does not affect theorem claims or proof-review standards.

## License

Copyright © 2026 Le Chen and contributors. Distributed under the [MIT
License](LICENSE).
