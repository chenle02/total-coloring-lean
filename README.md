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
> This repository proves an all-orders **auxiliary edge-coloring theorem** and
> a **conditional auxiliary-to-total transfer**. From an explicitly supplied
> equitable independent partition it also proves a conditional
> `Delta + 3` total-coloring result. It does not prove the Total Coloring
> Conjecture or an end-to-end high-degree theorem from graph hypotheses alone.

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

What remains is existence of the supplied partition for every target graph,
for example through the prospective complement-matching route, plus a separate
empty-graph base case. The pinned Mathlib has no ready theorem for that
existence step.

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
```

The all-orders theorem was introduced at commit
[`310b82c`](https://github.com/chenle02/total-coloring-lean/commit/310b82c174ab2281581900897d4646875575e89b)
and passed [public Lean CI at that exact
commit](https://github.com/chenle02/total-coloring-lean/actions/runs/29588129760).
The conditional transfer was introduced at
[`9bdcdec`](https://github.com/chenle02/total-coloring-lean/commit/9bdcdec1a872ccef42cfd79e791fe39c22a1beeb).
The supplied-witness extension seam was introduced at
[`dc2a318`](https://github.com/chenle02/total-coloring-lean/commit/dc2a318be1dd1475b90c492ad460c4180a3fbdec)
on draft PR [#8](https://github.com/chenle02/total-coloring-lean/pull/8); it is
not on `main` unless that PR has since been merged. The qualitative structural
layer is commit `7aa102b…`, exact Git tree
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
infrastructure failures, not verification receipts or proof failures. PR #8
remains draft. The supplied-partition adapter is commit `a441fbf…`, exact code
tree `0e9b04a2acabae0cb0612e5e3cbf0344cc2f94f7`; its source-archive SHA-256 is
`736db25ca7d25fb0eed8431e435e80bc94287e1ae88f9dea806ddba2c1b544f4`.
Leaf job `5387980`, Nova full build job `5387981`, and high-memory
full/Quickstart/leanchecker trust job `5387982` all completed with exit `0:0`.
The outgoing-cache SHA-256 is
`94456901604a3b6ecde49368a4ba285fda03ecdca856b0c37f207624527e037a`.
Release `v0.1.0` predates these result layers; cite the exact commit or a later
release that actually contains them.

### Exact boundary

The library does **not** currently formalize:

- the Total Coloring Conjecture;
- the stronger proposed high-degree `Delta + 2` total-coloring conclusion;
- an end-to-end high-degree `Delta + 3` conclusion from graph hypotheses alone;
- existence, for every nonempty graph in the intended high-degree regime, of
  the required equitable independent partition with
  `D = G.maxDegree + 1`;
- the prospective complement-matching construction that would supply that
  partition;
- the separate empty-graph base case;
- the resulting end-to-end reduction from an arbitrary input graph;
- the stronger auxiliary `D + 1` palette; or
- a novelty claim.

In the all-orders theorem, `Fin (D + 2)` is the auxiliary edge-coloring
palette; in the generic conditional transfer, the same type colors the
supplied original graph while `D` remains abstract. The separate high-degree
partition theorem does use `D = Delta(G) + 1` and checks a conditional
`Delta + 3` total-coloring conclusion from an explicitly supplied equitable
independent partition. Lean does not yet prove that this partition exists for
every nonempty target graph, and the empty graph remains separate. This is
therefore not yet an end-to-end `Delta + 3` theorem. See the
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
