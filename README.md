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
> a **conditional auxiliary-to-total transfer**. It does not prove the Total
> Coloring Conjecture or an end-to-end high-degree total-coloring theorem.

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

Finally, `P.isAuxiliaryClassMember_of_numeric D` supplies the complete
`IsAuxiliaryClassMember` witness once these three numerical facts are given:

```text
P.distinguished.card = D
P.auxiliaryGraph.maxDegree ≤ D
2 ≤ P.auxiliaryGraph.degree none ∧ P.auxiliaryGraph.degree none ≤ D.
```

Lean does not construct `P` from an equitable partition or prove those three
numerical facts.

```lean
import TotalColoring

#check TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.PairSingletonWitness.extension
#check TotalColoring.Auxiliary.PairSingletonWitness
  .classEdge_mem_distinguishedEdgeSet
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
passed. Release `v0.1.0` predates these result layers; cite the exact commit or
a later release that actually contains them.

### Exact boundary

The library does **not** currently formalize:

- the Total Coloring Conjecture;
- either proposed high-degree total-coloring conclusion;
- the equitable-partition input and construction of a
  `PairSingletonWitness` from it;
- the three numerical hypotheses required by
  `PairSingletonWitness.isAuxiliaryClassMember_of_numeric`: exact distinguished
  cardinality, the maximum-degree bound, and the center-degree range;
- any identification of `D` with the maximum degree of the original graph;
- the resulting end-to-end reduction from an arbitrary input graph;
- the stronger auxiliary `D + 1` palette; or
- a novelty claim.

In the all-orders theorem, `Fin (D + 2)` is the auxiliary edge-coloring
palette; in the conditional transfer, the same type colors the supplied
original graph. Because no theorem identifies `D` with `Delta(G) + 1`, this is
not yet a `Delta + 3` total-coloring conclusion. See the
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
