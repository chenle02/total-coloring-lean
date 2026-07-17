# Guide for coding agents

This page gives coding assistants a small, safe context window for the project.

## Read order

1. Read [`claim-boundary.json`](claim-boundary.json).
2. Inspect the exact declarations in `TotalColoring/CriticalAllDClosure.lean`
   and `TotalColoring/AuxiliaryTransfer.lean`. For the current concrete seam,
   also inspect `TotalColoring/PairSingletonExtension.lean` and
   `TotalColoring/EquitablePairSingleton.lean`.
3. Use the [curated theorem index](theorem-index.md) to find public entrypoints.
4. Read `AGENTS.md` before proposing or making repository changes.
5. Read only the source modules needed for the current theorem or definition.

## Authority order

1. Lean declarations at the pinned commit determine what is proved.
2. `AGENTS.md` determines repository and trust policy.
3. `docs/claim-boundary.json` is the machine-readable public mirror.
4. The README and Pages explain the result but cannot broaden it.

## Mandatory claim guardrails

- “All orders” means every finite formal `InAuxiliaryClass D H J`.
- In the all-orders auxiliary theorem, `Fin (D + 2)` is an edge-coloring
  palette.
- In the conditional transfer theorem, `Fin (D + 2)` becomes a total-coloring
  palette only for the supplied `G`; that generic theorem leaves `D` abstract.
  The separate supplied-witness high-degree wrapper conditionally uses
  `D = Delta(G) + 1`.
- The three terminal coloring results are propositional existence theorems, not
  executable extractors.
- Keep all transfer hypotheses explicit: the supplied `Auxiliary.Extension`,
  selector membership in `J`, and auxiliary-class membership. On a finite
  vertex type with decidable equality, a supplied `PairSingletonWitness` now
  gives the extension and selector-membership seam, exact selector coverage,
  the qualitative matching-plus-full-star structure, and exact degree/count
  identities. A supplied witness satisfying
  `P.distinguished.card = G.maxDegree + 1` together with
  `Fintype.card V <= 2 * G.maxDegree` now discharges every
  `IsAuxiliaryClassMember` field at parameter `G.maxDegree + 1`.
  `EquitablePairSingleton` now checks the next adapter: from
  `Q : EquitableIndependentPartition G D` and `D <= |V| < 2D`, it constructs
  the witness and proves `J.card = D`. On a nonempty graph, the supplied
  `G.maxDegree + 1` partition and density hypothesis yield the conditional
  terminal theorem `Q.exists_valid_assignment_of_highDegreePartition`, with
  `G.maxDegree + 3` colors. Keep the remaining inputs explicit: existence of
  `Q` for each target graph and the separate empty-graph base case. The pinned
  Mathlib has no ready existence theorem; complement matching remains an
  unformalized route.
- Never claim the Total Coloring Conjecture, an end-to-end high-degree theorem
  from graph hypotheses alone, the stronger `D + 1` auxiliary palette, or
  novelty. It is correct to state the checked conditional `Delta + 3` theorem
  only with its supplied-partition and nonempty hypotheses.
- Do not say release `v0.1.0` contains these results; use commit `310b82c…`
  for the all-orders auxiliary theorem, `9bdcdec…` for the conditional
  transfer, `dc2a318…` for the original supplied-witness seam, `7aa102b…` for
  the qualitative structural layer, public PR commit `343b7b8…` for the
  numerical layer, and commit `a441fbf…` for the equitable-partition adapter,
  or a later release that actually includes the declaration.
  The private numerical verification source was commit `acb08de…`, exact tree
  `7207e2a…`; its numerical Lean content is identical to the public integration,
  but the repository tree is not.

## Repository map

| Need | Start here |
| --- | --- |
| Exact terminal theorem | `TotalColoring/CriticalAllDClosure.lean` |
| Conditional auxiliary-to-total transfer | `TotalColoring/AuxiliaryTransfer.lean` |
| Supplied pair/singleton extension seam | `TotalColoring/PairSingletonExtension.lean` |
| Supplied equitable-partition adapter | `TotalColoring/EquitablePairSingleton.lean` |
| Auxiliary predicate | `TotalColoring/AuxiliaryClass.lean` |
| Semantic coloring definitions | `TotalColoring/Total.lean` |
| Conditional decoding | `TotalColoring/Auxiliary.lean` |
| Executable checkers | `TotalColoring/Certificate.lean` |
| Complete import surface | `TotalColoring.lean` |
| Modification rules | `AGENTS.md`, then `CONTRIBUTING.md` |

## Useful prompts

### Explain the theorem safely

> Explain the exact hypotheses and conclusion of
> `hasValidRainbowColoring_of_inAuxiliaryClass`. Separate the kernel-checked
> auxiliary result from reductions that are not formalized.

### Write downstream Lean

> Write Lean code that applies
> `Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` while keeping
> the supplied extension, selector-membership proof, and
> `InAuxiliaryClass D H J` explicit. For the concrete partition route, apply
> `EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition`
> only with an explicit supplied `G.maxDegree + 1` partition, nonempty vertex
> type, and density hypothesis. Do not synthesize existence of that partition
> for an arbitrary graph, and keep the empty graph separate.

### Audit prose

> Classify every mathematical sentence as kernel-checked here, conditional on
> an explicit hypothesis, external mathematics, bounded computation, or
> unsupported. Cite the exact Lean declaration where one exists.

### Find a checker

> Locate the Boolean checker corresponding to this semantic predicate and the
> theorem proving its soundness. State what parsing or completeness claims
> remain outside the checker.

## Modification workflow

Before editing, inspect the branch and dirty tree. Keep changes small, use no
proof placeholders, update documentation mirrors when the public theorem
boundary changes, and run the complete gate from `AGENTS.md`. Heavy full-library
verification may be delegated to CI or an appropriate build node, but it may
not be skipped before publication.
