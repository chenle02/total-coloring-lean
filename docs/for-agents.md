# Guide for coding agents

This page gives coding assistants a small, safe context window for the project.

## Read order

1. Read [`claim-boundary.json`](claim-boundary.json).
2. Inspect the exact declarations in `TotalColoring/CriticalAllDClosure.lean`
   and `TotalColoring/AuxiliaryTransfer.lean`. For the current concrete seam,
   also inspect `TotalColoring/PairSingletonExtension.lean`.
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
  palette only for the supplied `G`; no relation between `D` and `Delta(G)` is
  proved.
- The two terminal coloring results are propositional existence theorems, not
  executable extractors.
- Keep all transfer hypotheses explicit: the supplied `Auxiliary.Extension`,
  selector membership in `J`, and auxiliary-class membership. On a finite
  vertex type with decidable equality, a supplied `PairSingletonWitness` now
  gives the extension and selector-membership seam, exact selector coverage,
  and the qualitative matching-plus-full-star structure. Its conditional
  `isAuxiliaryClassMember_of_numeric` theorem still requires exact
  distinguished cardinality, the maximum-degree bound, and the center-degree
  range. Construction of the witness and proofs of those numerical facts
  remain open.
- Never claim the Total Coloring Conjecture, a high-degree total-coloring
  theorem, the stronger `D + 1` auxiliary palette, or novelty.
- Do not say release `v0.1.0` contains these results; use commit `310b82c…`
  for the all-orders auxiliary theorem, `9bdcdec…` for the conditional
  transfer, `dc2a318…` for the original supplied-witness seam, `7aa102b…` for
  the qualitative structural layer, or a later release that
  actually includes the declaration.

## Repository map

| Need | Start here |
| --- | --- |
| Exact terminal theorem | `TotalColoring/CriticalAllDClosure.lean` |
| Conditional auxiliary-to-total transfer | `TotalColoring/AuxiliaryTransfer.lean` |
| Supplied pair/singleton extension seam | `TotalColoring/PairSingletonExtension.lean` |
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
> `InAuxiliaryClass D H J` explicit. Do not assume a concrete reduction from a
> total-coloring instance or identify `D` with the input graph's degree.

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
