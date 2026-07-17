# Guide for coding agents

This page gives coding assistants a small, safe context window for the project.

## Read order

1. Read [`claim-boundary.json`](claim-boundary.json).
2. Inspect the exact declaration in `TotalColoring/CriticalAllDClosure.lean`.
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
- `Fin (D + 2)` is an auxiliary edge-coloring palette.
- The result is a propositional existence theorem, not an executable extractor.
- Keep the equitable partition, pair/singleton construction, split-star
  transfer, and total-coloring decoder seam explicit.
- Never claim the Total Coloring Conjecture, a high-degree total-coloring
  theorem, the stronger `D + 1` auxiliary palette, or novelty.
- Do not say release `v0.1.0` contains the terminal theorem; use commit
  `310b82c…` or a later release that actually includes it.

## Repository map

| Need | Start here |
| --- | --- |
| Exact terminal theorem | `TotalColoring/CriticalAllDClosure.lean` |
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
> `MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass` while keeping
> `InAuxiliaryClass D H J` as an explicit hypothesis. Do not assume a concrete
> reduction from a total-coloring instance.

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
