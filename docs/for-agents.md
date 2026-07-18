# Guide for coding agents

This page gives coding assistants a small, safe context window for the project.

## Read order

1. Inspect the exact terminal declaration in
   `TotalColoring/HighDegreeTotalColoring.lean`.
2. Read [`claim-boundary.json`](claim-boundary.json) and check that its pinned
   tree matches the code tree you are discussing.
3. For the terminal route, inspect `MatchingLowerBound.lean`,
   `HighDegreeComplementMatching.lean`, `MatchingExact.lean`,
   `ComplementMatchingWitness.lean`, `PairSingletonExtension.lean`,
   `AuxiliaryTransfer.lean`, and `EmptyAssignment.lean` as needed.
4. Use the [curated theorem index](theorem-index.md) to find public entrypoints.
5. Read `AGENTS.md` before proposing or making repository changes.
6. Read only the additional source modules needed for the current theorem or
   definition.

## Authority order

1. Lean declarations at the exact pinned tree determine what is proved.
2. `AGENTS.md` determines repository and trust policy.
3. `docs/claim-boundary.json` is the machine-readable public mirror.
4. The README and Pages explain the result but cannot broaden it.

If code and prose disagree, narrow the prose. If two trees differ, a receipt
for one does not automatically verify the other.

## Mandatory claim guardrails

- The package terminal declaration is
  `TotalColoring.exists_valid_assignment_of_highDegree`.
- Its graph-theoretic hypothesis is exactly
  `Fintype.card V <= 2 * G.maxDegree`, in addition to the displayed finite and
  decidability instances in its type.
- Its conclusion is a valid assignment in
  `ExtensionPalette (G.maxDegree + 1)`, definitionally
  `Fin (G.maxDegree + 3)`.
- The theorem covers both empty and nonempty finite vertex types. It has no
  parity hypothesis.
- The result is a propositional existence theorem, not an executable coloring
  extractor for external graph data.
- For the nonempty branch, keep the actual route straight: complement-degree
  bound, general matching lower bound, exact-size trimming,
  `PairSingletonWitness`, auxiliary-class membership, rainbow auxiliary
  coloring, and semantic decoding.
- The empty branch uses `exists_valid_assignment_of_isEmpty`; it is not an
  unproved side condition.
- Never call this the Total Coloring Conjecture, a `G.maxDegree + 2` result, a
  locked or fully proved manuscript theorem, or a novelty result.
- Do not extend the theorem to graphs outside its density hypothesis.
- Keep package proof status and publication trust separate. The exact
  proof-development tree `4624044788ab42c0dc116cfbf7f38c696065263c`
  passed five separate high-memory full/Quickstart/`leanchecker` jobs
  (`5388311` through `5388315`). A later integrated Git tree needs its own
  exact-tree gate and public CI before receiving the same trust statement.
- Do not say release `v0.1.0` contains the terminal theorem; cite a later exact
  commit or release that actually contains it.

## Retained conditional interfaces

Do not erase or misdescribe the more general supplied-input theorems:

- `MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass` applies to
  every finite formal `InAuxiliaryClass D H J` and uses an auxiliary edge
  palette `Fin (D + 2)`.
- `Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` keeps its
  supplied extension, selector-membership proof, and auxiliary-class
  membership explicit.
- A supplied `PairSingletonWitness` exposes its concrete graph, extension,
  selector coverage, structural class, and numerical lemmas.
- `EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition`
  remains a valid route from an explicit supplied partition on a nonempty
  graph together with `Fintype.card V <= 2 * G.maxDegree`.

The supplied equitable partition is no longer a premise of the package
terminal theorem. `HighDegreeTotalColoring` constructs the needed witness from
an exact complement matching. Say which API you are using instead of carrying
limitations from one interface over to another.

## Repository map

| Need | Start here |
| --- | --- |
| Package terminal theorem | `TotalColoring/HighDegreeTotalColoring.lean` |
| Empty-vertex base case | `TotalColoring/EmptyAssignment.lean` |
| General matching lower bound | `TotalColoring/MatchingLowerBound.lean` |
| High-degree complement specialization | `TotalColoring/HighDegreeComplementMatching.lean` |
| Exact matching extraction | `TotalColoring/MatchingExact.lean` |
| Complement matching to witness | `TotalColoring/ComplementMatchingWitness.lean` |
| Supplied pair/singleton interface | `TotalColoring/PairSingletonExtension.lean` |
| Supplied equitable-partition interface | `TotalColoring/EquitablePairSingleton.lean` |
| All-orders auxiliary theorem | `TotalColoring/CriticalAllDClosure.lean` |
| Conditional auxiliary-to-total transfer | `TotalColoring/AuxiliaryTransfer.lean` |
| Auxiliary predicate | `TotalColoring/AuxiliaryClass.lean` |
| Semantic coloring definitions | `TotalColoring/Total.lean` |
| Conditional decoding | `TotalColoring/Auxiliary.lean` |
| Executable checkers | `TotalColoring/Certificate.lean` |
| Complete import surface | `TotalColoring.lean` |
| Modification rules | `AGENTS.md`, then `CONTRIBUTING.md` |

## Useful prompts

### Explain the package theorem safely

> Explain the exact hypotheses and conclusion of
> `TotalColoring.exists_valid_assignment_of_highDegree`. Trace the nonempty
> complement-matching route and the empty base case. State the exact palette,
> and separate the Lean package theorem from manuscript and novelty claims.

### Write downstream Lean from graph hypotheses

> Write Lean code applying
> `TotalColoring.exists_valid_assignment_of_highDegree` to a finite graph.
> Keep the density hypothesis explicit and do not add parity, nonempty, or
> supplied-partition assumptions that are absent from the theorem's type.

### Write downstream Lean from supplied structure

> Apply `Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` while
> keeping the supplied extension, selector-membership proof, and
> `InAuxiliaryClass D H J` explicit. Alternatively, use
> `EquitableIndependentPartition.exists_valid_assignment_of_highDegreePartition`
> only when an explicit partition and the required high-degree density
> inequality have already been supplied.

### Audit prose

> Classify every mathematical sentence as kernel-checked at the exact tree,
> conditional on an explicit hypothesis, external mathematics, bounded
> computation, manuscript-only, or unsupported. Cite the exact Lean
> declaration where one exists.

### Find a checker

> Locate the Boolean checker corresponding to this semantic predicate and the
> theorem proving its soundness. State what parsing or completeness claims
> remain outside the checker.

## Modification workflow

Before editing, inspect the branch and dirty tree. Keep changes small, use no
proof placeholders, update documentation mirrors when the public theorem
boundary changes, and run the complete gate from `AGENTS.md`. Heavy
full-library verification may be delegated to CI or an appropriate build node,
but it may not be skipped before publication.
