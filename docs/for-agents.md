# Guide for coding agents

This page gives coding assistants a small, safe context window for the project.

## Read order

1. Inspect the exact terminal declaration in
   `TotalColoring/HighDegreeTotalColoring.lean`.
   For the separate supplied-witness endpoint, inspect
   `TotalColoring/IndependentSeed.lean` at proof-branch source commit
   `cc4dd7ae1d858ea0583549f88707952e2414bf60` instead.
   For the total-independent selector and alternating-path wrappers, inspect
   `TotalColoring/TotalIndependentSelector.lean` at source commit
   `d008514c7a1cf834007bf0bd8de0d10a93926711`.
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
   The default-branch authority and each proof-branch authority are distinct
   until merge.
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
- Never call the package terminal theorem the Total Coloring Conjecture, a
  `G.maxDegree + 2` result, a locked or fully proved manuscript theorem, or a
  novelty result.
- Do not extend the theorem to graphs outside its density hypothesis.
- The independent-seed declarations currently exist only on
  `agent/independent-seed-endpoint` at commit
  `cc4dd7ae1d858ea0583549f88707952e2414bf60`, tree
  `9af6a84e1305aed9a0156dcd59c279de792dea4a`; `main` does not yet contain
  them.
- The separate generic endpoint
  `TotalColoring.exists_valid_assignment_of_independentSeedPeel` requires
  exactly `0 < q`, a supplied proper `phi : EdgeAssignment G (Fin q)`, a
  supplied independent seed `A`, and a supplied
  `IndependentSeedPeelCertificate G A q`; it concludes a valid assignment in
  `Fin (q + 1)`.
- The direct wrapper
  `TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel`
  takes the corresponding explicit witnesses at `q = G.maxDegree + 1` and
  concludes a valid assignment in `Fin (G.maxDegree + 2)`.
- Neither independent-seed declaration proves Vizing's theorem, constructs
  the proper edge assignment, or proves existence of the independent seed or
  peel certificate. Never present either as an unrestricted Total Coloring
  Conjecture theorem or as a strengthening of the terminal high-degree
  theorem's unconditional scope.
- Exact source tree `9af6a84e…` passed sealed offline Easley trust jobs
  `5389587` and `5389588`, including strict leaf, umbrella/full, Quickstart,
  axiom, `leanchecker`, metadata, and reconstruction gates. This verifies the
  conditional decoder; it does not verify existence of its inputs.
- The newer selector declarations exist only on
  `agent/total-independent-selector-decoder` at source commit
  `d008514c7a1cf834007bf0bd8de0d10a93926711`, exact tree
  `1847934c78da03fe80bb67236868700c79016129`; `main` does not contain them.
- `exists_valid_assignment_of_totalIndependentSelectorPeel` requires a
  supplied proper `Fin q` edge coloring, independent fresh-color vertex set,
  matching fresh-color edge set avoiding those vertices, actual-list core
  coloring, and core-relative peel certificate. Its maximum-degree wrapper
  only substitutes `q = G.maxDegree + 1`.
- `AlternatingRainbowPathSelectorCertificate` makes the proposed donor
  exchange explicit: indexed path/endpoints, rainbow colors, unused old spare,
  alternating matching families, start avoidance, core colors, and peel data.
  The corresponding wrapper checks the exchange but does not prove existence
  of the path or certificate.
- Neither selector wrapper proves Vizing, constructs a canonical core or
  selector, or proves the peel/path existence seam. Never present its
  conditional `Fin (G.maxDegree + 2)` conclusion as the unrestricted Total
  Coloring Conjecture.
- Exact source tree `1847934c…` passed sealed Easley job `5391803` with exit
  `0:0` through strict leaf, target/umbrella/full, Quickstart, axiom,
  `leanchecker`, JSON/diff, and exact-tree gates. The receipt verifies the
  implications only.
- Keep package proof status and publication trust separate. The exact
  proof-development tree `4624044788ab42c0dc116cfbf7f38c696065263c`
  passed five separate high-memory full/Quickstart/`leanchecker` jobs
  (`5388311` through `5388315`). The later publishable tree
  `89a32c7a78e294a8b1484092ec79afaa3b4ace5a` received its own Wave 11
  exact-tree gate and PR-head plus post-merge public CI before PR #8 merged it
  into `main`.
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
- At proof-branch commit `cc4dd7ae…`,
  `exists_valid_assignment_of_independentSeedPeel` and its maximum-degree
  wrapper remain conditional on the explicitly supplied proper edge coloring,
  independent seed, and peel certificate. They are not default-branch APIs
  before merge.
- At proof-branch source commit `d008514…`, the total-independent selector
  decoder and alternating-path wrapper retain every selector, core, peel, and
  path witness as explicit input. They are not default-branch APIs before
  merge.

The supplied equitable partition is no longer a premise of the package
terminal theorem. `HighDegreeTotalColoring` constructs the needed witness from
an exact complement matching. Say which API you are using instead of carrying
limitations from one interface over to another.

## Repository map

| Need | Start here |
| --- | --- |
| Package terminal theorem | `TotalColoring/HighDegreeTotalColoring.lean` |
| Proof-branch conditional independent-seed endpoint | `TotalColoring/IndependentSeed.lean` at `cc4dd7ae…`, tree `9af6a84e…` |
| Proof-branch total-independent selector decoder | `TotalColoring/TotalIndependentSelector.lean` at `d008514…`, tree `1847934c…` |
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

### Use the conditional `Delta + 2` wrapper safely

> Apply
> `TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel` while
> keeping the proper `EdgeAssignment G (Fin (G.maxDegree + 1))`, its validity,
> the independent seed, and its peel certificate explicit. State that the
> declaration does not prove Vizing or seed existence and is not an
> unrestricted Total Coloring Conjecture theorem. Also state that this wrapper
> is on proof branch `agent/independent-seed-endpoint`, not yet on `main`.

### Use the total-independent selector safely

> Apply
> `TotalColoring.exists_valid_assignment_of_maxDegreeTotalIndependentSelectorPeel`
> only with an explicit proper edge coloring, independent vertex selector,
> matching edge selector avoiding it, actual-list core coloring, and peel
> certificate. If using
> `exists_valid_assignment_of_maxDegreeAlternatingRainbowPathSelector`, list
> the certificate fields and state that Lean checks the donor exchange but
> does not prove path/certificate existence. Cite proof branch
> `agent/total-independent-selector-decoder`, not `main`.

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
