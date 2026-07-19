# Proof architecture

The formal route is layered so each theorem exposes its hypotheses and trust
boundary. The terminal result is assembled from ordinary Lean propositions;
no external solver result is imported as an axiom.

```text
finite graph G + |V| <= 2 * G.maxDegree
        │
        ├── V empty ───────────────────────────────┐
        │                                           │
        └── V nonempty                              │
              │                                     │
              ▼                                     │
    complement minimum-degree and order bounds      │
              │                                     │
              ▼                                     │
    matching in G-complement with at least k edges  │
              │                                     │
              ▼                                     │
    exact trim to k = |V| - (G.maxDegree + 1)       │
              │                                     │
              ▼                                     │
    PairSingletonWitness with                       │
    J.card = G.maxDegree + 1                        │
              │                                     │
              ▼                                     │
    ordinary auxiliary graph in A_D                 │
              │                                     │
              ▼                                     │
    finite minimal noncolorable extraction          │
              │                                     │
              ▼                                     │
    fans, maximal states, dominators, crossing      │
              │                                     │
              ▼                                     │
    HasValidRainbowColoring D H J                   │
              │                                     │
              ▼                                     │
    conflict-preserving semantic decoder            │
              │                                     │
              └──────────────┬──────────────────────┘
                             ▼
    exists Assignment G (ExtensionPalette
      (G.maxDegree + 1)) with Assignment.Valid
```

Here `D = G.maxDegree + 1` and
`ExtensionPalette D = Fin (D + 2)`. The empty branch uses
`exists_valid_assignment_of_isEmpty`; the nonempty branch is the full route
shown on the left. No parity hypothesis occurs.

## Layer map

| Layer | Principal modules | Role |
| --- | --- | --- |
| Semantics | `Graph`, `Total`, `Auxiliary` | Graph incidence, assignments, validity, and conflict-preserving decoding |
| Matching engine | `MatchingLowerBound` | Maximum-matching argument giving at least `k` edges from minimum-degree and order bounds |
| High-degree specialization | `HighDegreeComplementMatching` | Converts the density hypothesis into the complement matching lower bound |
| Exact extraction | `MatchingExact` | Trims a matching subgraph to a prescribed exact edge count |
| Complement adapter | `ComplementMatchingWitness` | Converts a complement matching into a pair/singleton witness and proves its counts |
| Supplied-witness constructor | `PairSingletonExtension` | Auxiliary graph, extension, selector coverage, matching-plus-full-star structure, and degree/count identities |
| Supplied-partition adapter | `EquitablePairSingleton` | Retained alternate API from an explicit equitable independent partition |
| Structural class | `AuxiliaryClass`, `Distinguished` | Definition of `A_D`, deletion closure, and stable distinguished-edge transport |
| Certificates | `Certificate` | Executable checkers connected to semantic propositions by soundness theorems |
| Conditional selector decoding | `IndependentSeed`, `TotalIndependentSelector` | Reverse greedy extension from supplied seed/core peel data; fresh-color vertex/edge selector and explicit alternating-path donor wrappers on proof branches |
| Critical extraction | `CriticalState`, `MinimalExtraction`, `DeletionBridge` | Minimal hypothetical counterexample and one-hole state |
| Recoloring geometry | `RainbowSwap`, `Kempe`, `PartialKempe`, `TwoColorGeometry` | Exact swap safety and physical two-color components |
| Fan mechanics | `Fan*`, `Dependency*`, `CriticalFan*` | Legal shifts, reachability, missing colors, and capacity |
| Global pivots | `CriticalGlobalMaximal`, `CriticalFrozenMobility`, `CriticalRootPivot` | Maximal reachable state and elimination of frozen triples |
| Auxiliary closure | `CriticalDirectEntry`, `CriticalDominator*`, `CriticalCrossing*`, `CriticalAllDClosure` | External-source cases and the all-orders contradiction |
| Terminal composition | `EmptyAssignment`, `AuxiliaryTransfer`, `HighDegreeTotalColoring` | Empty base case, nonempty decoding, and the final package theorem |

The umbrella `TotalColoring.lean` imports every production module, including
the matching, empty, high-degree terminal, and proof-branch selector layers at
the exact branch tree where those modules are present.

## Two routes into the reusable auxiliary engine

The terminal high-degree theorem constructs its input through a matching in
the complement. The supplied-partition route remains available independently:

```text
supplied EquitableIndependentPartition G D
        │  D <= |V| < 2D
        ▼
PairSingletonWitness + J.card = D
        │  G.maxDegree + 1 <= D
        │  |V| + 2 <= 2D
        ▼
InAuxiliaryClass D H J
```

Likewise, a downstream development may start from a supplied
`PairSingletonWitness`, or directly from a compatible `Auxiliary.Extension`
and `InAuxiliaryClass`. These are stable interfaces, not unresolved premises
of `TotalColoring.exists_valid_assignment_of_highDegree`.

The conditional `Delta + 2` proof branches form a separate route. The
independent-seed endpoint starts from a supplied proper old-palette edge
coloring, independent seed, and peel certificate. The later
`TotalIndependentSelector` module permits both an independent fresh-color
vertex set and an avoiding matching of fresh-color edges, together with a
supplied actual-list core coloring and core-relative peel certificate. Its
alternating rainbow-path wrapper proves the donor exchange only after the full
indexed path certificate is supplied. These modules do not feed the terminal
high-degree theorem and do not discharge Vizing, selector/core, peel, or path
existence.

## The matching route in detail

For a nonempty finite graph, put

```text
k = |V| - (G.maxDegree + 1).
```

The complement-degree formula proves every complement degree is at least
`k`, while `|V| <= 2 * G.maxDegree` proves `2 * k <= |V|`. The general
maximum-matching lemma supplies at least `k` complement edges. `MatchingExact`
deletes excess matching edges, preserving the matching predicate, to obtain
exactly `k`.

The exact size is what closes the numerical reduction. Paired vertices
contribute the matching edges; all uncovered vertices become singletons. The
checked support and edge-count identities then give exactly
`G.maxDegree + 1` classes. `PairSingletonExtension` converts those classes to
the ordinary auxiliary graph and proves all fields of
`InAuxiliaryClass (G.maxDegree + 1)` required by the all-orders theorem.

## Terminal boundary

The terminal declaration is:

```lean
TotalColoring.exists_valid_assignment_of_highDegree
```

It closes the former complement-matching, exact-count, partition-construction,
and empty-graph seams inside the Lean package. The exact proof-development tree
`4624044788ab42c0dc116cfbf7f38c696065263c` passed five separate high-memory
full/Quickstart/`leanchecker` replays (jobs `5388311` through `5388315`).

That receipt applies to the named proof tree. It must not be silently promoted
to a later integration or publication tree. Accordingly, the later publishable
tree `89a32c7a78e294a8b1484092ec79afaa3b4ace5a` received a separate Wave 11
exact-tree gate and public CI before PR #8 merged it into `main` as
`0e938606`. The package theorem still does not lock a manuscript theorem,
establish novelty, prove an unconditional stronger palette, or settle the
Total Coloring Conjecture.
