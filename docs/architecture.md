# Proof architecture

The formal route is layered so each theorem exposes its hypotheses and trust
boundary. The terminal result is assembled from ordinary Lean propositions;
no external solver result is imported as an axiom.

```text
Auxiliary class A_D
        │
        ▼
finite minimal noncolorable extraction
        │
        ▼
valid rainbow one-hole critical state
        │
        ▼
fans, reachability, missing-color capacity
        │
        ▼
global maximal state and root pivots
        │
        ▼
direct entry, dominators, robust columns
        │
        ▼
k = 1 / 2 / 3 exhaustion
        │
        ▼
crossing and detachment contradiction
        │
        ▼
HasValidRainbowColoring D H J
        │
        │ supplied Extension + selector inclusion
        ▼
exists Assignment G (Fin (D + 2)) with Assignment.Valid
```

## Layer map

| Layer | Principal modules | Role |
| --- | --- | --- |
| Semantics | `Graph`, `Total`, `Auxiliary` | Graph incidence, coloring assignments, and conditional decoding |
| Supplied-witness constructor | `PairSingletonExtension` | Concrete auxiliary graph, conflict-preserving extension, selector inclusion and exact coverage, qualitative matching-plus-full-star structure, and conditional structural-class membership from a supplied singleton/pair witness |
| Abstract transfer | `AuxiliaryTransfer` | Composition of the all-orders auxiliary theorem with a supplied compatible extension |
| Structural class | `AuxiliaryClass`, `Distinguished` | Definition of `A_D`, deletion closure, and stable distinguished-edge transport |
| Certificates | `Certificate` | Executable checkers connected to semantic propositions by soundness theorems |
| Critical extraction | `CriticalState`, `MinimalExtraction`, `DeletionBridge` | Minimal hypothetical counterexample and one-hole state |
| Recoloring geometry | `RainbowSwap`, `Kempe`, `PartialKempe`, `TwoColorGeometry` | Exact swap safety and physical two-color components |
| Fan mechanics | `Fan*`, `Dependency*`, `CriticalFan*` | Legal shifts, reachability, missing colors, and capacity |
| Global pivots | `CriticalGlobalMaximal`, `CriticalFrozenMobility`, `CriticalRootPivot` | Maximal reachable state and elimination of frozen triples |
| Terminal closure | `CriticalDirectEntry`, `CriticalDominator*`, `CriticalCrossing*`, `CriticalAllDClosure` | External-source cases and final contradiction |

The umbrella [`TotalColoring.lean`](https://github.com/chenle02/total-coloring-lean/blob/7aa102b0211c36c6d69f03bc051a5c2706f62c9d/TotalColoring.lean)
directly imports every production module.

## The remaining constructor and numerical seam

The abstract auxiliary theorem and its conditional composition with
`Auxiliary.Extension.decode_valid` are complete. From a supplied
`PairSingletonWitness` on a finite vertex type with decidable equality,
`PairSingletonExtension` now constructs the concrete auxiliary graph, packages
its conflict maps as an `Auxiliary.Extension`, proves selector membership and
exact coverage, constructs the off-center matching part, proves that its
endpoints avoid the center and center neighbors, and identifies the remaining
distinguished edges with the full center incidence star. The theorem
`isAuxiliaryClassMember_of_numeric` packages these facts as an
`IsAuxiliaryClassMember` once exact distinguished cardinality, the
maximum-degree bound, and the center-degree range are supplied.

This structural layer is commit `7aa102b…` on draft PR #8, with exact source
tree `4b6440a0df108f47f5c120e7e0187c058a462138`; it is not on `main` unless
that PR has since merged.

The remaining track must construct that witness from an equitable partition,
prove those three numerical obligations, and relate `D` to the original
graph's maximum degree.

Those remaining seams are intentionally visible: the checked supplied-witness
layer cannot be silently promoted to the manuscript theorem.
