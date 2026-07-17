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
| Abstract transfer | `AuxiliaryTransfer` | Composition of the all-orders auxiliary theorem with a supplied compatible extension |
| Structural class | `AuxiliaryClass`, `Distinguished` | Definition of `A_D`, deletion closure, and stable distinguished-edge transport |
| Certificates | `Certificate` | Executable checkers connected to semantic propositions by soundness theorems |
| Critical extraction | `CriticalState`, `MinimalExtraction`, `DeletionBridge` | Minimal hypothetical counterexample and one-hole state |
| Recoloring geometry | `RainbowSwap`, `Kempe`, `PartialKempe`, `TwoColorGeometry` | Exact swap safety and physical two-color components |
| Fan mechanics | `Fan*`, `Dependency*`, `CriticalFan*` | Legal shifts, reachability, missing colors, and capacity |
| Global pivots | `CriticalGlobalMaximal`, `CriticalFrozenMobility`, `CriticalRootPivot` | Maximal reachable state and elimination of frozen triples |
| Terminal closure | `CriticalDirectEntry`, `CriticalDominator*`, `CriticalCrossing*`, `CriticalAllDClosure` | External-source cases and final contradiction |

The umbrella [`TotalColoring.lean`](https://github.com/chenle02/total-coloring-lean/blob/9bdcdec1a872ccef42cfd79e791fe39c22a1beeb/TotalColoring.lean)
directly imports every production module.

## The constructor seam remains open

The abstract auxiliary theorem and its conditional composition with
`Auxiliary.Extension.decode_valid` are complete. The next independent formal
track must construct the concrete pair/singleton auxiliary graph, package its
conflict maps as an `Auxiliary.Extension`, prove selector membership and
`InAuxiliaryClass`, and relate `D` to the original graph's maximum degree. An
equitable-partition theorem is a further external input.

That constructor seam is intentionally visible: the conditional transfer
cannot be silently promoted to the manuscript theorem.
