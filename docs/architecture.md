# Proof architecture

The formal route is layered so each theorem exposes its hypotheses and trust
boundary. The terminal result is assembled from ordinary Lean propositions;
no external solver result is imported as an axiom.

```text
supplied EquitableIndependentPartition G (Delta(G) + 1) + density
        │
        ▼
PairSingletonWitness + exact J.card = Delta(G) + 1
        │
        ▼
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
| Supplied-witness constructor | `PairSingletonExtension` | Concrete auxiliary graph, conflict-preserving extension, selector inclusion and exact coverage, qualitative matching-plus-full-star structure, exact degree/class-count identities, and conditional high-degree structural-class membership from a supplied singleton/pair witness |
| Supplied-partition adapter | `EquitablePairSingleton` | Equitable independent partition to pair/singleton witness, exact class count, high-degree auxiliary membership, and conditional terminal total assignment |
| Abstract transfer | `AuxiliaryTransfer` | Composition of the all-orders auxiliary theorem with a supplied compatible extension |
| Structural class | `AuxiliaryClass`, `Distinguished` | Definition of `A_D`, deletion closure, and stable distinguished-edge transport |
| Certificates | `Certificate` | Executable checkers connected to semantic propositions by soundness theorems |
| Critical extraction | `CriticalState`, `MinimalExtraction`, `DeletionBridge` | Minimal hypothetical counterexample and one-hole state |
| Recoloring geometry | `RainbowSwap`, `Kempe`, `PartialKempe`, `TwoColorGeometry` | Exact swap safety and physical two-color components |
| Fan mechanics | `Fan*`, `Dependency*`, `CriticalFan*` | Legal shifts, reachability, missing colors, and capacity |
| Global pivots | `CriticalGlobalMaximal`, `CriticalFrozenMobility`, `CriticalRootPivot` | Maximal reachable state and elimination of frozen triples |
| Terminal closure | `CriticalDirectEntry`, `CriticalDominator*`, `CriticalCrossing*`, `CriticalAllDClosure` | External-source cases and final contradiction |

The umbrella [`TotalColoring.lean`](https://github.com/chenle02/total-coloring-lean/blob/a441fbfa1e404dc7610e0c32c80dd692cd938c20/TotalColoring.lean)
directly imports every production module.

## The remaining partition-existence and empty-graph seams

The abstract auxiliary theorem and its conditional composition with
`Auxiliary.Extension.decode_valid` are complete. From a supplied
`PairSingletonWitness` on a finite vertex type with decidable equality,
`PairSingletonExtension` now constructs the concrete auxiliary graph, packages
its conflict maps as an `Auxiliary.Extension`, proves selector membership and
exact coverage, constructs the off-center matching part, proves that its
endpoints avoid the center and center neighbors, and identifies the remaining
distinguished edges with the full center incidence star. It now also proves
the exact copied-vertex degree formula and center/class-count identity. The
theorem `isAuxiliaryClassMember_of_class_count_and_bounds` derives the
maximum-degree and center-degree fields from exact distinguished cardinality,
an original-graph degree bound, and an order bound. Its high-degree
specialization assumes

```text
P.distinguished.card = G.maxDegree + 1
Fintype.card V ≤ 2 * G.maxDegree
```

and produces `IsAuxiliaryClassMember (G.maxDegree + 1)` for the constructed
auxiliary graph.

The qualitative structural layer is commit `7aa102b…`, exact tree
`4b6440a0df108f47f5c120e7e0187c058a462138`. The numerical layer was verified
from private source commit `acb08de…`, exact tree
`7207e2a282ff829fba9737e93154f46f385ef879`; the same numerical Lean content is
integrated at public PR commit `343b7b8…`, tree
`9863f500b2671048f4dc386f497eb6523b065099`. The repository trees differ
because the public commit integrates the numerical file onto the PR branch.
Full/checker job `5387929` and independent trust-v3 job `5387978` passed with
exit `0:0`; public Lean CI run `29612994477` and docs run `29612994502` also
passed at `343b7b8…`. PR #8 remains draft and these layers are not on `main`
unless it has since merged.

`EquitablePairSingleton` now closes the first of those tracks. From
`Q : EquitableIndependentPartition G D` and `D <= |V| < 2D`, it proves every
class has size one or two, constructs `Q.toPairSingletonWitness`, and proves
`Q.distinguished_card`. In the nonempty high-degree specialization,
`Q.highDegreeWitness_inAuxiliaryClass` supplies the complete pair-level
auxiliary hypothesis and `Q.exists_valid_assignment_of_highDegreePartition`
returns a valid total assignment with palette
`ExtensionPalette (G.maxDegree + 1)`.

That adapter is commit `a441fbf`, exact code tree
`0e9b04a2acabae0cb0612e5e3cbf0344cc2f94f7`. Exact-tree leaf job `5387980`,
Nova full build job `5387981`, and high-memory full/Quickstart/leanchecker
trust job `5387982` all passed with exit `0:0`. PR #8 remains draft.

The remaining proof track must construct the supplied equitable independent
partition with `D = G.maxDegree + 1` for each nonempty graph in the intended
high-degree regime. A complement-matching argument is a prospective route,
not a checked result. The empty graph is a separate base case. These remaining
seams prevent promotion of the conditional partition theorem to the
end-to-end manuscript theorem.
