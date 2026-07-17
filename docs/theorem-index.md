# Curated theorem index

This is a small map of public entrypoints, not an exhaustive inventory of every
internal lemma.

## Core predicates

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.InAuxiliaryClass` | `AuxiliaryClass` | Pair-level structural predicate for the matching-plus-star class |
| `TotalColoring.ExtensionPalette` | `CriticalState` | The auxiliary palette `Fin (D + 2)` |
| `TotalColoring.HasValidRainbowColoring` | `CriticalState` | Existence of a proper auxiliary edge coloring rainbow on `J` |
| `TotalColoring.Auxiliary.Extension` | `Auxiliary` | Conflict-preserving data for decoding auxiliary edge colors to a total assignment |

## Supplied pair/singleton constructor seam

| Declaration | Module | Purpose |
| --- | --- | --- |
| `TotalColoring.Auxiliary.PairSingletonWitness` | `PairSingletonExtension` | A supplied fixed partition relation into independent singleton and pair classes; the finite constructor uses a finite vertex type with decidable equality |
| `TotalColoring.Auxiliary.PairSingletonWitness.auxiliaryGraph` | `PairSingletonExtension` | The ordinary auxiliary graph on `Option V` |
| `TotalColoring.Auxiliary.PairSingletonWitness.extension` | `PairSingletonExtension` | The conflict-preserving extension from the original graph into that auxiliary graph |
| `TotalColoring.Auxiliary.PairSingletonWitness.classEdge_mem_distinguishedEdgeSet` | `PairSingletonExtension` | Every decoder selector belongs to the constructed distinguished edge set |

## Terminal proof entrypoints

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.IsOutsideEdgeMinimalNoncolorable.false_of_critical_allD` | `CriticalAllDClosure` | A finite outside-edge-minimal noncolorable auxiliary member is impossible |
| `TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass` | `CriticalAllDClosure` | Every finite `InAuxiliaryClass D H J` has `HasValidRainbowColoring D H J` |
| `TotalColoring.Auxiliary.Extension.decode_valid` | `Auxiliary` | A proper selector-rainbow auxiliary assignment decodes to a valid total assignment |
| `TotalColoring.Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` | `AuxiliaryTransfer` | A supplied compatible extension into a finite auxiliary-class member yields a valid total assignment with palette `Fin (D + 2)` |

The composed transfer theorem remains conditional on a supplied
`Auxiliary.Extension G H`, membership of every selector edge in the
distinguished set, and `InAuxiliaryClass D H J`. A supplied
`PairSingletonWitness` now discharges the first two pieces for its constructed
graph. The library does not yet construct that witness from an equitable
partition, prove `InAuxiliaryClass` for the constructed graph, or relate `D`
to the original graph's maximum degree.

## Executable checker soundness

| Declaration | Accepted Boolean implies |
| --- | --- |
| `TotalColoring.Certificate.checkTotal_sound` | The supplied total assignment is semantically valid |
| `TotalColoring.Certificate.checkEdge_sound` | The supplied edge assignment is proper |
| `TotalColoring.Certificate.checkRainbow_sound` | Distinguished selector edges have pairwise distinct colors |
| `TotalColoring.Certificate.checkExtension_sound` | The accepted auxiliary certificate decodes to a valid total assignment |

The checkers operate on already well-typed Lean values. Parsing arbitrary JSON
or proving an external census complete is outside these soundness theorems.

## Copyable inspection

```lean
import TotalColoring

#check TotalColoring.InAuxiliaryClass
#check TotalColoring.HasValidRainbowColoring
#check TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.PairSingletonWitness
#check TotalColoring.Auxiliary.PairSingletonWitness.auxiliaryGraph
#check TotalColoring.Auxiliary.PairSingletonWitness.extension
#check TotalColoring.Auxiliary.PairSingletonWitness
  .classEdge_mem_distinguishedEdgeSet
#check TotalColoring.Certificate.checkExtension_sound
```

The maintained version of this snippet is
[`docs/examples/Quickstart.lean`](https://github.com/chenle02/total-coloring-lean/blob/main/docs/examples/Quickstart.lean)
and is compiled by CI.
