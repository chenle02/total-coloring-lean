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

## Terminal proof entrypoints

| Declaration | Module | Checked conclusion |
| --- | --- | --- |
| `TotalColoring.IsOutsideEdgeMinimalNoncolorable.false_of_critical_allD` | `CriticalAllDClosure` | A finite outside-edge-minimal noncolorable auxiliary member is impossible |
| `TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass` | `CriticalAllDClosure` | Every finite `InAuxiliaryClass D H J` has `HasValidRainbowColoring D H J` |
| `TotalColoring.Auxiliary.Extension.decode_valid` | `Auxiliary` | A proper selector-rainbow auxiliary assignment decodes to a valid total assignment |

`decode_valid` is conditional. The current library does not yet construct the
pair/singleton auxiliary extension needed to combine it with the terminal
all-orders theorem for an arbitrary input graph.

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
#check TotalColoring.Certificate.checkExtension_sound
```

The maintained version of this snippet is
[`docs/examples/Quickstart.lean`](https://github.com/chenle02/total-coloring-lean/blob/main/docs/examples/Quickstart.lean)
and is compiled by CI.
