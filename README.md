# Total Coloring Lean

[![Lean CI](https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml)

`total-coloring-lean` is a Lean 4 library for formal definitions and
proof-producing certificate checks in total-coloring research. Its first
verified result is the conditional auxiliary reduction: a proper auxiliary
edge coloring that is rainbow on the distinguished family decodes to a valid
total coloring when the stated structural obligations hold.

## Current proof boundary

The library currently proves:

- semantic definitions of total and edge colorings;
- executable finite checkers and theorems characterizing their acceptance;
- soundness of the total-, edge-, rainbow-, and combined auxiliary checkers;
- the conditional auxiliary decoding theorem; and
- tiny positive and negative examples.

The library does **not** currently prove:

- the Total Coloring Conjecture;
- existence of the required rainbow auxiliary edge coloring;
- the proposed high-degree theorem with either `Δ + 2` or `Δ + 3` colors;
- the Hajnal–Szemerédi theorem or a construction of the required equitable
  partition; or
- completeness of any external graph census.

Bounded computations remain finite evidence. Checking every stored positive
witness does not by itself prove that an external generator listed every graph
in scope.

## Modules

- `TotalColoring.Graph`: incidence and finite line-graph decidability.
- `TotalColoring.Total`: semantic total- and edge-coloring assignments.
- `TotalColoring.Auxiliary`: structural extension data and conditional decoding.
- `TotalColoring.Certificate`: executable checkers and soundness theorems.
- `TotalColoring.Examples`: tiny acceptance and rejection checks.

## Trust boundary

Solver output is treated as an untrusted witness. A Boolean result becomes a
Lean theorem only through a proved soundness statement. The initial API checks
already well-typed Lean values; it does not yet parse the JSON certificate
format used by the companion Python toolkit. A future interoperability layer
must separately validate serialization, palette bounds, graph identity, and
the correspondence between numbered edges and Lean edge subtypes.

## Build

The repository pins Lean and mathlib `v4.32.0` and commits the complete Lake
manifest.

```bash
elan show
lake exe cache get
lake build
lake env leanchecker
```

CI also rejects proof placeholders and unreviewed native-evaluation axioms,
verifies that every module is imported, and rebuilds the library with the
pinned Lean kernel and mathlib manifest. Lean's bundled declaration replayer
then checks the compiled project environment; it is a defense against build-
environment tampering, not an independent implementation of Lean.

## Related repositories

- [`total-coloring-toolkit`](https://github.com/chenle02/total-coloring-toolkit):
  search algorithms, schemas, and independent Python verifiers.
- [`total-coloring-data`](https://github.com/chenle02/total-coloring-data):
  reviewed, hash-pinned finite artifacts and release reports.

Raw runs, checkpoints, and private manuscript material belong in neither this
repository nor the public data repository.

## License and citation

The code and formalization are available under the MIT License. Citation
metadata is provided in `CITATION.cff`.
