# Total Coloring Lean

[![Lean CI](https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml)

`total-coloring-lean` is a Lean 4 library for formal definitions and
kernel-checked proof foundations in total-coloring research. Its verified
layer includes the conditional auxiliary reduction, one-hole completion,
exact distinguished-edge safety for two-color swaps, and the finite-set
arithmetic in the critical degree-sum argument.

## Current proof boundary

The library currently proves:

- semantic definitions of total and edge colorings;
- executable finite checkers and theorems characterizing their acceptance;
- soundness of the total-, edge-, rainbow-, and combined auxiliary checkers;
- the conditional auxiliary decoding theorem;
- partial proper edge colorings and the theorem that a color missing at both
  endpoints properly fills the unique uncolored edge;
- the exact `J`-rainbow two-color swap criterion, including the unused-color
  and same-side unique-carrier cases;
- preservation of properness under an explicit two-color boundary-closure
  hypothesis;
- the cardinality and natural-number arithmetic deriving
  `D + 4 <= degreeU + degreeV` from disjoint endpoint missing sets; and
- tiny positive and negative examples.

The library does **not** currently prove:

- the Total Coloring Conjecture;
- existence of the required rainbow auxiliary edge coloring;
- the proposed high-degree theorem with either `Δ + 2` or `Δ + 3` colors;
- the all-orders `A_D` rainbow-extension theorem from the companion proof
  program;
- the Hajnal–Szemerédi theorem or a construction of the required equitable
  partition;
- a physical Kempe-component API proving the boundary-closure hypothesis;
- a bridge applying the complete-assignment swap theorem to a one-hole partial
  coloring, or equivalently to the edge-deleted graph;
- missing-set disjointness and its cardinality hypotheses from a formalized
  minimal nonextendable `A_D` instance; or
- completeness of any external graph census.

Bounded computations remain finite evidence. Checking every stored positive
witness does not by itself prove that an external generator listed every graph
in scope.

## Modules

- `TotalColoring.Graph`: incidence and finite line-graph decidability.
- `TotalColoring.Total`: semantic total- and edge-coloring assignments.
- `TotalColoring.Auxiliary`: structural extension data and conditional decoding.
- `TotalColoring.Certificate`: executable checkers and soundness theorems.
- `TotalColoring.Partial`: partial edge colorings, missing colors, one-hole
  filling, and conversion of complete partial assignments.
- `TotalColoring.RainbowSwap`: exact `J`-rainbow swap safety and the separate
  properness boundary condition.
- `TotalColoring.Critical`: disjoint-finset counting and the critical
  degree-sum arithmetic.
- `TotalColoring.Examples`: tiny acceptance and rejection checks.

## Relation to the paper proof program

The modules formalize stable seams used by the proof program; they do not
replace its remaining graph-theoretic argument. The next dependency chain is
to define finite palettes and distinguished sets, formalize the class `A_D`
and its deletion-minimal one-hole state, derive the endpoint missing-set
hypotheses, bridge partial one-hole states to swaps on the edge-deleted graph,
and show that an actual two-color component satisfies the abstract
boundary-closure condition. Fans, shifts, endpoint-location lemmas, the
direct-entry crossing argument, and the uniform `A_D` extension theorem remain
later kernel obligations. No manuscript theorem is considered Lean-verified
until those obligations close and the authors lock the theorem statement.

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
