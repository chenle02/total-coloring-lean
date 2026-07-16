# Total Coloring Lean

[![Lean CI](https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/chenle02/total-coloring-lean/actions/workflows/ci.yml)

`total-coloring-lean` is a Lean 4 library for formal definitions and
kernel-checked proof foundations in total-coloring research. Its verified
layer includes conditional auxiliary decoding, the structural class `A_D`
and its deletion closure, deleted-edge/one-hole transport, physical
two-color components with exact distinguished-edge safety, and the full
critical degree-sum checkpoint for a hypothetical edge-minimal noncolorable
member, including extraction of such a minimum from any fixed-`V`, fixed-`J`
counterexample. The next checked layers formalize simple ordered fan paths,
legal hole shifts, dependency reachability, center--reachable-leaf
elementarity, local vertex geometry of genuine physical two-color components,
and all-leaf fan-prefix repair inside that conditional critical state.

## Current proof boundary

The library currently proves:

- semantic definitions of total and edge colorings;
- executable finite checkers and theorems characterizing their acceptance;
- soundness of the total-, edge-, rainbow-, and combined auxiliary checkers;
- the conditional auxiliary decoding theorem;
- partial proper edge colorings and the theorem that a color missing at both
  endpoints properly fills the unique uncolored edge;
- the matching-plus-full-star definition of `A_D`, its pair-level wrapper,
  and closure under deletion of an edge outside `J`;
- the exact bridge between stable `Sym2` distinguished finsets and the edge
  subtype used by colorings;
- the exact `J`-rainbow two-color swap criterion, including the unused-color
  and same-side unique-carrier cases;
- physical two-color reachability components for complete and partial edge
  assignments, including proofs that they supply boundary closure and preserve
  properness and the unique hole;
- explicit transport of a valid rainbow coloring of `H - e` to a valid
  rainbow one-hole coloring of `H`;
- finite-palette missing-color finsets, blocked-fill disjointness, and the
  sharp one-hole missing-color count;
- the conditional minimal-counterexample checkpoint deriving
  `D + 4 <= degreeU + degreeV` for every edge outside `J`, without separately
  assumed missing-set or cardinality bounds;
- the zero-outside-edge base coloring and hence existence of an outside edge
  in every supplied minimal noncolorable member;
- finite extraction of an outside-edge-minimal noncolorable member from any
  counterexample on the same finite vertex type and stable `J`;
- the residual bound
  `D + 2 <= degree_(H-J)(u) + degree_(H-J)(v)` for every outside edge in the
  conditional critical state;
- literal two-edge hole moves and finite duplicate-free edge shifts, with
  exact properness and unique-hole criteria plus explicit sufficient
  distinguished-rainbow preservation conditions;
- explicitly oriented center spokes, simple `J`-free linear fan paths, and
  the exact correspondence between those paths and center-dependency
  reachability;
- kernel-derived legality of every fan shift, including center missing-color
  invariance and persistence of terminal-leaf missing colors;
- center--reachable-leaf elementarity for every supplied minimal
  noncolorable member;
- local no-branching plus exact endpoint/internal missing-color geometry for
  genuine partial two-color components, with unsupported raw reachability
  roots kept outside the genuine-component interface;
- literal nonempty fan-prefix extraction, including the singleton root case,
  and structural prefix repair after a physical component swap that avoids
  the fan center;
- in a supplied minimal critical state, the conditional all-leaf dichotomy
  that a genuine two-color component meeting the selected terminal leaf
  either meets the center or fails the exact `SwapCompatibleOn` condition;
- arbitrary-vertex missing-color lower bounds and the conditional fan count
  giving `|W| + 1` distinct leaf-missing colors when the still-unproved
  multiplicity-two premise is supplied; and
- tiny positive and negative examples.

The library does **not** currently prove:

- the Total Coloring Conjecture;
- existence of the required rainbow auxiliary edge coloring;
- the proposed high-degree theorem with either `Δ + 2` or `Δ + 3` colors;
- the all-orders `A_D` rainbow-extension theorem from the companion proof
  program;
- the Hajnal–Szemerédi theorem or a construction of the required equitable
  partition;
- the split-star transfer or the actual pair/singleton construction;
- global path/cycle classification or an at-most-two-component-endpoints
  theorem, spare-color leaf multiplicity, general leaf-multiplicity and
  carrier-location lemmas, fan capacity and global maximality,
  endpoint-location lemmas, root pivots, or the direct-entry crossing
  argument; or
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
- `TotalColoring.AuxiliaryClass`: the witnessed and pair-level definitions of
  `A_D` and structural deletion closure.
- `TotalColoring.Distinguished`: stable-`J` to edge-subtype transport,
  cardinality, and coverage.
- `TotalColoring.DeletionBridge`: transport from a coloring of `H - e` to a
  one-hole partial coloring of `H`.
- `TotalColoring.PartialSwap`: exact swap safety for partial assignments.
- `TotalColoring.Kempe` and `TotalColoring.PartialKempe`: physical two-color
  reachability components and boundary closure.
- `TotalColoring.Missing` and `TotalColoring.MissingCount`: endpoint missing
  finsets, direct-fill obstruction, and sharp one-hole counts.
- `TotalColoring.CriticalState`: the explicit outside-edge-minimal
  noncolorable interface, blocked one-hole state, and degree-sum checkpoint.
- `TotalColoring.MinimalExtraction`: finite extraction of the minimal critical
  state from an arbitrary fixed-`V`, fixed-`J` counterexample.
- `TotalColoring.ResidualDegree`: exact removal of one distinguished incidence
  at each noncenter vertex and the residual critical degree sum.
- `TotalColoring.Fan` and `TotalColoring.CenterSpoke`: generic hole shifts and
  explicitly oriented center edges.
- `TotalColoring.SimpleReachability`, `TotalColoring.Dependency`,
  `TotalColoring.OrderedFan`, and `TotalColoring.FanReachability`: loop-erased
  dependency paths and their exact simple-fan realization.
- `TotalColoring.FanShift` and `TotalColoring.CriticalFan`: legal iterated fan
  shifts and conditional center--reachable-leaf elementarity.
- `TotalColoring.TwoColorGeometry`: local vertex no-branching,
  endpoint/internal characterization, and exact missing-label transport for
  genuine partial two-color components.
- `TotalColoring.FanPrefix`, `TotalColoring.FanPrefixRepair`, and
  `TotalColoring.CriticalAllLeaf`: literal fan prefixes, structural repair
  after a center-avoiding component swap, and the conditional
  meet-center-or-incompatible all-leaf theorem.
- `TotalColoring.FanCount`, `TotalColoring.FanMissingCount`,
  `TotalColoring.MissingGeneralCount`, `TotalColoring.FanLeaves`, and
  `TotalColoring.CriticalFanCount`: the finite missing-incidence layer with
  multiplicity two retained as an explicit hypothesis.
- `TotalColoring.Examples` and `TotalColoring.Wave4Examples`: tiny acceptance,
  rejection, unsupported-root, endpoint-swap, and singleton-prefix checks.

## Relation to the paper proof program

The modules now kernel-check the paper proof program through the critical
degree-sum checkpoint, legal fan shifts, center--reachable-leaf elementarity,
and the prefix-repair slice of all-leaf Kempe closure, all conditional on a
hypothetical outside-edge-minimal noncolorable member. They also extract such
a minimum from any assumed fixed-`V`, fixed-`J` counterexample. They do not
prove that a counterexample exists or that every `A_D` member is colorable.
The auxiliary-proof track next requires global two-color endpoint capacity,
spare and general leaf multiplicity, carrier-location lemmas, fan
capacity/maximality, endpoint location, root pivots, and the direct-entry
crossing argument. The reduction track still requires the split-star and
pair/singleton construction. No manuscript theorem is considered
Lean-verified until those obligations close and the authors lock the theorem
statement.

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
