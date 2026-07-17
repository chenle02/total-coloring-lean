# Exact proof status

## All-orders auxiliary theorem

At commit `310b82c174ab2281581900897d4646875575e89b`, the library proves:

```text
InAuxiliaryClass D H J
  →
HasValidRainbowColoring D H J
```

for every finite vertex type. The declaration is:

```lean
TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
```

`HasValidRainbowColoring D H J` means that there exists an
`EdgeAssignment H (Fin (D + 2))` which is proper and whose colors are pairwise
distinct on the distinguished edge set represented by `J`.

!!! success "Plain-language reading"

    Every finite graph-and-distinguished-set pair satisfying the exact formal
    predicate `InAuxiliaryClass D H J` has the required rainbow auxiliary edge
    coloring from the `D + 2` palette.

## Conditional auxiliary-to-total transfer

At commit `9bdcdec1a872ccef42cfd79e791fe39c22a1beeb`, the library also proves:

```lean
TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
```

Its explicit inputs are:

- a supplied conflict-preserving `Auxiliary.Extension G H`;
- a proof that every `X.classEdge vertex` belongs to
  `distinguishedEdgeSet H J`; and
- `InAuxiliaryClass D H J` on the finite auxiliary graph.

Its conclusion is:

```text
exists assignment : Assignment G (Fin (D + 2)), assignment.Valid.
```

!!! success "Plain-language reading"

    Once a compatible auxiliary extension has been supplied, the all-orders
    rainbow edge-coloring theorem and the semantic decoder compose to give a
    valid total coloring of the supplied original graph.

This is a conditional transfer theorem. It neither constructs the extension
from an arbitrary graph nor proves a relation between `D` and the original
graph's maximum degree.

## Structural hypothesis

`InAuxiliaryClass D H J` existentially supplies a center `x` and an off-center
matching `M`. Its checked fields require, among other things:

- `J` is exactly `M` together with the full star at `x`;
- `M` is a matching, lies off `x`, and avoids neighbors of `x`;
- every vertex other than `x` is incident with exactly one member of `J`;
- `J.card = D` and the ambient maximum degree is at most `D`;
- the center degree lies between `2` and `D`.

The source of truth is
[`TotalColoring/AuxiliaryClass.lean`](https://github.com/chenle02/total-coloring-lean/blob/310b82c174ab2281581900897d4646875575e89b/TotalColoring/AuxiliaryClass.lean).

## What the checked results do not establish

The checked results do **not** prove:

- the Total Coloring Conjecture;
- an unrestricted total-coloring theorem for all finite graph orders;
- either proposed high-degree total-coloring conclusion;
- the equitable-partition input;
- the concrete pair/singleton split-star instantiation of
  `Auxiliary.Extension`;
- an end-to-end total-coloring corollary from an arbitrary input graph without
  supplied extension, selector-membership, and auxiliary-class proofs;
- any identification of `D` with the maximum degree of `G`;
- the stronger auxiliary `D + 1` palette; or
- novelty of either checked result.

!!! warning "Palette warning"

    `Fin (D + 2)` is the auxiliary palette parameter. The transfer theorem
    reuses it for a total coloring of the supplied `G`, but no checked theorem
    identifies `D` with `Delta(G) + 1`. It must not be reported as a
    `Delta + 3` or `Delta + 2` conclusion.

## Provenance and distribution status

- The terminal theorem was introduced at `310b82c…`.
- Public Lean CI run
  [`29588129760`](https://github.com/chenle02/total-coloring-lean/actions/runs/29588129760)
  passed at that exact commit.
- The conditional transfer theorem was introduced at `9bdcdec…`; its proof
  source passed the full Easley build and leanchecker gate in Slurm job
  `5387732` (`COMPLETED`, exit `0:0`). The exact merged tree `c332155a…` then
  passed the same complete gate in job `5387751` (`COMPLETED`, exit `0:0`).
- PR [#6](https://github.com/chenle02/total-coloring-lean/pull/6)
  merged the transfer into `main` at `8ec71e7…`. Public Lean CI run
  [`29597109189`](https://github.com/chenle02/total-coloring-lean/actions/runs/29597109189)
  passed at PR head `16fca45…`, whose Git tree is identical to the merge
  commit's tree.
- Release `v0.1.0` predates both declarations. Cite an exact commit until a
  later release includes the result used.

For tools, the same boundary is mirrored in
[`claim-boundary.json`](claim-boundary.json). The Lean declarations at the
pinned commit remain authoritative if prose and code ever disagree.
