# Exact proof status

## Terminal checked theorem

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

## What the theorem does not establish

The checked result does **not** prove:

- the Total Coloring Conjecture;
- an unrestricted total-coloring theorem for all finite graph orders;
- either proposed high-degree total-coloring conclusion;
- the equitable-partition input;
- the concrete pair/singleton auxiliary construction;
- the split-star transfer;
- an end-to-end total-coloring corollary from an input graph;
- the stronger auxiliary `D + 1` palette; or
- novelty of the auxiliary theorem.

!!! warning "Palette warning"

    `Fin (D + 2)` is the palette of the auxiliary **edge coloring**. It must not
    be reported as a `Delta + 2` total-coloring conclusion.

## Provenance and distribution status

- The terminal theorem was introduced at `310b82c…`.
- Public Lean CI run
  [`29588129760`](https://github.com/chenle02/total-coloring-lean/actions/runs/29588129760)
  passed at that exact commit.
- The default branch contains the theorem through merge commit `eddf811…`.
- Release `v0.1.0` predates the theorem. Cite an exact commit when using the
  all-orders auxiliary result until a later release includes it.

For tools, the same boundary is mirrored in
[`claim-boundary.json`](claim-boundary.json). The Lean declarations at the
pinned commit remain authoritative if prose and code ever disagree.
