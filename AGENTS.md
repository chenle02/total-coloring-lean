# Total Coloring Lean contributor contract

This repository formalizes definitions and proof-producing verification
infrastructure for total coloring. Mathematical correctness and precise claim
boundaries take priority over breadth or automation.

## Scientific boundary

- The current proved result is conditional decoding: a proper auxiliary edge
  coloring that is rainbow on a structurally valid distinguished family yields
  a valid total coloring.
- Do not state that this repository proves the Total Coloring Conjecture, the
  proposed universal rainbow-extension statement, or all finite orders.
- A checked positive assignment proves that assignment is valid. It does not
  prove that an external graph enumeration was complete.
- External solver output is an untrusted witness until a checker accepts it.
- External JSON bytes are outside the initial trusted interface. A future
  parser must validate shape, bounds, graph identity, and certificate identity
  before constructing the typed values checked here.

## Proof discipline

- Do not add `sorry`, `admit`, custom `axiom` declarations, or
  `native_decide` to production Lean modules. The committed tiny examples use
  kernel reduction with `decide`; any future trust-boundary change requires
  explicit review and documentation.
- Keep conjectures in documentation or as clearly named proposition
  definitions. Do not present an unproved proposition as a theorem.
- Prefer small semantic definitions and explicit soundness theorems over
  tactics that hide the trust boundary.
- New executable checkers require a theorem connecting Boolean acceptance to
  the semantic proposition.
- Changes to auxiliary decoding must retain separate hypotheses for vertex,
  edge-edge, and vertex-edge conflicts.

## Repository boundary

- Formal definitions, proofs, checkers, and tiny fixtures belong here.
- Search algorithms and JSON schemas belong in `total-coloring-toolkit`.
- Reviewed finite artifacts belong in `total-coloring-data`.
- Raw runs, private drafts, and generated census output do not belong here.

## Required checks

Run from the repository root before every commit:

```bash
lake exe cache get
lake build
lake env leanchecker
if git grep -n -E \
  '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' \
  -- '*.lean'; then
  exit 1
fi
git diff --check
```

Commit `lake-manifest.json`. Change `lean-toolchain` and the mathlib revision
together, and rebuild the entire library after any toolchain update.
