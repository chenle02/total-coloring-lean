# Total Coloring Lean contributor contract

This repository formalizes definitions and proof-producing verification
infrastructure for total coloring. Mathematical correctness and precise claim
boundaries take priority over breadth or automation.

## Scientific boundary

- The proved layer includes conditional auxiliary decoding; the structural
  class `A_D` and deletion closure; deleted-edge/one-hole transport; exact
  complete and partial `J`-rainbow swap safety; physical two-color components
  and boundary closure; finite missing-color counts; and the critical
  degree-sum checkpoint conditional on an explicitly outside-edge-minimal
  noncolorable member, including finite extraction of such a minimum from any
  assumed fixed-vertex, fixed-`J` counterexample and the residual degree sum.
- Do not state that this repository proves the Total Coloring Conjecture, the
  all-orders `A_D` rainbow-extension theorem, the proposed high-degree
  manuscript theorem, or all finite orders.
- Do not promote conditional extraction from an assumed counterexample into
  existence of a counterexample or into the all-orders extension theorem.
  Fans, endpoint location, and the crossing argument remain separate
  obligations.
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
