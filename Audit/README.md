# Comparator audit

Each directory here restates one headline theorem of the library for
[lean-pkg](https://github.com/lean-pkg/lean-pkg)'s comparator tier.

| Directory | Statement | Proved by |
|---|---|---|
| `HighDegree` | every finite graph with at most twice its maximum degree many vertices has a total coloring with `Δ + 3` colors | `TotalColoring.exists_valid_assignment_of_highDegree` |
| `AuxiliaryClass` | every member of the auxiliary class `A_D` has a proper `(D + 2)`-edge coloring that is rainbow on its distinguished set | `TotalColoring.MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass` |

- `Challenge.lean` states the theorem with Mathlib's definitions only (it imports
  nothing else) and leaves the proof as `sorry`. It is a statement for people to
  read and check against the paper, not a production module; it is the one
  place where `sorry` is allowed (`scripts/check-placeholders.sh`).
- `Solution.lean` states the same theorem, with the same name, and proves it from
  the library. It is held to the full placeholder rule.
- `comparator/config-*.json` lists each pair. The comparator checks that every
  Solution theorem has exactly its Challenge's type, uses only `propext`,
  `Classical.choice` and `Quot.sound`, and replays in a second kernel; its
  receipt is in `.lean-receipts/`.

The comparator does not check that a Challenge says what the paper says. That
was checked by hand: the hypotheses of `AuxiliaryClass` are the fields of
`IsAuxiliaryClassMember`, with the center and matching as explicit arguments
instead of an existential in a hypothesis, which is equivalent.

Build with `lake build Audit` (not a default target). The library turns
`warningAsError` off for itself only, since each Challenge warns about its
`sorry`.
