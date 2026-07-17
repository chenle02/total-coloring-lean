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
  It now also includes oriented center spokes, literal and finite fan shifts,
  simple center-dependency reachability, exact fan-path/reachability
  correspondence, and center--reachable-leaf elementarity in that conditional
  critical state. It further includes local no-branching and exact
  endpoint/internal missing-color geometry for genuine partial two-color
  components, literal fan-prefix repair in both the center-avoiding and
  through-center directions, and the corresponding exact critical component
  closure dichotomies. The finite global layer proves that, in every valid
  finite partial assignment, each genuine two-color component has at most two
  endpoints, without choosing a path/cycle classification. In the supplied
  critical state it proves multiplicity at most one on all dependency-
  reachable leaves for a color unused on `J`, multiplicity at most three for
  every color, and the local saturated three-leaf theorem placing both unique
  distinguished carriers in the matching. It also proves that if an unused
  color is missing at the center, every palette color has reachable
  multiplicity at most one, so any supplied repeated or triply missing color
  excludes unused colors from the center. On the canonical full dependency-
  reachable set `W`, it now proves the incidence lower bound
  `I(W) >= 2|W| + 1` and the occurring missing-color capacity
  `r(W) <= |W|`. Thus some color is missing at exactly three reachable
  leaves, and every color unused on `J` is absent from the fan center in every
  supplied minimal critical valid `J`-rainbow one-hole state whose root edge
  lies outside `J`. This closes critical-state spare-center exclusion without
  introducing a new `MaximalFan` structure. The general multiplicity-two fan
  premise remains explicit only in the earlier conditional incidence-count
  interface, and the local carrier theorem is not the later uniform or
  recentered matching-location result. Finally, in a supplied minimal critical
  valid `J`-rainbow one-hole state, a safe genuine two-color component swap
  meeting the center, with its left color missing there, preserves a designated
  `LinearFanPath` literally: a post-swap path exists with the identical root
  and tail. This closes full fixed selected-sequence survival, not merely an
  existential surviving-prefix statement, and needs no terminal-hole, carrier,
  unused-color, maximality, or fan-capacity hypothesis. Building on global
  spare-center exclusion, it also proves the centered carrier-label rotation
  wrapper: a genuine center-meeting swap between a center-missing color and a
  color unused on `J` crosses the unique distinguished carrier of the former,
  makes that edge the unique distinguished carrier of the latter, makes the
  former unused on `J`, and preserves the designated fan path exactly. A
  separate state-local layer counts the physical universe exactly, proves the
  fan-capacity bound `|W| + a <= D + z`, and proves `4 <= |W|` when a triply
  missing color is explicitly supplied with a non-`J` center edge; it does not
  use the centered rotation theorem. For one exact triple chosen by the
  reachable-set count, it also proves a state-local dichotomy whose literal
  center carrier is either mobile outside `J`, forcing `4 <= |W|`, or is the
  unique distinguished carrier in matching `M`. The latter remains a live
  frozen branch: `M` is off the auxiliary star center `x`, not the current fan
  center.
- Do not state that this repository proves the Total Coloring Conjecture, the
  all-orders `A_D` rainbow-extension theorem, the proposed high-degree
  manuscript theorem, or all finite orders.
- Do not promote conditional extraction from an assumed counterexample into
  existence of a counterexample or into the all-orders extension theorem.
  The used-color multiplicity-two strengthening, cross-state or global
  maximality properties of the canonical reachable set, mobility of an
  arbitrary triply missing color, contradiction of the chosen triple's frozen
  matching-carrier branch, uniform/recentered matching-`M` carrier
  location and center-incidence control, recentering and uniform endpoint
  location, root pivots, and the crossing argument remain separate obligations.
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
if rg -n \
  --glob '*.lean' \
  --glob '!.lake/**' \
  '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' \
  .; then
  exit 1
fi
git diff --check
git diff --cached --check
```

Commit `lake-manifest.json`. Change `lean-toolchain` and the mathlib revision
together, and rebuild the entire library after any toolchain update.
