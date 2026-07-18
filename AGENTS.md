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
  use the centered rotation theorem. For every supplied color missing on at
  least three reachable leaves, it also proves a state-local dichotomy whose
  literal center carrier is either mobile outside `J`, forcing `4 <= |W|`, or
  is the unique distinguished carrier in matching `M`. Matching-center
  carrier colors form a subsingleton, so two distinct triples force at least
  one mobile carrier. The recentered layer now proves fresh matching-carrier
  location at either endpoint of every supplied critical hole and transports
  the same literal carrier to every dependency-reachable missing color. Thus
  no unused-on-`J` color has a hole on canonical `W`, and the center/reachable
  colors satisfy the matching/star capacity bounds. A finite global interface
  chooses an oriented one-hole state of maximum canonical reach-card. The
  checked two-exchange strict-growth argument eliminates the exceptional
  frozen triple at that state, so every triple there is mobile. Literal
  one-step root pivots are also checked, including their exact missing-color
  and dependency-column updates, old-reachability containment, and equality
  of the physical reachable finset under global maximality. The library also
  contains the exact ordinary balanced fixed-witness exchange criterion and
  the fixed-`D` BKW threshold arithmetic interface through `D = 6`. The final
  auxiliary layer kernel-checks iterated direct-entry positioning, the
  directed-dominator `k = 1, 2, 3` split (including robust-column expansion
  and the crossing/detachment branch), and the resulting critical
  contradiction. Finite minimal extraction yields exactly
  `MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass`: for finite
  `V`, `InAuxiliaryClass D H J` implies `HasValidRainbowColoring D H J`, a
  proper `Fin (D + 2)` edge coloring rainbow on `J`.
- The composed declaration
  `Auxiliary.Extension.exists_valid_decode_of_inAuxiliaryClass` proves a
  conditional total-coloring transfer. Given a supplied conflict-preserving
  `Auxiliary.Extension G H`, proof that every selector edge lies in
  `distinguishedEdgeSet H J`, and `InAuxiliaryClass D H J`, it yields
  `∃ assignment : Assignment G (Fin (D + 2)), assignment.Valid`. It does not
  itself construct the extension or identify `D` with a parameter of `G`.
- Given a supplied `PairSingletonWitness G` on a finite vertex type with
  decidable equality, the module `PairSingletonExtension` constructs the
  ordinary auxiliary graph on `Option V`, packages its conflict maps as an
  `Auxiliary.Extension`, and proves every selector belongs to the corresponding
  distinguished edge set. It also proves exact selector coverage, that the
  off-center `matchingPart` is a matching avoiding the center and its
  neighbors, and that the distinguished family is the matching part together
  with the full center incidence star. It also proves the exact copied-vertex
  degree formula and center/class-count identity. The theorem
  `isAuxiliaryClassMember_of_class_count_and_bounds` derives the former
  maximum-degree and center-degree obligations from exact distinguished
  cardinality, an original-graph degree bound, and an order bound. Its
  specialization `isAuxiliaryClassMember_of_highDegree` uses
  `P.distinguished.card = G.maxDegree + 1` and
  `Fintype.card V <= 2 * G.maxDegree` to obtain structural membership with
  parameter `G.maxDegree + 1`.
- Given a supplied `EquitableIndependentPartition G D`, the module
  `EquitablePairSingleton` now kernel-checks the adapter under
  `D <= Fintype.card V` and `Fintype.card V < 2 * D`. It proves every class has
  size one or two, constructs `Q.toPairSingletonWitness`, and proves
  `(Q.toPairSingletonWitness ...).distinguished.card = D`. For a nonempty
  finite graph, a supplied partition with `D = G.maxDegree + 1` and
  `Fintype.card V <= 2 * G.maxDegree` produces `InAuxiliaryClass` and the
  conditional terminal result
  `Q.exists_valid_assignment_of_highDegreePartition`: a valid assignment with
  palette `ExtensionPalette (G.maxDegree + 1) = Fin (G.maxDegree + 3)`.
  This supplied-partition route remains available, but it is no longer the
  terminal boundary of the library.
- The modules `HighDegreeComplementMatching` and `MatchingExact` check the
  missing existence route: under
  `Fintype.card V <= 2 * G.maxDegree`, a nonempty finite graph has a complement
  matching of at least the target size, and that matching can be trimmed to
  exactly `Fintype.card V - (G.maxDegree + 1)` edges. The resulting matching
  supplies a `PairSingletonWitness G` with exactly `G.maxDegree + 1`
  distinguished edges. The module `EmptyAssignment` separately proves the
  vacuous valid assignment for an empty vertex type.
- The checked terminal declaration is
  `TotalColoring.exists_valid_assignment_of_highDegree`. For every
  `G : SimpleGraph V` with `[Fintype V]`, `[DecidableEq V]`, and
  `[DecidableRel G.Adj]`, its sole proposition-valued input is
  `Fintype.card V <= 2 * G.maxDegree`; it concludes
  `∃ assignment : Assignment G (ExtensionPalette (G.maxDegree + 1)),
  assignment.Valid`. Thus its palette has `G.maxDegree + 3` colors. It includes
  the empty vertex type and uses no even-order or other parity hypothesis.
- Do not state that this repository proves the Total Coloring Conjecture, the
  manuscript's still-unlocked main theorem, a `Delta + 2` conclusion, or an
  unrestricted total-coloring theorem outside the explicit high-degree
  hypothesis. Do not attach a novelty claim to the checked terminal theorem.
- The checked all-orders theorem is confined to the exact formal predicate
  `InAuxiliaryClass`. The conditional transfer uses the same `D + 2` type as a
  total-coloring palette only after a supplied extension is provided. The
  generic transfer does not identify `D`. The separate terminal theorem sets
  `D = Delta(G) + 1` and discharges the witness construction from the exact
  density hypothesis. Keep the abstract transfer, supplied-partition theorem,
  and terminal graph theorem distinct when documenting or reusing them.
- Verification provenance is tree-specific. Exact proof tree
  `4624044788ab42c0dc116cfbf7f38c696065263c`, source-archive SHA-256
  `302bc3f00bf5d8c1ce563d2bc84d1370e627c81d219e8d8085b286a21d530077`,
  passed five separate full-build, Quickstart, and leanchecker replays
  (`5388311`--`5388315`) with exit `0:0` and empty stderr. Those receipts do not
  certify the later publishable tree; run the complete
  gate and public CI on that exact tree before publishing a trust claim.
- Kernel verification establishes correctness of the formal statement, not
  novelty. Novelty remains subject to the literature check and author lock.
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

## Documentation consistency

- Lean declarations at a pinned commit are authoritative for proved claims.
  `docs/claim-boundary.json`, `llms.txt`, the Pages proof-status page, and the
  README are public mirrors and must not broaden the source statement.
- A change to the public theorem boundary must update those mirrors in the
  same reviewable pull request. Distinguish a release tag, the default branch,
  and an unmerged proof branch when they contain different results.
- Maintain `docs/examples/Quickstart.lean` as the canonical public declaration
  example. Every declaration shown in a copyable documentation snippet must
  appear there, and CI must compile the canonical file so examples cannot
  drift silently.

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
