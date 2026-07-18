<div class="tc-hero">
  <img src="assets/logo.svg" alt="Total Coloring Lean graph logo">
  <p class="tc-kicker">Kernel-checked combinatorics</p>
  <h1>Total Coloring Lean</h1>
  <p>
    Lean 4 foundations for total coloring, constrained auxiliary edge coloring,
    and proof-producing certificate checks.
  </p>
  <div class="tc-actions">
    <a href="getting-started/" class="md-button md-button--primary">Get started</a>
    <a href="proof-status/" class="md-button">Exact proof boundary</a>
    <a href="https://github.com/chenle02/total-coloring-lean" class="md-button">Browse source</a>
    <a href="https://github.com/sponsors/chenle02" class="md-button">Sponsor</a>
  </div>
</div>

<div class="tc-grid">
  <section class="tc-card tc-card--proved">
    <h2>What is proved</h2>
    <p>
      For every finite graph <code>G</code> satisfying
      <code>Fintype.card V &lt;= 2 * G.maxDegree</code>, Lean proves the existence
      of a valid total assignment with palette
      <code>ExtensionPalette (G.maxDegree + 1)</code>.
    </p>
    <p>
      The terminal declaration is
      <code>TotalColoring.exists_valid_assignment_of_highDegree</code>. It
      includes the empty vertex type and uses no parity hypothesis.
    </p>
    <p>
      For a nonempty graph, the checked proof obtains a sufficiently large
      matching in the complement, trims it to the exact required size,
      converts it to a <code>PairSingletonWitness</code>, proves membership in
      the auxiliary class, applies the all-orders rainbow theorem, and decodes
      the result. The empty graph is discharged separately by a vacuous valid
      assignment.
    </p>
    <p>
      The lower-level supplied-input interfaces remain public: users may start
      from an <code>Auxiliary.Extension</code>, a
      <code>PairSingletonWitness</code>, or an
      <code>EquitableIndependentPartition</code>. The abstract theorem for
      every finite <code>InAuxiliaryClass D H J</code> also remains available.
    </p>
    <p><a href="proof-status/">Read the exact theorem →</a></p>
  </section>
  <section class="tc-card tc-card--boundary">
    <h2>What is not proved</h2>
    <p>
      This package theorem is not the Total Coloring Conjecture, does not prove
      the stronger <code>Delta + 2</code> target, and does not establish a paper
      theorem or novelty claim. Those manuscript claims remain under their own
      author and literature-review gates. The current cluster receipt verifies
      the exact proof-development tree; the later public integration tree still
      requires its own publication trust gate.
    </p>
    <p><a href="claim-boundary.json">Inspect the machine-readable boundary →</a></p>
  </section>
</div>

## Start with the theorem

```lean
import TotalColoring

#check TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.exists_valid_assignment_of_highDegree
#check TotalColoring.Auxiliary
  .exists_valid_assignment_of_highDegree_nonempty
#check TotalColoring.MatchingLowerBound
  .exists_complement_matchingGraph_edgeFinset_card_eq
#check TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.PairSingletonWitness.extension
#check TotalColoring.Auxiliary.PairSingletonWitness
  .classEdge_mem_distinguishedEdgeSet
#check TotalColoring.Auxiliary.PairSingletonWitness
  .isAuxiliaryClassMember_of_highDegree
#check TotalColoring.Auxiliary.EquitableIndependentPartition
  .exists_valid_assignment_of_highDegreePartition
```

These coloring declarations are propositional existence theorems. They do not
compute a coloring from external data. For executable finite certificates,
begin with `TotalColoring.Certificate` and its soundness theorems.

## Choose your route

<div class="tc-grid">
  <section class="tc-card">
    <h3>Use the library</h3>
    <p>
      Install the pinned Lean toolchain, fetch the mathlib cache, build, and
      import the umbrella module.
    </p>
    <p><a href="getting-started/">Installation and first checks</a></p>
  </section>
  <section class="tc-card">
    <h3>Audit the proof</h3>
    <p>
      Follow the formal route from complement matching and exact extraction to
      the auxiliary class, then through minimal extraction, maximal one-hole
      states, crossing, the final contradiction, and semantic decoding.
    </p>
    <p><a href="architecture/">Proof architecture</a></p>
  </section>
  <section class="tc-card">
    <h3>Build with an agent</h3>
    <p>
      Give a coding agent the exact authority order, public entrypoints,
      forbidden inferences, and reproducibility gates.
    </p>
    <p>
      <a href="for-agents/">Agent guide</a> ·
      <a href="https://chenle02.github.io/total-coloring-lean/llms.txt"><code>/llms.txt</code></a>
    </p>
  </section>
</div>

## Reproducibility before spectacle

The repository separates semantic propositions, executable checks, and
external data. Production proofs contain no `sorry`, `admit`, custom `axiom`,
or `native_decide`. CI builds the umbrella import and replays declarations with
`leanchecker`.

[Understand the trust boundary →](trust.md)
