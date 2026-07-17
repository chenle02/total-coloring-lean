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
      For every finite formal <code>InAuxiliaryClass D H J</code>, there exists
      a proper auxiliary edge coloring with palette <code>Fin (D + 2)</code>
      that is rainbow on <code>J</code>.
    </p>
    <p>
      The terminal declaration is
      <code>MinimalExtraction.hasValidRainbowColoring_of_inAuxiliaryClass</code>.
    </p>
    <p>
      With a supplied compatible <code>Auxiliary.Extension</code> whose
      selector edges lie in <code>distinguishedEdgeSet H J</code>, Lean
      composes this result into a valid total assignment with the same
      <code>Fin (D + 2)</code> palette.
    </p>
    <p><a href="proof-status/">Read the exact theorem →</a></p>
  </section>
  <section class="tc-card tc-card--boundary">
    <h2>What is not proved</h2>
    <p>
      This is not the Total Coloring Conjecture, not the proposed high-degree
      total-coloring theorem, and not an end-to-end reduction from an arbitrary
      graph. The equitable partition, concrete pair/singleton split-star
      constructor, relation between <code>D</code> and the original maximum
      degree, stronger palette, and novelty remain separate.
    </p>
    <p><a href="claim-boundary.json">Inspect the machine-readable boundary →</a></p>
  </section>
</div>

## Start with the theorem

```lean
import TotalColoring

#check TotalColoring.MinimalExtraction
  .hasValidRainbowColoring_of_inAuxiliaryClass
#check TotalColoring.Auxiliary.Extension
  .exists_valid_decode_of_inAuxiliaryClass
```

Both declarations are propositional existence theorems. They do not compute a
coloring from external data. For executable finite certificates, begin with
`TotalColoring.Certificate` and its soundness theorems.

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
      Follow the formal route from the auxiliary class through minimal
      extraction, maximal one-hole states, dominators, crossing, and the final
      contradiction.
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
