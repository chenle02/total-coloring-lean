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
    <p>
      On proof branch <code>agent/independent-seed-endpoint</code>, the separate
      theorem <code>exists_valid_assignment_of_independentSeedPeel</code>
      constructs a <code>Fin (q + 1)</code> total assignment from a supplied
      proper <code>Fin q</code> edge coloring, independent seed, and peel
      certificate. Its direct maximum-degree wrapper has palette
      <code>Fin (G.maxDegree + 2)</code>, while retaining all of those witnesses
      as explicit hypotheses. Two sealed Easley trust replays passed at exact
      source tree <code>9af6a84e...</code>.
    </p>
    <p>
      The later proof branch
      <code>agent/total-independent-selector-decoder</code> checks a broader
      supplied-witness decoder: an independent fresh-color vertex set may be
      combined with a matching of fresh-color edges avoiding it, an
      actual-list-colored core, and a core-relative peel certificate. An
      explicit alternating rainbow-path certificate wrapper checks the donor
      exchange. The maximum-degree wrappers have palette
      <code>Fin (G.maxDegree + 2)</code>, but all edge-coloring,
      selector/core, path, and peel witnesses remain hypotheses. Exact source
      tree <code>1847934c...</code> passed sealed Easley job
      <code>5391803</code>.
    </p>
    <p>
      The stacked branch
      <code>agent/partial-edge-selector-normalization</code> weakens the old
      edge premise further: colors stored on the selected matching are
      ignored, and properness is required only outside it. It also gives an
      exact reverse decomposition of any supplied valid total coloring after
      choosing one fresh color class. The decoded assignment is literally the
      supplied assignment. This converse starts from the coloring and does
      not establish its existence.
    </p>
    <p><a href="proof-status/">Read the exact theorem →</a></p>
  </section>
  <section class="tc-card tc-card--boundary">
    <h2>What is not proved</h2>
    <p>
      This package does not prove the Total Coloring Conjecture or an
      unconditional <code>Delta + 2</code> theorem, and it does not establish a
      paper theorem or novelty claim. The proof-branch endpoint does not prove
      Vizing's theorem or existence of its seed/certificate inputs. The newer
      selector branch likewise does not prove existence of its selector,
      canonical core, peel order, or alternating rainbow path. Those
      statements are not supplied by the later normalization either, because
      that construction assumes a valid total coloring as input. Those
      manuscript claims remain under their own author and literature-review
      gates. Each cited source tree received tree-specific verification.
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
#check TotalColoring.exists_valid_assignment_of_independentSeedPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeIndependentSeedPeel
#check TotalColoring.SelectorCorePeelCertificate
#check TotalColoring.exists_valid_assignment_of_totalIndependentSelectorPeel
#check TotalColoring.exists_valid_assignment_of_maxDegreeTotalIndependentSelectorPeel
#check TotalColoring.AlternatingRainbowPathSelectorCertificate
#check TotalColoring.exists_valid_assignment_of_alternatingRainbowPathSelector
#check TotalColoring.exists_valid_assignment_of_maxDegreeAlternatingRainbowPathSelector
#check TotalColoring.EdgeAssignment.ValidOutside
#check TotalColoring.partialEdgeSelectorAssignment_valid
#check TotalColoring.PartialEdgeSelectorNormalization
#check TotalColoring.partialEdgeSelectorNormalization_of_valid
#check TotalColoring.maxDegreePartialEdgeSelectorNormalization_of_valid
```

The independent-seed declarations require proof branch
`agent/independent-seed-endpoint`; the six selector/path declarations after
them require `agent/total-independent-selector-decoder`. The final five
partial-edge/normalization declarations require the stacked branch
`agent/partial-edge-selector-normalization`. None is yet on `main`. The
forward coloring declarations are propositional existence theorems, while the
normalization declarations start from a supplied valid assignment.
They do not compute a coloring from external data. For executable finite
certificates, begin with `TotalColoring.Certificate` and its soundness
theorems.

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
