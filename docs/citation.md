# Citation

GitHub exposes the repository's `CITATION.cff` through its **Cite this
repository** interface.

!!! warning "Release boundary"

    Release `v0.1.0` predates the all-orders auxiliary theorem, the conditional
    auxiliary-to-total transfer, and the terminal high-degree theorem. For the
    auxiliary theorem, cite exact commit
    `310b82c174ab2281581900897d4646875575e89b`; for the composed transfer, cite
    `9bdcdec1a872ccef42cfd79e791fe39c22a1beeb`; for
    `TotalColoring.exists_valid_assignment_of_highDegree`, cite merged main
    commit `0e938606f81e7a27a5925987824e7152f7dbb4c6` (exact verified tree
    `89a32c7a78e294a8b1484092ec79afaa3b4ace5a`), or use a later release that
    actually contains the declaration you need.

## Suggested commit-level citation

```bibtex
@software{ChenShanTotalColoringLean2026,
  author  = {Le Chen and Songling Shan},
  title   = {Total Coloring Lean},
  year    = {2026},
  url     = {https://github.com/chenle02/total-coloring-lean},
  note    = {Lean 4 source, commit 0e938606f81e7a27a5925987824e7152f7dbb4c6}
}
```

For reproducibility, record all three of:

1. the software release or exact commit;
2. Lean and mathlib version `v4.32.0`; and
3. the declaration(s) on which your result depends.

Do not cite the software repository as proof of novelty. Novelty requires a
separate literature analysis.
