## Summary

<!-- What changed, and why is this the smallest reviewable unit? -->

## Mathematical and trust scope

<!-- State any changed hypotheses/conclusions. If none, say "No theorem-boundary change." -->

- [ ] I distinguished kernel-checked results from external mathematics,
      bounded computation, manuscript claims, and novelty.
- [ ] I introduced no `sorry`, `admit`, custom `axiom`, or `native_decide` in
      production Lean modules.
- [ ] If the public theorem boundary changed, I updated `README.md`,
      `docs/claim-boundary.json`, `docs/proof-status.md`, and `llms.txt`.
- [ ] If I added a Boolean checker, I also added a semantic soundness theorem.

## Validation

<!-- List the exact commands and CI runs. -->

- [ ] `lake exe cache get`
- [ ] `lake build`
- [ ] `lake env leanchecker`
- [ ] forbidden-token scan from `AGENTS.md`
- [ ] `git diff --check`
- [ ] `git diff --cached --check`
- [ ] documentation build, when documentation changed

## Reviewer notes

<!-- Point reviewers to the load-bearing declarations and any deliberately deferred work. -->
