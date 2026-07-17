# Trust and reproduction

## What is trusted

The formal result is checked by the Lean 4.32.0 kernel using the pinned mathlib
revision. Production modules prohibit proof placeholders and trust-expanding
shortcuts:

- `sorry`
- `admit`
- custom `axiom` declarations
- `native_decide`

The CI scan and local contribution gate reject these tokens in production Lean
sources.

## Complete repository gate

Run from the repository root:

```sh
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

`leanchecker` replays compiled declarations with an independent executable and
can require substantially more memory than an ordinary incremental build. CI
runs the full gate for public pull requests.

## Certificates are not axioms

`TotalColoring.Certificate` contains Boolean checkers plus theorems relating
acceptance to semantic propositions. A solver may produce an assignment, but
Lean validates the well-typed certificate before it contributes evidence.

A checked positive assignment proves that assignment valid. It does not prove
that an external generator enumerated every graph in scope.

## Deliberately outside the initial interface

Arbitrary JSON bytes are not trusted. A future parser must validate shape,
bounds, graph identity, and certificate identity before constructing typed Lean
values. Search algorithms and schemas belong in
[`total-coloring-toolkit`](https://github.com/chenle02/total-coloring-toolkit),
while reviewed finite artifacts belong in
[`total-coloring-data`](https://github.com/chenle02/total-coloring-data).

## Documentation trust

The machine-readable [`claim-boundary.json`](claim-boundary.json) and these
pages are navigation aids. If documentation and source disagree, the Lean
declarations at the pinned commit are authoritative. Please report any drift
as a documentation issue.
