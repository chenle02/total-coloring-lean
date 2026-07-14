# Contributing

Contributions are welcome when they preserve the repository's mathematical
and software trust boundaries.

## Development setup

Install `elan`, clone the repository, and let the checked-in toolchain file
select the exact Lean release:

```bash
elan show
lake update
lake exe cache get
lake build
```

`lake update` is needed when creating a fresh manifest or deliberately changing
a dependency pin. Ordinary builds must use the committed `lake-manifest.json`.

## Pull requests

1. Open an issue for a new mathematical interface or a changed theorem claim.
2. Keep each change small enough for its assumptions and conclusions to be
   reviewed directly.
3. Add a checked example or regression theorem when changing executable code.
4. Prove a soundness theorem for every new Boolean checker.
5. Run the complete quality gate from `AGENTS.md`.
6. Do not commit generated census output, private manuscript text, credentials,
   or local build products.

Documentation must distinguish a proved Lean theorem from a conjecture, a
bounded computation, and an external result cited from the literature.
