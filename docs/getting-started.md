# Getting started

## Prerequisites

Install [elan](https://lean-lang.org/lean4/doc/setup.html), Git, and a C/C++
toolchain suitable for Lean. The repository pins Lean and mathlib to version
`v4.32.0`; do not substitute a floating toolchain.

## Clone and build

```sh
git clone https://github.com/chenle02/total-coloring-lean.git
cd total-coloring-lean
lake exe cache get
lake build
```

`lake exe cache get` downloads compatible mathlib build artifacts. The first
build without a useful cache can take substantially longer.

## Confirm the public entrypoints

The following file is compiled by CI, so the example cannot silently drift.

```lean
--8<-- "docs/examples/Quickstart.lean"
```

Run it directly with:

```sh
lake env lean docs/examples/Quickstart.lean
```

## Use the library downstream

Import the umbrella module when exploring:

```lean
import TotalColoring
```

For a smaller dependency surface, import the module that owns the declaration
you need. The [theorem index](theorem-index.md) lists the principal public
entrypoints and source modules.

## Build the documentation

```sh
python3 -m venv .venv-docs
. .venv-docs/bin/activate
python -m pip install --requirement requirements-docs.txt
bash scripts/build-docs.sh
```

The generated site is in `site/`. Preview it with:

```sh
python -m http.server --directory site 8000
```

Then open `http://127.0.0.1:8000/`.

## Before contributing

Read [`CONTRIBUTING.md`](https://github.com/chenle02/total-coloring-lean/blob/main/CONTRIBUTING.md)
and the stricter repository contract in
[`AGENTS.md`](https://github.com/chenle02/total-coloring-lean/blob/main/AGENTS.md).
The complete gate includes `lake build`, `leanchecker`, the forbidden-token
scan, and both Git diff checks.
