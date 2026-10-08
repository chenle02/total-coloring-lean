#!/usr/bin/env bash
# Reject proof placeholders and native-evaluation axioms in tracked Lean files.
#
# Every tracked .lean file may not contain `sorry`, `admit`, `axiom` or
# `native_decide`, with one exception: a comparator challenge,
# Audit/<Claim>/Challenge.lean, states theorems whose proofs are `sorry` by
# design (see Audit/README.md). Such a file may contain `sorry` and nothing
# else from the list, and may import only Mathlib. Its Solution.lean is
# checked like any other file.
set -euo pipefail
cd "$(dirname "$0")/.."

word='(^|[^[:alnum:]_])(%s)([^[:alnum:]_]|$)'
status=0

# shellcheck disable=SC2059
if git grep -n -E "$(printf "$word" 'sorry|admit|axiom|native_decide')" \
    -- '*.lean' ':(exclude)Audit/*/Challenge.lean'; then
  status=1
fi

# shellcheck disable=SC2059
if git grep -n -E "$(printf "$word" 'admit|axiom|native_decide')" \
    -- 'Audit/*/Challenge.lean'; then
  status=1
fi

if git grep -n -E '^import ' -- 'Audit/*/Challenge.lean' | grep -v -E ':import Mathlib[[:space:]]*$'; then
  echo "a comparator challenge may import only Mathlib" >&2
  status=1
fi

exit "$status"
