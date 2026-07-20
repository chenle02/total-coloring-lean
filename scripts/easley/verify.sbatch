#!/bin/bash
# verify.sbatch — full Lean trust-gate for total-coloring-lean on Easley.
#
# Runs the AGENTS.md verification contract on a high-memory Dept node because
# leanchecker peaks at 117-142 GiB (lean-easley-slurm-verification skill) and
# cannot fit on the 62 GiB Greenwood workstation. Submitted by ~/bin/leancheck.
#
# Submit (from ~/total-coloring-lean on Easley):
#   sbatch --parsable scripts/easley/verify.sbatch

#SBATCH --job-name=tclean-verify
#SBATCH --partition=mathdep_bg2,abebeas_bg2,abebeas_std
#SBATCH --nodes=1
#SBATCH --ntasks=1
#SBATCH --cpus-per-task=24
#SBATCH --mem=180G
#SBATCH --time=02:00:00
#SBATCH --output=/scratch/%u/tclean/logs/verify-%j.out
#SBATCH --error=/scratch/%u/tclean/logs/verify-%j.err
#SBATCH --mail-type=END,FAIL
#SBATCH --mail-user=lzc0090@auburn.edu

set -euo pipefail

mkdir -p "/scratch/$USER/tclean/logs"

# Node-local build tree — never build on shared GPFS scratch (I/O contention).
WORK="${SLURM_TMPDIR:-/tmp/$USER/tclean-$SLURM_JOB_ID}"
mkdir -p "$WORK"
trap 'rm -rf -- "$WORK"' EXIT

REPO="$HOME/total-coloring-lean"
[[ -f "$REPO/lakefile.toml" ]] || { echo "no Lean project at $REPO"; exit 66; }

# Copy the committed source into node-local storage (not .lake build artifacts).
git -C "$REPO" archive --format=tar HEAD | tar -x -C "$WORK"
cd "$WORK"

HEAD_SHA="$(git -C "$REPO" rev-parse HEAD)"
echo "=== total-coloring-lean verify @ ${HEAD_SHA} on $(hostname) ==="

# Elan/Lake toolchain (pinned by lean-toolchain: leanprover/lean4:v4.32.0).
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export PATH="$ELAN_HOME/bin:$PATH"

echo "--- [1/4] lake exe cache get (mathlib cache restore) ---"
lake exe cache get

echo "--- [2/4] lake build (full package) ---"
lake build

echo "--- [3/4] lake env leanchecker (kernel replay trust gate) ---"
lake env leanchecker

echo "--- [4/4] forbidden-token scan (no sorry/admit/axiom/native_decide) ---"
if rg -n --glob '*.lean' --glob '!.lake/**' \
     '(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|$)' .; then
  echo "FAIL: forbidden token found"
  exit 1
fi

echo "=== VERIFY PASSED @ ${HEAD_SHA} ==="
