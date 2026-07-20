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

# Easley nodes run CentOS 7 / glibc 2.17, but the Lean 4.32 clang needs glibc
# 2.29. Run the whole toolchain inside a glibc-2.35 Ubuntu 22.04 container.
# Singularity auto-binds $HOME, so ~/.elan and the mathlib cache are visible.
SIF="${LEANCHECK_SIF:-$HOME/Apptainder_Ubuntu_22-04_Chenle02_nvim_texlive-full_nodejs_gh.sif}"
[[ -f "$SIF" ]] || { echo "container image not found: $SIF"; exit 66; }
module load singularity 2>/dev/null || true

# Whole verification contract runs in ONE container invocation on the compute
# node. `bash -c` (not -l) skips the host LMOD profile that errors in-container.
singularity exec "$SIF" bash -c '
  set -euo pipefail
  export PATH="$HOME/.elan/bin:$PATH"
  echo "container glibc: $(ldd --version | head -1)"

  echo "--- [1/4] lake exe cache get (mathlib cache restore) ---"
  lake exe cache get

  echo "--- [2/4] lake build (full package) ---"
  lake build

  echo "--- [3/4] lake env leanchecker (kernel replay trust gate) ---"
  lake env leanchecker

  echo "--- [4/4] forbidden-token scan (no sorry/admit/axiom/native_decide) ---"
  if rg -n --glob "*.lean" --glob "!.lake/**" \
       "(^|[^[:alnum:]_])(sorry|admit|axiom|native_decide)([^[:alnum:]_]|\$)" .; then
    echo "FAIL: forbidden token found"
    exit 1
  fi
'

echo "=== VERIFY PASSED @ ${HEAD_SHA} ==="
