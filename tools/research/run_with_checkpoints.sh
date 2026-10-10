#!/bin/bash
# Checkpoint wrapper (owner-commissioned, A340): run a long computation
# while committing + pushing tools/research/checkpoints/ every 10 min,
# so container restores lose at most one interval of compute. Usage:
#   run_with_checkpoints.sh <logfile> <cmd...>
set -u
LOG="$1"; shift
REPO="$(cd "$(dirname "$0")/../.." && pwd)"
( "$@" > "$LOG" 2>&1; echo "exit=$?" >> "$LOG" ) &
PID=$!
while kill -0 $PID 2>/dev/null; do
  sleep 600
  cd "$REPO"
  if ! git diff --quiet -- tools/research/checkpoints || \
     [ -n "$(git status --porcelain tools/research/checkpoints | grep -v .gitkeep)" ]; then
    git add tools/research/checkpoints
    git commit -q -m "compute checkpoint (auto, run_with_checkpoints)" || true
    git push -q origin HEAD || true
  fi
done
cd "$REPO"
git add tools/research/checkpoints
git commit -q -m "compute checkpoint (final, run_with_checkpoints)" || true
git push -q origin HEAD || true
echo "WRAPPER-COMPLETE"
