#!/usr/bin/env bash
# Stack review 3 (STRUCTURAL-REVIEW.md §9.7): compile a scratch copy of a module with `set_option maxHeartbeats`,
# `maxRecDepth` or `synthInstance` override lines deleted (no olean is written). With line numbers, only those lines are
# deleted; without, every override line of the file. Prints rc, seconds and the error lines of the copy.
# Usage: MATHLIB=<built Mathlib checkout> OUT=<scratch dir> ./override_test.sh <path/to/Module.lean> [line ...]
set -euo pipefail
P="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${OUT:?set OUT to a scratch directory}"
mkdir -p "$OUT"
f="$(cd "$(dirname "$1")" && pwd)/$(basename "$1")"; shift
b="$(basename "$f" .lean)"
if [ $# -gt 0 ]; then
  expr=""; for n in "$@"; do expr="$expr${n}d;"; done
  sed "$expr" "$f" > "$OUT/$b.lean"
else
  grep -v "^set_option \(maxHeartbeats\|maxRecDepth\|synthInstance\)" "$f" > "$OUT/$b.lean"
fi
cd "${MATHLIB:?set MATHLIB to a built Mathlib checkout}"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH="$(lake env printenv LEAN_PATH):$P/build"
start=$(date +%s); rc=0
lean "$OUT/$b.lean" > "$OUT/$b.log" 2>&1 || rc=$?
echo "$b: rc=$rc secs=$(( $(date +%s) - start ))"
grep -o "lean:[0-9]*:[0-9]*: error.*" "$OUT/$b.log" | head -20 || true
