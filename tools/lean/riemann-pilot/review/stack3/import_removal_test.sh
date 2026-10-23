#!/usr/bin/env bash
# Stack review 3 (STRUCTURAL-REVIEW.md §9.4): compile each listed module with one import line deleted, in a scratch
# copy outside build/ (no olean is written). Usage: MATHLIB=<built Mathlib checkout> OUT=<scratch dir> ./import_removal_test.sh
set -euo pipefail
P="$(cd "$(dirname "$0")/../.." && pwd)"
OUT="${OUT:?set OUT to a scratch directory}"
mkdir -p "$OUT"
cd "${MATHLIB:?set MATHLIB to a built Mathlib checkout}"
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_PATH="$(lake env printenv LEAN_PATH):$P/build"
while read -r M I; do
  f=$(ls "$P/src/$M.lean" "$P/external/dh/$M.lean" "$P/external/pnt/$M.lean" "$P/external/zeta23/$M.lean" 2>/dev/null | head -1)
  out="$OUT/$M--$I.lean"
  sed "/^import $I\$/d" "$f" > "$out"
  if lean "$out" > "$out.log" 2>&1 && ! grep -q "error" "$out.log"; then r=OK; else r=FAIL; fi
  echo "$M -> $I: $r"
done <<'LIST'
KubotaBallOp HilbertResolvent
DHColumn StripConv
PrimeSide Concave
WeilRH ExteriorZeta
ZetaInputs Zeta
Polya Roadmap
CountCompare DensityAsym
EisensteinTransferPoisson EisensteinDescent
EisensteinTransferPoisson MellinUniform
ExpSum6 ExpSum5
ExpSum5 ExpSum4
DHExplicit WeilChiCriterion
EisensteinPrepared EisensteinSquarefreeRows
KaiserPlanch KaiserZeroWeight
LIST
