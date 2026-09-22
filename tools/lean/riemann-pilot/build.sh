#!/usr/bin/env bash
# Compile the pilot. T1bt.lean and Exterior.lean are standalone; T1ca → Osc → Split import each other
# through the oleans written to build/.
set -euo pipefail
# MATHLIB: a built Mathlib checkout at the commit in MATHLIB_REV (default ./mathlib4).
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "${MATHLIB:-$HERE/mathlib4}"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p $HERE/build
run() { echo "== $1"; }
run T1bt;     lake env lean $HERE/src/T1bt.lean
run T1ca;     lake env lean -R $HERE/src -o $HERE/build/T1ca.olean -i $HERE/build/T1ca.ilean $HERE/src/T1ca.lean
run Osc;      HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Osc.olean -i $HERE/build/Osc.ilean $HERE/src/Osc.lean'
run Split;    HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/Split.lean'
run Exterior; lake env lean $HERE/src/Exterior.lean
