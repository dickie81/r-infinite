#!/usr/bin/env bash
# Compile the pilot. T1ca → Osc → Split import each other; Zeta imports T1bt, Split and Exterior, and
# Roadmap imports T1bt and Exterior, Limit imports Roadmap, HadamardApply imports Hadamard and Limit, XiBounds imports HadamardApply, Curvature imports XiBounds, GroundState imports Curvature, Existence imports GroundState, Compactness imports Existence, GroundStateExists imports Compactness, Uniqueness imports GroundStateExists, Positivity imports Uniqueness,
# through the oleans written to build/.
set -euo pipefail
# MATHLIB: a built Mathlib checkout at the commit in MATHLIB_REV (default ./mathlib4).
HERE="$(cd "$(dirname "$0")" && pwd)"
cd "${MATHLIB:-$HERE/mathlib4}"
export PATH="$HOME/.elan/bin:$PATH"
mkdir -p $HERE/build
run() { echo "== $1"; }
run T1bt;     lake env lean -R $HERE/src -o $HERE/build/T1bt.olean -i $HERE/build/T1bt.ilean $HERE/src/T1bt.lean
run T1ca;     lake env lean -R $HERE/src -o $HERE/build/T1ca.olean -i $HERE/build/T1ca.ilean $HERE/src/T1ca.lean
run Osc;      HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Osc.olean -i $HERE/build/Osc.ilean $HERE/src/Osc.lean'
run Split;    HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Split.olean -i $HERE/build/Split.ilean $HERE/src/Split.lean'
run Exterior; lake env lean -R $HERE/src -o $HERE/build/Exterior.olean -i $HERE/build/Exterior.ilean $HERE/src/Exterior.lean
run Zeta;     HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/Zeta.lean'
run Roadmap;  HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Roadmap.olean -i $HERE/build/Roadmap.ilean $HERE/src/Roadmap.lean'
run Limit;    HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Limit.olean -i $HERE/build/Limit.ilean $HERE/src/Limit.lean'
run Hadamard; lake env lean -R $HERE/src -o $HERE/build/Hadamard.olean -i $HERE/build/Hadamard.ilean $HERE/src/Hadamard.lean
run HadamardApply; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/HadamardApply.olean -i $HERE/build/HadamardApply.ilean $HERE/src/HadamardApply.lean'
run XiBounds; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/XiBounds.olean -i $HERE/build/XiBounds.ilean $HERE/src/XiBounds.lean'
run Curvature; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Curvature.olean -i $HERE/build/Curvature.ilean $HERE/src/Curvature.lean'
run GroundState; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/GroundState.olean -i $HERE/build/GroundState.ilean $HERE/src/GroundState.lean'
run Existence; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Existence.olean -i $HERE/build/Existence.ilean $HERE/src/Existence.lean'
run Compactness; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Compactness.olean -i $HERE/build/Compactness.ilean $HERE/src/Compactness.lean'
run GroundStateExists; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/GroundStateExists.olean -i $HERE/build/GroundStateExists.ilean $HERE/src/GroundStateExists.lean'
run Uniqueness; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Uniqueness.olean -i $HERE/build/Uniqueness.ilean $HERE/src/Uniqueness.lean'
run Positivity; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/Positivity.lean'
