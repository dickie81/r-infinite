#!/usr/bin/env bash
# Compile the pilot. T1ca → Osc → Split import each other; Zeta imports T1bt, Split and Exterior, and
# Roadmap imports T1bt and Exterior, Limit imports Roadmap, RiemannKernel imports Roadmap, HadamardApply imports Hadamard and Limit, XiBounds imports HadamardApply and RiemannKernel, Curvature imports XiBounds, GroundState imports Curvature, Existence imports GroundState, Compactness imports Existence, GroundStateExists imports Compactness, Uniqueness imports GroundStateExists, Positivity imports Uniqueness, StrictPositivity imports Positivity, UniquenessQ imports StrictPositivity, FourierGap imports UniquenessQ, ParabolaGap imports FourierGap, Polya imports Roadmap, Concave imports Polya, PrimeSide imports Positivity and Concave, Saturation imports only Mathlib, Unconditional imports Concave and Saturation, ZeroSwap imports UniquenessQ, HurwitzCross imports PrimeSide and ZeroSwap, SwapRealize imports HurwitzCross, SimpleCover imports SwapRealize and ParabolaGap, SimpleStructure imports SimpleCover, GapCriterion imports SimpleStructure, Commute imports GapCriterion, DegenerateFlat imports Commute, StructureD imports DegenerateFlat, Mollify imports StructureD, TheoremC imports Mollify, GapBound imports TheoremC, CosTrunc imports GapBound, StripConv imports GapBound, KernelChain imports StripConv, ZeroCount imports StructureD, SixteenPi imports Curvature,
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
run RiemannKernel; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/RiemannKernel.olean -i $HERE/build/RiemannKernel.ilean $HERE/src/RiemannKernel.lean'
run Hadamard; lake env lean -R $HERE/src -o $HERE/build/Hadamard.olean -i $HERE/build/Hadamard.ilean $HERE/src/Hadamard.lean
run HadamardApply; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/HadamardApply.olean -i $HERE/build/HadamardApply.ilean $HERE/src/HadamardApply.lean'
run XiBounds; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/XiBounds.olean -i $HERE/build/XiBounds.ilean $HERE/src/XiBounds.lean'
run Curvature; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Curvature.olean -i $HERE/build/Curvature.ilean $HERE/src/Curvature.lean'
run GroundState; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/GroundState.olean -i $HERE/build/GroundState.ilean $HERE/src/GroundState.lean'
run Existence; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Existence.olean -i $HERE/build/Existence.ilean $HERE/src/Existence.lean'
run Compactness; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Compactness.olean -i $HERE/build/Compactness.ilean $HERE/src/Compactness.lean'
run GroundStateExists; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/GroundStateExists.olean -i $HERE/build/GroundStateExists.ilean $HERE/src/GroundStateExists.lean'
run Uniqueness; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Uniqueness.olean -i $HERE/build/Uniqueness.ilean $HERE/src/Uniqueness.lean'
run Positivity; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Positivity.olean -i $HERE/build/Positivity.ilean $HERE/src/Positivity.lean'
run StrictPositivity; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/StrictPositivity.olean -i $HERE/build/StrictPositivity.ilean $HERE/src/StrictPositivity.lean'
run UniquenessQ; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/UniquenessQ.olean -i $HERE/build/UniquenessQ.ilean $HERE/src/UniquenessQ.lean'
run FourierGap; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/FourierGap.olean -i $HERE/build/FourierGap.ilean $HERE/src/FourierGap.lean'
run ParabolaGap; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/ParabolaGap.olean -i $HERE/build/ParabolaGap.ilean $HERE/src/ParabolaGap.lean'
run Polya; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Polya.olean -i $HERE/build/Polya.ilean $HERE/src/Polya.lean'
run Concave; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Concave.olean -i $HERE/build/Concave.ilean $HERE/src/Concave.lean'
run PrimeSide; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/PrimeSide.olean -i $HERE/build/PrimeSide.ilean $HERE/src/PrimeSide.lean'
run Saturation; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Saturation.olean -i $HERE/build/Saturation.ilean $HERE/src/Saturation.lean'
run Unconditional; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/Unconditional.lean'
run ZeroSwap; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/ZeroSwap.olean -i $HERE/build/ZeroSwap.ilean $HERE/src/ZeroSwap.lean'
run HurwitzCross; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/HurwitzCross.olean -i $HERE/build/HurwitzCross.ilean $HERE/src/HurwitzCross.lean'
run SwapRealize; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/SwapRealize.olean -i $HERE/build/SwapRealize.ilean $HERE/src/SwapRealize.lean'
run SimpleCover; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/SimpleCover.olean -i $HERE/build/SimpleCover.ilean $HERE/src/SimpleCover.lean'
run SimpleStructure; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/SimpleStructure.olean -i $HERE/build/SimpleStructure.ilean $HERE/src/SimpleStructure.lean'
run GapCriterion; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/GapCriterion.olean -i $HERE/build/GapCriterion.ilean $HERE/src/GapCriterion.lean'
run Commute; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Commute.olean -i $HERE/build/Commute.ilean $HERE/src/Commute.lean'
run DegenerateFlat; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/DegenerateFlat.olean -i $HERE/build/DegenerateFlat.ilean $HERE/src/DegenerateFlat.lean'
run StructureD; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/StructureD.olean -i $HERE/build/StructureD.ilean $HERE/src/StructureD.lean'
run Mollify; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/Mollify.olean -i $HERE/build/Mollify.ilean $HERE/src/Mollify.lean'
run TheoremC; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/TheoremC.olean -i $HERE/build/TheoremC.ilean $HERE/src/TheoremC.lean'
run GapBound; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/GapBound.olean -i $HERE/build/GapBound.ilean $HERE/src/GapBound.lean'
run CosTrunc; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/CosTrunc.lean'
run StripConv; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean -R $HERE/src -o $HERE/build/StripConv.olean -i $HERE/build/StripConv.ilean $HERE/src/StripConv.lean'
run KernelChain; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/KernelChain.lean'
run ZeroCount; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/ZeroCount.lean'
run SixteenPi; HERE="$HERE" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$HERE/build" lean $HERE/src/SixteenPi.lean'
