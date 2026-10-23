#!/usr/bin/env bash
# Build the external layer (rungs 1–3 of the wander ladder, rounds 191–216) on the pilot's own toolchain.
# Usage: ./build.sh, after ../../build.sh. Set MATHLIB as for ../../build.sh. Optionally set PNT to a
# PrimeNumberTheoremAnd clone that contains commit 650d312; otherwise that one commit is fetched.
# The script takes the 19 PrimeNumberTheoremAnd (PNT+) files that the layer imports, at 650d312 (Lean v4.33.1),
# applies pnt_port.patch (the port to the pilot's Lean and Mathlib), and compiles Architect.lean (a no-op
# stand-in for the LeanArchitect blueprint package), those files and this directory's files into ../../build.
# A module is compiled only if its olean is missing or older than its source or than the olean in ../../build of a
# module it imports (one of the pilot's, PNT+'s or this directory's; Mathlib's oleans are not compared), so after
# an edit only that file and its dependents are rebuilt, one at a time; FORCE=1 compiles every module (round 618,
# the rule of ../../build.sh since round 217); the module list must be in dependency order, which the script checks
# (round 619). The final check, which prints the axioms of the final theorems, runs
# every time. The build fails if Lean reports a use of sorry in one of this directory's files that it compiles, or
# if such a file or the final check prints an axiom outside propext, Classical.choice and Quot.sound (round 327,
# the rule of ../../build.sh). The vendored PNT+ files are not checked: two lemmas of PNT+'s Wiener.lean are sorry,
# outside the dependency cone of every theorem here, and the final check gates the theorems built on PNT+.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PILOT="$(cd "$HERE/../.." && pwd)"
REV=650d31264be65f4cd6e70c45d8b25d86d482a761
UP="$HERE/upstream"
PNTFILES="Mathlib/Algebra/Notation/Support Mathlib/Analysis/Asymptotics/Asymptotics
  Mathlib/Analysis/SpecialFunctions/Log/Basic Auxiliary EulerMaclaurin Rectangle Tactic/AdditiveCombination
  ResidueCalcOnRectangles Sobolev Fourier SmoothExistence MellinCalculus ZetaBounds ZetaConj MediumPNT StrongPNT
  Defs Wiener Consequences"
if [ ! -f "$UP/.ported" ] || [ "$HERE/pnt_port.patch" -nt "$UP/.ported" ]; then
  rm -rf "$UP"; mkdir -p "$UP"
  if [ -n "${PNT:-}" ]; then G="$PNT"; else
    G="$UP/.src"; git init -q "$G"
    git -C "$G" fetch -q --depth 1 https://github.com/AlexKontorovich/PrimeNumberTheoremAnd "$REV"
  fi
  for f in $PNTFILES; do
    mkdir -p "$UP/PrimeNumberTheoremAnd/$(dirname "$f")"
    git -C "$G" show "$REV:PrimeNumberTheoremAnd/$f.lean" > "$UP/PrimeNumberTheoremAnd/$f.lean"
  done
  git -C "$G" show "$REV:LICENSE" > "$UP/LICENSE"
  (cd "$UP" && patch -s -p1 < "$HERE/pnt_port.patch")
  touch "$UP/.ported"
fi
cd "${MATHLIB:-$PILOT/mathlib4}"
export PATH="$HOME/.elan/bin:$PATH"
B="$PILOT/build"
LP="$(lake env printenv LEAN_PATH):$B"
STD='(propext|Classical\.choice|Quot\.sound)'
CLEAN="' depends on axioms: \[$STD(, $STD)*\]\$"
# dirty TEXT: the number of axiom lines in TEXT that name an axiom outside propext, Classical.choice, Quot.sound
dirty() {
  printf '%s\n' "$1" | grep -e "' depends on axioms: " | grep -vEc "$CLEAN" || true
}
# c GATE ROOT MODULE [lean options]: compile ROOT/MODULE.lean to B/MODULE.olean, unless FORCE is not 1 and that olean
# is newer than the source and than the olean in B of every module the source imports (an import with no olean in B
# is not compared). With GATE = 1, fail, removing that olean, if Lean reports a use of sorry in the file or it prints
# an axiom outside the three. NC counts the modules compiled, NUP those up to date. The list must be in dependency
# order: a module of PNT+ or of this directory that the source imports must have been listed before it, else the
# build fails (round 619; SEEN holds the modules listed so far).
NC=0; NUP=0; SEEN=""
c() {
  local gate=$1 root=$2 rel=${3//.//} out dep t0 stale; shift 3
  local src="$root/$rel.lean" olean="$B/$rel.olean"
  for dep in $(sed -nE 's/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+//p' "$src"); do
    if [ -f "$HERE/${dep//.//}.lean" ] || [ -f "$UP/${dep//.//}.lean" ]; then
      case " $SEEN " in *" $dep "*) ;; *) echo "build.sh: ${rel//\//.} imports $dep, listed after it" >&2; exit 1;; esac
    fi
  done
  SEEN="$SEEN ${rel//\//.}"
  if [ "${FORCE:-0}" != 1 ] && [ -f "$olean" ] && [ ! "$src" -nt "$olean" ]; then
    stale=0
    for dep in $(sed -nE 's/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+//p' "$src"); do
      dep="$B/${dep//.//}.olean"
      if [ -f "$dep" ] && [ "$dep" -nt "$olean" ]; then stale=1; break; fi
    done
    if [ "$stale" = 0 ]; then NUP=$((NUP + 1)); return 0; fi
  fi
  echo "== ${rel//\//.}"; mkdir -p "$B/$(dirname "$rel")"; t0=$SECONDS
  out="$(LEAN_PATH="$LP" lean "$@" -R "$root" -o "$olean" -i "$B/$rel.ilean" "$src" 2>&1)" \
    || { printf '%s\n' "$out"; rm -f "$olean" "$B/$rel.ilean"; exit 1; }
  [ -z "$out" ] || printf '%s\n' "$out"
  echo "-- ${rel//\//.}: $((SECONDS - t0))s"; NC=$((NC + 1))
  [ "$gate" = 1 ] || return 0
  # Lean's sorry warning is m!"declaration uses `{s}`"; match its fixed text, as ../../build.sh does
  if [[ "$out" == *'declaration uses `'* ]]; then
    rm -f "$B/$rel.olean" "$B/$rel.ilean"
    echo "axioms check FAILED: ${rel//\//.} uses sorry" >&2
    exit 1
  fi
  if [ "$(dirty "$out")" != 0 ]; then
    rm -f "$B/$rel.olean" "$B/$rel.ilean"
    echo "axioms check FAILED: ${rel//\//.} prints an axiom outside [propext, Classical.choice, Quot.sound]" >&2
    exit 1
  fi
}
c 1 "$HERE" Architect
# PNT+'s lakefile sets these two options for its own files.
for f in $PNTFILES; do c 0 "$UP" "PrimeNumberTheoremAnd.${f//\//.}" -DautoImplicit=false -DrelaxedAutoImplicit=false; done
for f in WanderLadderPNT Rung3 Landau LogDerivDisc KVBridge LandauKV LogDerivKV MediumPNTW PNTKV KaiserKV TwinKV ShortKV DetectEM KVSubsumes Domination HalfPlanePNT BohrKV HalfPlaneFinal PsiExponent HalfPlaneLindelof SmoothPerron MertensExponent HalfPlaneJoinsPNT DivisorExponent ChiPNT PNTProgressions ChiUniform Littlewood LeastNonresidue SquarefreeCount ExplicitSmooth ExplicitConstants QuadRing QuadSplit QuadKronecker QuadClassNumber Subconvexity InghamDetect InghamDensity LinnikChar LinnikDeduction LinnikHybrid LinnikDetect LinnikDensity LinnikHalf LinnikFE LinnikLindelof LinnikSubconvex MertensChi LinnikAFE LinnikFourth LinnikIngham LinnikPower LinnikOffDiag LinnikHuxley LinnikGammaRatio LinnikReflect LinnikWeighted LinnikDual LinnikBuckets LinnikLargeValues LinnikTwelveBins LinnikTwelveSizes LinnikTwelve LinnikMoment LinnikLines LinnikSplit LinnikS2 LinnikPoints SieveSmooth LinnikStep SieveLemma1 SieveWeight SieveTypeII SieveRoute SieveCertDefs SieveCert SieveCert229 SieveRough SieveSep SieveFamily SieveBrun SieveCount SieveRanges SieveLeaf SieveTree SieveDyadic SieveTypeIIU SieveRoughTuple SieveTypeIIR SieveDiff SieveStops1 SieveCmp SieveStops2 SieveProp6 SieveChain SieveDecomp SieveBuch SieveLeaves SieveQ SieveDrop SieveMain LinnikCGL LinnikIngham73 LinnikHuxStep SieveTypeIIGen SieveTypeII73 Linnik229 LinnikInghamC LinnikStairs SieveCurveGlue SieveTypeIIU232 SieveCert232 Linnik232 LinnikWeyl LinnikHuxStepY LinnikStairs7 SieveTypeIIU227 SieveCert227 Linnik227 SieveTypeIIU226 SieveGrid226 SieveCert226P1 SieveCert226P2 SieveCert226P3 SieveCert226P4 SieveCert226P5 SieveCert226 Linnik226 SieveHMBin SieveHMBins SieveHMWindow SieveTypeIIHM SieveTypeIIU230 SieveCert230 Linnik230 SieveTypeIIU226C Linnik226C SieveTypeIIU229 SieveGrid229U SieveCert229UP1 SieveCert229UP2 SieveCert229UP3 SieveCert229UP4 SieveCert229UP5 SieveCert229U Linnik229U; do c 1 "$HERE" $f; done
# Round 625: Linnik's exponent 9/4 under CGLDensity alone; its certificate in 1374 kernel parts in 167 files, one
# lean process each (their completed runs 57590 s of elapsed time in the round's job, the first alone, the others
# two at a time; README.md; round 632: it read "57590 s of process time in the round's job, which ran them two at a
# time", review of round 625, F4).
for f in SieveCertColsDefs SieveCertCols SieveTypeIIU225C SieveGrid225C; do c 1 "$HERE" $f; done
for i in $(seq 1 167); do c 1 "$HERE" SieveCert225CP$i; done
for f in SieveCert225C Linnik225C; do c 1 "$HERE" $f; done
# Round 631: Linnik's exponent 2285/1000 with no hypothesis; its certificate in 252 kernel parts in 28 files, one
# lean process each (their completed runs 7100 s of elapsed time in the round's job, the first and the last
# alone, the others two at a time; README.md).
for f in SieveTypeIIU2285 SieveGrid2285U; do c 1 "$HERE" $f; done
for i in $(seq 1 28); do c 1 "$HERE" SieveCert2285UP$i; done
for f in SieveCert2285U Linnik2285U; do c 1 "$HERE" $f; done
# Rounds 636–678: Chen–Gupta–Li's Proposition 3.1 as a hypothesis and the large-values counts it gives
# (LinnikCGLLV), the density step from it on [5/7, 16/21] (LinnikCGLStep), Linnik's exponents 9/4 and 226/100
# from it (LinnikCGLLinnik), (round 638) Proposition 3.1 from a bound on the cubic trace (LinnikCGLMat),
# (round 639) that bound from the paper's S₂ and S₃ (LinnikCGLS23), (round 640) the Mellin transform of w² and the
# Gram entries as vertical integrals (LinnikCGLMellin), (round 641) their reflection (LinnikCGLReflect),
# (round 642) the bounds of the reflected entries (LinnikCGLPair), (round 643) the off-diagonal mass of the Gram
# matrix (LinnikCGLFrob), (round 644) the hypothesis CGLS2 proved (LinnikCGLS2), and (round 645) the decay of the
# Fourier transform of w(u)²u^{it}, their Lemma 4.3 (1) (LinnikCGLFourier), (round 646) the Poisson expansion
# of the Gram entries in residue classes (LinnikCGLPoisson), (round 648) the paper's S₃ at one point per
# character (LinnikCGLTrace), (round 649) the Gram diagonal against its main term (LinnikCGLDiag), (round 650)
# the truncation in m (LinnikCGLTrunc), (round 651) a product of three ĥs as an integral over (v₁, v₂)
# (LinnikCGLProd), (round 652) their I′ as an integral over (v₁, v₂) (LinnikCGLRFact), (round 653) the
# Ramanujan sum's bound and the decay of J (LinnikCGLRam), (round 654) their Proposition 7.1 (LinnikCGLP71),
# (round 655) the support of J in v₂/v₁ and the cyclic symmetry of I′ (LinnikCGLSym), (round 656) their R̃ and
# the inner integral of Proposition 7.2 (LinnikCGLRt), (round 657) their Proposition 7.2 (LinnikCGLP72), and
# (round 658) their Lemma 9.1, the second moments of R and R̃ (LinnikCGLMom), (round 659) their Lemma 9.2, the
# fourth moments (LinnikCGLMom4), (round 660) the two Cauchy–Schwarz steps of their §11 (LinnikCGLCS), and
# (round 662) their J, their Proposition 8.1 displayed, and S₃,₃ and S₃,₄ in its form (LinnikCGLJ), and
# (round 663) their f_b = ψR̃(·, −b)² with ψ = 1 on [−3, 3]: smoothness, support, lower bound (LinnikCGLFb),
# and (round 664) the Fourier decay of the pieces ψ·K(· − u′) of f_b (LinnikCGLPhi), and (round 665) the decay
# of f̂_b in the form of their Proposition 8.1 (LinnikCGLDecay), and (round 666) S₃,₃, S₃,₄ and the block sums
# of Ĩ by their Proposition 8.1 and Lemmas 9.1 and 9.2 (LinnikCGLBlock), and (round 667) their (11.2), the blocks
# of their Proposition 7.2 summed (LinnikCGL112), and (round 668) local averages of finite exponential sums, toward
# their Lemmas 10.4 and 10.8 (LinnikCGLLoc), and (round 669) their Lemma 10.5, the energy by the third moment of R
# (LinnikCGLL105), and (round 670) their Theorem 10.1 displayed and their Lemma 10.6 (LinnikCGLT101), and
# (round 672) their Lemma 10.7, the fourth moment of R (LinnikCGLL107), and (round 673) separated points and
# the fractions of their Lemma 10.9 (LinnikCGLSep), and (round 674) their Lemma 10.9, the small-gcd terms
# (LinnikCGLL109), and (round 675) their Lemma 10.10, the large-gcd terms, before their case analysis
# (LinnikCGLL1010), and (round 676) their Lemma 10.10 with its case analysis, and Remark 10.3
# (LinnikCGLCase), and (round 677) their Lemmas 10.9 and 10.10 with their ⪅, and their Proposition 10.2
# (LinnikCGLEps), and (round 678) their Proposition 11.1, CGLS3 from CGLP81 and CGLT101, and Linnik's exponents
# 9/4 and 226/100 from those two (LinnikCGLS3), and (round 680) the majorant of their J, Plancherel and its Fourier
# transform (LinnikCGLG), and its Poisson expansion in residue classes (LinnikCGLPois8), and (round 681) their count
# of the pairs (m₁′, n′) (LinnikCGLCount), and the sum over a by the Ramanujan sum (LinnikCGLAsum), and (round 682)
# ĝ_a as a sum over m₁ and n with the sum over a for every n ≠ 0 (LinnikCGLNsum), and the term n = 0, their I
# (LinnikCGLN0), and (round 683) the terms n ≠ 0 over |ξ| ≤ X by their change of variables (LinnikCGLCov), and
# (round 684) their Σ_II expanded and their Σ₂ by Poisson summation (LinnikCGLSig2), and (round 685) their smoothing
# f̃_b and the inner integral of their Σ_II (LinnikCGLFtil), and (round 686) their Cauchy–Schwarz back to J(f̃⃗) for
# the terms |n| ≤ N₀ of their Σ_II (LinnikCGLJtil), and (round 687) the terms |n| > N₀ and the range |ξ| > X of ĝ_a by
# the decay premise (LinnikCGLTail), and (round 688) their Lemma 8.2 with explicit constants (LinnikCGLL82), and
# (round 689) the bounds of its constants that do not depend on the parameters (LinnikCGLConst).
for f in LinnikCGLLV LinnikCGLStep LinnikCGLLinnik LinnikCGLMat LinnikCGLS23 LinnikCGLMellin LinnikCGLReflect \
    LinnikCGLPair LinnikCGLFrob LinnikCGLS2 LinnikCGLFourier LinnikCGLPoisson LinnikCGLTrace \
    LinnikCGLDiag LinnikCGLTrunc LinnikCGLProd LinnikCGLRFact LinnikCGLRam LinnikCGLP71 LinnikCGLSym LinnikCGLRt \
    LinnikCGLP72 LinnikCGLMom LinnikCGLMom4 LinnikCGLCS LinnikCGLJ LinnikCGLFb LinnikCGLPhi LinnikCGLDecay \
    LinnikCGLBlock LinnikCGL112 LinnikCGLLoc LinnikCGLL105 LinnikCGLT101 LinnikCGLL107 LinnikCGLSep \
    LinnikCGLL109 LinnikCGLL1010 LinnikCGLCase LinnikCGLEps LinnikCGLS3 LinnikCGLG LinnikCGLPois8 \
    LinnikCGLCount LinnikCGLAsum LinnikCGLNsum LinnikCGLN0 LinnikCGLCov LinnikCGLSig2 LinnikCGLFtil \
    LinnikCGLJtil LinnikCGLTail LinnikCGLL82 LinnikCGLConst; do
  c 1 "$HERE" $f
done
echo "$NC compiled, $NUP up to date"
AX="$(mktemp --suffix=.lean)"
trap 'rm -f "$AX"' EXIT
cat > "$AX" <<'EOT'
import WanderLadderPNT
import Rung3
import PNTKV
import KaiserKV
import TwinKV
import DetectEM
import KVSubsumes
import Domination
import LogDerivDisc
import HalfPlanePNT
import BohrKV
import HalfPlaneFinal
import PsiExponent
import HalfPlaneLindelof
import SmoothPerron
import MertensExponent
import HalfPlaneJoinsPNT
import DivisorExponent
import ChiPNT
import PNTProgressions
import ChiUniform
import Littlewood
import LeastNonresidue
import SquarefreeCount
import ExplicitSmooth
import ExplicitConstants
import QuadRing
import QuadSplit
import QuadKronecker
import QuadClassNumber
import Subconvexity
import InghamDetect
import InghamDensity
import LinnikChar
import LinnikDeduction
import LinnikHybrid
import LinnikDetect
import LinnikDensity
import LinnikHalf
import LinnikFE
import LinnikLindelof
import LinnikSubconvex
import MertensChi
import LinnikAFE
import LinnikFourth
import LinnikIngham
import LinnikPower
import LinnikOffDiag
import LinnikHuxley
import LinnikGammaRatio
import LinnikReflect
import LinnikWeighted
import LinnikDual
import LinnikBuckets
import LinnikLargeValues
import LinnikTwelveBins
import LinnikTwelveSizes
import LinnikTwelve
import LinnikMoment
import LinnikLines
import LinnikSplit
import LinnikS2
import LinnikPoints
import SieveSmooth
import LinnikStep
import SieveLemma1
import SieveWeight
import SieveTypeII
import SieveRoute
import SieveCert
import SieveCert229
import SieveRough
import SieveSep
import SieveFamily
import SieveBrun
import SieveCount
import SieveRanges
import SieveLeaf
import SieveTree
import SieveDyadic
import SieveTypeIIU
import SieveRoughTuple
import SieveTypeIIR
import SieveDiff
import SieveStops1
import SieveCmp
import SieveStops2
import SieveProp6
import SieveChain
import SieveDecomp
import SieveBuch
import SieveLeaves
import SieveQ
import SieveDrop
import SieveMain
import LinnikCGL
import LinnikIngham73
import LinnikHuxStep
import SieveTypeIIGen
import SieveTypeII73
import Linnik229
import LinnikInghamC
import LinnikStairs
import SieveCurveGlue
import SieveTypeIIU232
import SieveCert232
import Linnik232
import LinnikWeyl
import LinnikHuxStepY
import LinnikStairs7
import SieveTypeIIU227
import SieveCert227
import Linnik227
import SieveTypeIIU226
import SieveGrid226
import SieveCert226P1
import SieveCert226P2
import SieveCert226P3
import SieveCert226P4
import SieveCert226P5
import SieveCert226
import Linnik226
import SieveHMBin
import SieveHMBins
import SieveHMWindow
import SieveTypeIIHM
import SieveTypeIIU230
import SieveCert230
import Linnik230
import SieveTypeIIU226C
import Linnik226C
import SieveTypeIIU229
import SieveGrid229U
import SieveCert229UP1
import SieveCert229UP2
import SieveCert229UP3
import SieveCert229UP4
import SieveCert229UP5
import SieveCert229U
import Linnik229U
import SieveCertCols
import SieveTypeIIU225C
import SieveGrid225C
import SieveCert225C
import Linnik225C
import SieveTypeIIU2285
import SieveGrid2285U
import SieveCert2285U
import Linnik2285U
import LinnikCGLLV
import LinnikCGLStep
import LinnikCGLLinnik
import LinnikCGLMat
import LinnikCGLS23
import LinnikCGLMellin
import LinnikCGLReflect
import LinnikCGLPair
import LinnikCGLFrob
import LinnikCGLS2
import LinnikCGLFourier
import LinnikCGLPoisson
import LinnikCGLTrace
import LinnikCGLDiag
import LinnikCGLTrunc
import LinnikCGLProd
import LinnikCGLRFact
import LinnikCGLRam
import LinnikCGLP71
import LinnikCGLSym
import LinnikCGLRt
import LinnikCGLP72
import LinnikCGLMom
import LinnikCGLMom4
import LinnikCGLCS
import LinnikCGLJ
import LinnikCGLFb
import LinnikCGLPhi
import LinnikCGLDecay
import LinnikCGLBlock
import LinnikCGL112
import LinnikCGLLoc
import LinnikCGLL105
import LinnikCGLT101
import LinnikCGLL107
import LinnikCGLSep
import LinnikCGLL109
import LinnikCGLL1010
import LinnikCGLCase
import LinnikCGLEps
import LinnikCGLS3
import LinnikCGLG
import LinnikCGLPois8
import LinnikCGLCount
import LinnikCGLAsum
import LinnikCGLNsum
import LinnikCGLN0
import LinnikCGLCov
import LinnikCGLSig2
import LinnikCGLFtil
import LinnikCGLJtil
import LinnikCGLTail
import LinnikCGLL82
import LinnikCGLConst
#print axioms Landau.zeroFree_of_growth
#print axioms Landau.logDerivBnd_of_growth
#print axioms Landau.rung3_of_growth
#print axioms KVBridge.polylogGrowth_kv
#print axioms KVBridge.polylogGrowth_sharp
#print axioms KVBridge.zeroFree_kv
#print axioms KVBridge.rung3_kv
#print axioms LandauKV.zeroFree_KV
#print axioms LogDerivKV.logDerivBnd_KV
#print axioms MediumPNTW.GenPNTW
#print axioms MediumPNTW.GenPNTW'
#print axioms MediumPNTW.GenPNTWNoEps
#print axioms PNTKV.PNT_KV
#print axioms KaiserKV.lam_prefactor_KV
#print axioms TwinLandau.Q_ge_of_rates
#print axioms TwinKV.twins_lower_KV
#print axioms TwinKV.twins_lower_KV'
#print axioms TwinKV.twins_lower_cut
#print axioms TwinKV.twins_lower_KV_sharp
#print axioms KVSubsumes.kvInput_of_KV
#print axioms Domination.lam_prefactor_KV'
#print axioms ShortKV.zeroFreeXi_KV
#print axioms DetectEM.density_unconditional
#print axioms DetectEM.short_primes
#print axioms HalfPlanePNT.logDeriv_le_of_zeroFree
#print axioms HalfPlanePNT.psi_isBigO_of_zeroFree
#print axioms HalfPlanePNT.psi_isBigO_of_smoothBound
#print axioms HalfPlanePNT.psi_isBigO_of_completed
#print axioms BohrKV.shell_of_KV
#print axioms HalfPlanePNT.psi_isBigO_eleven_twelfths
#print axioms PsiExponent.Theta_le
#print axioms PsiExponent.half_le_Theta
#print axioms PsiExponent.zeta_ne_zero_of_Theta_lt
#print axioms PsiExponent.psi_isBigO_Theta
#print axioms PsiExponent.psi_omega_Theta
#print axioms PsiExponent.limsup_expo
#print axioms HalfPlaneLindelof.norm_le_interp
#print axioms HalfPlaneLindelof.hasDerivAt_log_norm
#print axioms HalfPlaneLindelof.logDeriv_le_interp
#print axioms HalfPlaneLindelof.zeta_bound_of_zeroFree
#print axioms HalfPlaneLindelof.zeta_bound_eleven_twelfths
#print axioms HalfPlaneLindelof.zeta_bound_Theta
#print axioms SmoothPerron.verticalIntegral_eq_smoothedSum
#print axioms SmoothPerron.verticalIntegral_shift
#print axioms SmoothPerron.mellin_le_geom
#print axioms SmoothPerron.norm_smoothedSum_sub_le
#print axioms SmoothPerron.verticalIntegral_integrand_shift
#print axioms SmoothPerron.smoothedSum_eq_verticalIntegral_left
#print axioms MertensExponent.mertens_isBigO_of_zeroFree
#print axioms MertensExponent.mertens_isBigO_eleven_twelfths
#print axioms MertensExponent.mertens_isBigO_Theta
#print axioms MertensExponent.mertens_omega_Theta
#print axioms MertensExponent.rh_iff_Theta_eq_half
#print axioms MertensExponent.rh_iff_mertens
#print axioms MertensExponent.limsup_mexpo
#print axioms MertensExponent.moebius_tendsto_of_Theta_lt
#print axioms MertensExponent.moebius_not_tendsto_of_lt_Theta
#print axioms MertensExponent.moebiusAbscissa_eq_Theta
#print axioms HalfPlaneJoinsPNT.weil_twins_rate_Theta
#print axioms HalfPlaneJoinsPNT.psiOmegaSqrt_of_not_RH
#print axioms HalfPlaneJoinsPNT.zeroFree_KV_explicit
#print axioms DivisorExponent.integral_pow_mul_cexp
#print axioms DivisorExponent.inv_sub_one_pow_eq_integral
#print axioms DivisorExponent.LSeries_dk
#print axioms DivisorExponent.zeta_pow_eq
#print axioms DivisorExponent.verticalIntegral_inv_sub_one_pow
#print axioms DivisorExponent.smoothedSum_dk_eq
#print axioms DivisorExponent.norm_remainder_le
#print axioms DivisorExponent.coeff_Pk
#print axioms DivisorExponent.natDegree_Pk_eq
#print axioms DivisorExponent.divisor_isBigO_of_zeroFree
#print axioms DivisorExponent.divisor_isBigO_eleven_twelfths
#print axioms DivisorExponent.divisor_isBigO_Theta
#print axioms LogDerivDisc.disc_point
#print axioms ChiPNT.logDeriv_le_of_zeroFree
#print axioms ChiPNT.sum_isBigO_of_zeroFree
#print axioms ChiPNT.psiChi_isBigO_of_zeroFree
#print axioms ChiPNT.psiChi_isBigO_eleven_twelfths
#print axioms PNTProgressions.sum_dvd_le_log
#print axioms PNTProgressions.sum_not_coprime_le
#print axioms PNTProgressions.psiChi_one
#print axioms PNTProgressions.psiAP_eq_sum
#print axioms PNTProgressions.psiAP_isBigO
#print axioms LogDerivDisc.logDeriv_le_uniform
#print axioms ChiPNT.sum_le_uniform
#print axioms ChiUniform.psiChi_le_uniform
#print axioms Littlewood.norm_LSeries_le_of_sum_le
#print axioms Littlewood.logDeriv_le_loglog
#print axioms Littlewood.norm_LFunction_le_real
#print axioms Littlewood.abs_log_norm_LFunction_one_le
#print axioms Littlewood.norm_LFunction_one_le
#print axioms Littlewood.norm_LFunction_one_ge
#print axioms Littlewood.norm_logDeriv_one_le
#print axioms LeastNonresidue.re_psiChi_ge
#print axioms LeastNonresidue.rpow_le_of_forall_eq
#print axioms LeastNonresidue.exists_prime_eq
#print axioms LeastNonresidue.exists_prime_ne_one
#print axioms LeastNonresidue.exists_nonsquare_le
#print axioms LeastNonresidue.exists_nonsquare_le_rpow
#print axioms SquarefreeCount.sum_sqf_eq
#print axioms SquarefreeCount.hasSum_moebius_div_sq
#print axioms SquarefreeCount.abs_sub_sum_le
#print axioms SquarefreeCount.abs_sum_sqf_sub_le
#print axioms SquarefreeCount.squarefree_isBigO_of_zeroFree
#print axioms SquarefreeCount.squarefree_isBigO_twelve_25ths
#print axioms SquarefreeCount.squarefree_isBigO_Theta
#print axioms SmoothPerron.mellin_le_geom_of
#print axioms ExplicitSmooth.contDiff_ν₀
#print axioms ExplicitSmooth.mass_ν₀
#print axioms ExplicitSmooth.mellin_ν₀_le_geom
#print axioms LogDerivDisc.logDeriv_le_uniform_of
#print axioms ChiPNT.sum_le_uniform_of
#print axioms ChiUniform.psiChi_le_uniform_of
#print axioms Littlewood.logDeriv_le_loglog_of
#print axioms Littlewood.abs_log_norm_LFunction_one_le_of
#print axioms LeastNonresidue.exists_nonsquare_le_of
#print axioms LeastNonresidue.exists_nonsquare_le_rpow_of
#print axioms ExplicitConstants.psiChi_le_explicit
#print axioms ExplicitConstants.logDeriv_le_explicit
#print axioms ExplicitConstants.norm_LFunction_one_le_explicit
#print axioms ExplicitConstants.norm_LFunction_one_ge_explicit
#print axioms ExplicitConstants.norm_logDeriv_one_le_explicit
#print axioms ExplicitConstants.exists_prime_eq_explicit
#print axioms ExplicitConstants.exists_prime_eq_13
#print axioms ExplicitConstants.exists_nonsquare_le_explicit
#print axioms ExplicitConstants.exists_nonsquare_le_13
#print axioms ExplicitConstants.exists_nonsquare_le_rpow_explicit
#print axioms QuadRing.int_of_mul_sq
#print axioms QuadRing.exists_eq
#print axioms QuadRing.minpoly_eq
#print axioms QuadRing.isIntegral_iff
#print axioms QuadRing.discr_eq_of_basis
#print axioms QuadRing.span_θ₁
#print axioms QuadRing.adjoin_θ₁
#print axioms QuadRing.discr_θ₁
#print axioms QuadRing.minpoly_θ₁
#print axioms QuadRing.span_θ₂
#print axioms QuadRing.adjoin_θ₂
#print axioms QuadRing.discr_θ₂
#print axioms QuadRing.minpoly_θ₂
#print axioms QuadRing.exists_sqrt
#print axioms QuadSplit.split_of_factors
#print axioms QuadSplit.ramified_of_factors
#print axioms QuadSplit.inert_of_factors
#print axioms QuadSplit.split_of_root
#print axioms QuadSplit.ramified_of_root
#print axioms QuadSplit.inert_of_no_root
#print axioms QuadSplit.ramified_of_dvd₂
#print axioms QuadSplit.ramified_two₂
#print axioms QuadSplit.split₂
#print axioms QuadSplit.inert₂
#print axioms QuadSplit.ramified_of_dvd₁
#print axioms QuadSplit.split₁
#print axioms QuadSplit.inert₁
#print axioms QuadSplit.split_two₁
#print axioms QuadSplit.inert_two₁
#print axioms QuadKronecker.jacBot_natCast
#print axioms QuadKronecker.jacTop_natCast
#print axioms QuadKronecker.jacobiSym_natAbs
#print axioms QuadKronecker.jacobiSym_two_natAbs
#print axioms QuadKronecker.type_one
#print axioms QuadKronecker.type_two_three
#print axioms QuadKronecker.dedekindZeta_eq
#print axioms QuadKronecker.ne_one_of_eq
#print axioms QuadKronecker.exists_kronecker
#print axioms QuadKronecker.classNumber_formula
#print axioms QuadClassNumber.classNumber_ge
#print axioms QuadClassNumber.classNumber_le
#print axioms QuadClassNumber.classNumber_ge_sqrt
#print axioms QuadClassNumber.regulator_mul_classNumber_ge
#print axioms QuadClassNumber.regulator_mul_classNumber_le
#print axioms QuadClassNumber.regulator_mul_classNumber_ge_sqrt
#print axioms QuadClassNumber.classNumber_ge_loglog
#print axioms QuadClassNumber.regulator_mul_classNumber_ge_loglog
#print axioms QuadClassNumber.exists_inert_le
#print axioms QuadClassNumber.exists_split_le
#print axioms QuadClassNumber.exists_inert_le_13
#print axioms QuadClassNumber.exists_split_le_13
#print axioms QuadClassNumber.eulerKronecker
#print axioms Subconvexity.zeta_strip_of_zeroFree
#print axioms Subconvexity.zeta_strip_eleven_twelfths
#print axioms Subconvexity.zetaCritBound_of_zeroFree
#print axioms Subconvexity.zetaCritBound_five_24
#print axioms Subconvexity.convexityBound
#print axioms Subconvexity.zetaCritBound_Theta
#print axioms Subconvexity.lindelof_of_RH
#print axioms InghamDensity.detect_identity
#print axioms InghamDensity.trichotomy
#print axioms InghamDensity.densityXi_of_zetaCrit
#print axioms InghamDensity.inghamFromC
#print axioms InghamDensity.densityXi_17_6
#print axioms InghamDensity.densityXi_Theta
#print axioms InghamDensity.densityHypothesis_of_lindelof
#print axioms InghamDensity.short_primes_11_17
#print axioms InghamDensity.short_primes_Theta
#print axioms LogDerivDisc.disc_point_ball
#print axioms LogDerivDisc.logDeriv_le_ball
#print axioms InghamDensity.norm_Gamma_exp_le
#print axioms ChiUniform.LFunction_ctr_inv_le
#print axioms ChiUniform.logDeriv_LFunction_right
#print axioms Linnik.perron_exp
#print axioms Linnik.logDeriv_LFunction_le
#print axioms Linnik.norm_Sx_le
#print axioms Linnik.totient_mul_SAP
#print axioms Linnik.re_Sx_one_ge
#print axioms Linnik.SAP_le_of_noPrime
#print axioms Linnik.error_le
#print axioms Linnik.total_le
#print axioms Linnik.prime_in_class
#print axioms Linnik.linnik_of_charDensity
#print axioms Linnik.charDensity_twelve
#print axioms Linnik.linnik_twelve
#print axioms LinnikHybrid.mean_value_row
#print axioms LinnikHybrid.sum_chars_norm_sq_le
#print axioms LinnikHybrid.mean_value_chars
#print axioms LinnikHybrid.large_values_chars
#print axioms LinnikHybrid.large_values_chars_off
#print axioms LinnikPoints.large_values_points
#print axioms LinnikPoints.large_values_chars_of_points
#print axioms SieveSmooth.indicator_sub_G
#print axioms SieveSmooth.pow_mul_norm_fourier_GC_le
#print axioms SieveSmooth.integrable_fourier_GC
#print axioms SieveSmooth.GC_sub_eq_integral
#print axioms LinnikStep.class1_step
#print axioms LinnikStep.count_step
#print axioms LinnikStep.charDensity_step
#print axioms SieveLemma1.perron_weight
#print axioms SieveLemma1.norm_Sw_le
#print axioms SieveWeight.exists_mellin_bound
#print axioms SieveWeight.norm_Sw_wy_le
#print axioms SieveWeight.norm_Sp_le
#print axioms SieveTypeII.sum_chars_dp_sq_le
#print axioms SieveTypeII.typeII_pointwise
#print axioms SieveTypeII.exponent_le
#print axioms SieveTypeII.typeII_step
#print axioms SieveRoute.routeOK2333
#print axioms SieveRoute.typeII2333
#print axioms SieveCert.gridOK2333
#print axioms SieveCert.total_le_2333
#print axioms SieveCert.total_div_le
#print axioms SieveCert.cover2
#print axioms SieveCert.cover3
#print axioms SieveCert.cover4
#print axioms SieveCert.omegaC_le
#print axioms SieveRough.psi_le
#print axioms SieveRough.share2
#print axioms SieveRough.share4
#print axioms SieveRough.share2_of_cand
#print axioms SieveRough.share4_of_counted4
#print axioms SieveSep.sum_sep
#print axioms SieveSep.sep_bound
#print axioms SieveFamily.family_bound
#print axioms SieveFamily.Dsum_sharp_le
#print axioms SieveFamily.typeII_sharp_explicit
#print axioms SieveFamily.typeII_sharp
#print axioms SieveBrun.bonferroni
#print axioms SieveBrun.fundamental
#print axioms SieveBrun.gap_le
#print axioms SieveCount.card_A
#print axioms SieveCount.card_B
#print axioms SieveRanges.rng_sum_le
#print axioms SieveLeaf.leaf_A
#print axioms SieveLeaf.leaf_B
#print axioms SieveLeaf.leaf_gap
#print axioms SieveTree.tree_sum
#print axioms SieveDyadic.sum_bump
#print axioms SieveTypeIIU.typeII_unw
#print axioms SieveRoughTuple.sum_rough_eq
#print axioms SieveTypeIIR.typeII_rough
#print axioms SieveDiff.leaf_diff
#print axioms SieveStops1.stops1_bound
#print axioms SieveStops1.window_bound
#print axioms SieveStops2.typeII_cmp
#print axioms SieveStops2.stops2_bound
#print axioms SieveProp6.prop6
#print axioms SieveChain.typeII_gcmp'
#print axioms SieveChain.chainTU_bound
#print axioms SieveChain.chainTL_bound
#print axioms SieveDecomp.buchstab_fam
#print axioms SieveDecomp.famI_cells
#print axioms SieveDecomp.famI_vanish
#print axioms SieveBuch.Par.decomp
#print axioms SieveLeaves.TL_spec
#print axioms SieveLeaves.TU_spec
#print axioms SieveLeaves.P6_spec
#print axioms SieveQ.good_of_large
#print axioms SieveQ.leaves_ev
#print axioms SieveDrop.drop_ev
#print axioms SieveMain.TB_ev
#print axioms SieveMain.linnik_large
#print axioms SieveMain.linnik_route
#print axioms SieveMain.linnik_route_lt
#print axioms SieveMain.fits2333
#print axioms SieveMain.linnik_2333
#print axioms LinnikIngham73.bound_class2_73
#print axioms LinnikIngham73.count_middle73
#print axioms LinnikIngham73.charDensity_ingham73
#print axioms LinnikHuxStep.class1_gen
#print axioms LinnikHuxStep.count_gen
#print axioms LinnikHuxStep.charDensity_gen
#print axioms LinnikHuxStep.charDensity_hux73
#print axioms LinnikHuxStep.charDensity_step'
#print axioms SieveTypeIIGen.card_bin_gen
#print axioms SieveTypeIIGen.bin_bound_gen
#print axioms SieveTypeIIGen.prod_MB_le_gen
#print axioms SieveTypeIIGen.typeII_gen
#print axioms SieveTypeII73.counts_73
#print axioms SieveTypeII73.window_73
#print axioms SieveTypeII73.typeII_73
#print axioms SieveCert.gridOK229
#print axioms SieveCert.total_le_229
#print axioms Linnik229.routeOK229
#print axioms Linnik229.typeII229
#print axioms Linnik229.fits229
#print axioms Linnik229.linnik_229
#print axioms LinnikInghamC.charDensity_ingham_c
#print axioms LinnikStairs.charDensity_in0
#print axioms LinnikStairs.charDensity_hx0
#print axioms LinnikStairs.charDensity_hx9
#print axioms SieveTypeIIU232.counts_U
#print axioms SieveTypeIIU232.window_U
#print axioms SieveTypeIIU232.typeII_232
#print axioms SieveCert.gridOK232
#print axioms SieveCert.total_eq_rows
#print axioms SieveCert.total_le_232
#print axioms Linnik232.routeOK232
#print axioms Linnik232.typeII232
#print axioms Linnik232.fits232
#print axioms Linnik232.linnik_232
#print axioms LinnikWeyl.class2_empty
#print axioms LinnikWeyl.class2_finset_empty
#print axioms LinnikWeyl.class2_card_eq_zero
#print axioms LinnikHuxStepY.charDensity_genY
#print axioms LinnikHuxStepY.parY_example_good
#print axioms LinnikHuxStepY.parY_example'_good
#print axioms LinnikStairs7.charDensity_in7_0
#print axioms LinnikStairs7.charDensity_hx7_0
#print axioms LinnikStairs7.charDensity_hy_0
#print axioms LinnikStairs7.charDensity_hy_top
#print axioms SieveTypeIIU227.counts_7
#print axioms SieveTypeIIU227.window_7
#print axioms SieveTypeIIU227.typeII_227
#print axioms SieveCert.gridOK227
#print axioms SieveCert.total_le_227
#print axioms Linnik227.routeOK227
#print axioms Linnik227.typeII227
#print axioms Linnik227.fits227
#print axioms Linnik227.linnik_227
#print axioms SieveTypeIIU226.window_6
#print axioms SieveTypeIIU226.typeII_226
#print axioms SieveCert.gridOK226
#print axioms SieveCert.total_eq_rows226
#print axioms SieveCert.total_le_226
#print axioms Linnik226.routeOK226
#print axioms Linnik226.typeII226
#print axioms Linnik226.fits226
#print axioms Linnik226.linnik_226
#print axioms SieveTypeIIHM.dp_eq_pv
#print axioms SieveTypeIIHM.sum_bin_hm
#print axioms SieveTypeIIHM.sum_typeII_bins_hm
#print axioms SieveTypeIIHM.offK_bound
#print axioms SieveCurveGlue.affine_corner_bound
#print axioms SieveCurveGlue.windowPieceHM_affine
#print axioms SieveCurveGlue.windowPieceHM_affine_split
#print axioms SieveCurveGlue.windowPieceHM_const_split
#print axioms SieveTypeIIHM.bin_bound_pt
#print axioms SieveTypeIIHM.bin_bound_gen_hm
#print axioms SieveTypeIIHM.typeII_gen_hm
#print axioms SieveTypeIIU230.window_230
#print axioms SieveTypeIIU230.typeII_230
#print axioms SieveCert.gridOK230
#print axioms SieveCert.total_le_230
#print axioms Linnik230.routeOK230
#print axioms Linnik230.typeII230
#print axioms Linnik230.fits230
#print axioms Linnik230.linnik_230
#print axioms SieveTypeIIU226C.counts_7c
#print axioms SieveTypeIIU226C.window_226c
#print axioms SieveTypeIIU226C.typeII_226c
#print axioms Linnik226C.typeII226c
#print axioms Linnik226C.linnik_226c
#print axioms SieveTypeIIU229.window_229
#print axioms SieveTypeIIU229.typeII_229
#print axioms SieveCert.gridOK229U
#print axioms SieveCert.total_eq_rows229U
#print axioms SieveCert.total_lt_229U
#print axioms Linnik229U.routeOK229U
#print axioms Linnik229U.typeII229U
#print axioms Linnik229U.fits229U
#print axioms Linnik229U.linnik_229U
#print axioms SieveCert.rowsJ_eq
#print axioms SieveCert.rows_eq_rowsJ
#print axioms SieveCert.rowsJ_split
#print axioms SieveCert.rows_split
#print axioms SieveCert.total_eq_rows_full
#print axioms SieveCert.rows_le_of_split
#print axioms SieveCert.rowsJ_le_of_split
#print axioms SieveCert.rows_le_of_rowsJ
#print axioms SieveTypeIIU225C.window_225c
#print axioms SieveTypeIIU225C.typeII_225c
#print axioms SieveCert.gridOK225C
#print axioms SieveCert.total_lt_225C
#print axioms Linnik225C.routeOK225C
#print axioms Linnik225C.typeII225c
#print axioms Linnik225C.fits225C
#print axioms Linnik225C.linnik_225c
#print axioms SieveTypeIIU2285.window_2285
#print axioms SieveTypeIIU2285.typeII_2285
#print axioms SieveCert.gridOK2285U
#print axioms SieveCert.total_lt_2285U
#print axioms Linnik2285U.routeOK2285U
#print axioms Linnik2285U.typeII2285U
#print axioms Linnik2285U.fits2285U
#print axioms Linnik2285U.linnik_2285U
#print axioms LinnikCGLLV.lv_range
#print axioms LinnikCGLLV.cgl_all
#print axioms LinnikCGLLV.taylor_pick
#print axioms LinnikCGLLV.cgl_shift
#print axioms LinnikCGLStep.block_bin_cgl
#print axioms LinnikCGLStep.class1_cgl
#print axioms LinnikCGLStep.count_cgl
#print axioms LinnikCGLStep.charDensity_cgl
#print axioms LinnikCGLLinnik.counts_7c_lv
#print axioms LinnikCGLLinnik.linnik_225c_lv
#print axioms LinnikCGLLinnik.linnik_226c_lv
#print axioms LinnikCGLMat.refined_moment_points
#print axioms LinnikCGLMat.prop46
#print axioms LinnikCGLMat.mvt_case
#print axioms LinnikCGLMat.alg112
#print axioms LinnikCGLMat.prop31_of_third
#print axioms LinnikCGLMat.linnik_225c_third
#print axioms LinnikCGLMat.linnik_226c_third
#print axioms LinnikCGLS23.X3_eq
#print axioms LinnikCGLS23.third_of_s23
#print axioms LinnikCGLS23.linnik_225c_s23
#print axioms LinnikCGLS23.linnik_226c_s23
#print axioms LinnikCGLMellin.exists_H_bound
#print axioms LinnikCGLMellin.differentiable_H
#print axioms LinnikCGLMellin.perron_Wt
#print axioms LinnikCGLMellin.perron_gram
#print axioms LinnikCGLReflect.norm_Phi_le_far
#print axioms LinnikCGLReflect.LFunction_reflected
#print axioms LinnikCGLReflect.shift_of_bound
#print axioms LinnikCGLReflect.reflect_gram
#print axioms LinnikCGLReflect.gram_reflect
#print axioms LinnikCGLPair.norm_Eu_mul_le
#print axioms LinnikCGLPair.norm_dualT_le
#print axioms LinnikCGLPair.norm_integral_Mn_le
#print axioms LinnikCGLPair.norm_integral_Tl_le
#print axioms LinnikCGLPair.norm_gram_le
#print axioms LinnikCGLFrob.ls_points
#print axioms LinnikCGLFrob.prod_trick_points
#print axioms LinnikCGLFrob.sum_Dp_sq_le
#print axioms LinnikCGLFrob.gram_sq_le
#print axioms LinnikCGLFrob.frobOff_le
#print axioms LinnikCGLS2.LSX_le
#print axioms LinnikCGLS2.Bmax_le
#print axioms LinnikCGLS2.s2_main
#print axioms LinnikCGLS2.cgls2
#print axioms LinnikCGLS2.linnik_225c_s3
#print axioms LinnikCGLS2.linnik_226c_s3
#print axioms LinnikCGLFourier.hasDerivAt_F
#print axioms LinnikCGLFourier.fourier_F
#print axioms LinnikCGLFourier.lemma43
#print axioms LinnikCGLPoisson.poisson_scaled
#print axioms LinnikCGLPoisson.sum_colsP_residue
#print axioms LinnikCGLPoisson.gram_poisson
#print axioms LinnikCGLTrace.S3_eq_cube
#print axioms LinnikCGLTrace.Em_eq
#print axioms LinnikCGLTrace.S3_eq_Fm
#print axioms LinnikCGLDiag.muP_sub_mu0_le
#print axioms LinnikCGLDiag.muP_sub_mu0_le_rpow
#print axioms LinnikCGLDiag.S3_eq_all
#print axioms LinnikCGLTrunc.sum_FmT_cube
#print axioms LinnikCGLTrunc.norm_Fm_sub_FmT_le
#print axioms LinnikCGLTrunc.S3_trunc
#print axioms LinnikCGLProd.prod_eq_iter
#print axioms LinnikCGLProd.iter_swap
#print axioms LinnikCGLProd.hhat_prod
#print axioms LinnikCGLRFact.S2_triple
#print axioms LinnikCGLRFact.sum_Qk
#print axioms LinnikCGLRFact.Ip_eq
#print axioms LinnikCGLRam.norm_Cq_le
#print axioms LinnikCGLRam.Jk_decay
#print axioms LinnikCGLRam.Jk_eq_zero_of
#print axioms LinnikCGLP71.norm_Psi_le
#print axioms LinnikCGLP71.prop71
#print axioms LinnikCGLSym.prop71r
#print axioms LinnikCGLSym.Ip_cyc
#print axioms LinnikCGLSym.sum_le_three_mul
#print axioms LinnikCGLRt.local_le_Rt_sq
#print axioms LinnikCGLRt.inner_le
#print axioms LinnikCGLRt.Vr_inner_le
#print axioms LinnikCGLP72.Ip_le_It
#print axioms LinnikCGLP72.sum_Ak_regroup
#print axioms LinnikCGLP72.prop72
#print axioms LinnikCGLMom.lemma91
#print axioms LinnikCGLMom.lemma91_Rt
#print axioms LinnikCGLMom4.lemma92
#print axioms LinnikCGLMom4.lemma92_Rt
#print axioms LinnikCGLCS.sum_It_sq_le
#print axioms LinnikCGLCS.S32_le
#print axioms LinnikCGLJ.S34_le_Jint
#print axioms LinnikCGLJ.S33_le_S34
#print axioms LinnikCGLFb.contDiff_fb
#print axioms LinnikCGLFb.fb_one_ge
#print axioms LinnikCGLFb.S34_le_fb
#print axioms LinnikCGLPhi.integral_abs_iteratedDeriv_phi_le
#print axioms LinnikCGLPhi.fourier_phi_le
#print axioms LinnikCGLDecay.fb_decay
#print axioms LinnikCGLDecay.fb_decay_all
#print axioms LinnikCGLBlock.S34_le_P81
#print axioms LinnikCGLBlock.block_le
#print axioms LinnikCGL112.S3_le_blocks
#print axioms LinnikCGL112.S3_le_112
#print axioms LinnikCGLLoc.norm_esum_le_integral
#print axioms LinnikCGLLoc.norm_sq_esum_le
#print axioms LinnikCGLLoc.norm_cube_esum_le
#print axioms LinnikCGLL105.sum_triple_le
#print axioms LinnikCGLL105.lemma105
#print axioms LinnikCGLT101.sum_sq_R2_eq
#print axioms LinnikCGLT101.lemma106
#print axioms LinnikCGLL107.group_le
#print axioms LinnikCGLL107.lemma107
#print axioms LinnikCGLSep.log_sep
#print axioms LinnikCGLSep.sum_cube_le
#print axioms LinnikCGLL109.sum_cube_moment_le
#print axioms LinnikCGLL109.lemma109
#print axioms LinnikCGLL1010.lemma106'
#print axioms LinnikCGLL1010.lemma1010
#print axioms LinnikCGLCase.case_le
#print axioms LinnikCGLCase.remark103
#print axioms LinnikCGLCase.lemma1010_case
#print axioms LinnikCGLEps.lemma109_eps
#print axioms LinnikCGLEps.lemma1010_eps
#print axioms LinnikCGLEps.prop102
#print axioms LinnikCGLS3.cgls3
#print axioms LinnikCGLS3.prop31_pt
#print axioms LinnikCGLS3.linnik_225c_pt
#print axioms LinnikCGLS3.linnik_226c_pt
#print axioms LinnikCGLG.Jint_le_ga
#print axioms LinnikCGLG.integral_sq_ga
#print axioms LinnikCGLG.fourier_ga
#print axioms LinnikCGLPois8.poisson_S
#print axioms LinnikCGLPois8.fourier_ga_poisson
#print axioms LinnikCGLCount.count_le
#print axioms LinnikCGLAsum.sum_a_finite_le
#print axioms LinnikCGLNsum.fourier_ga_split
#print axioms LinnikCGLNsum.sum_a_fourier_ga_le
#print axioms LinnikCGLN0.sum_integral_g0_le
#print axioms LinnikCGLCov.integral_r_eq
#print axioms LinnikCGLCov.integral_gstar_le
#print axioms LinnikCGLSig2.sum_psi_norm_Phi_sq_le
#print axioms LinnikCGLSig2.norm_S2_le
#print axioms LinnikCGLFtil.integral_S2_le
#print axioms LinnikCGLFtil.sum_psi_norm_Phi_sq_le_ftil
#print axioms LinnikCGLJtil.sum_psi_norm_Phi_sq_le_J
#print axioms LinnikCGLJtil.sum_integral_Phi_le
#print axioms LinnikCGLTail.sum_integral_Phi_tail_le
#print axioms LinnikCGLTail.setIntegral_ga_tail_le
#print axioms LinnikCGLL82.lemma82_explicit
#print axioms LinnikCGLConst.sum_gw_le
#print axioms LinnikCGLConst.KX_le
#print axioms LinnikDetect.LSeries_aXχ
#print axioms LinnikDetect.detect_identityχ
#print axioms LinnikDetect.dichotomy
#print axioms LinnikDensity.class1_count
#print axioms LinnikDensity.class2_count
#print axioms LinnikDensity.count_nontrivial
#print axioms LinnikDensity.charDensity_of_LBound
#print axioms LinnikDensity.charDensity_of_critBound
#print axioms LinnikDensity.linnik_of_critBound
#print axioms LinnikDensity.LFunction_split
#print axioms LinnikDensity.norm_LFunction_half_le
#print axioms LinnikDensity.critBoundχ_half
#print axioms LinnikDensity.linnik_four
#print axioms LinnikFE.rootNumber_inv
#print axioms LinnikFE.rootNumber_mul_inv
#print axioms LinnikFE.norm_rootNumber
#print axioms LinnikFE.norm_Gamma_mul_sin_le
#print axioms LinnikFE.norm_LFunction_one_sub_le
#print axioms LinnikLindelof.norm_LFunction_le_zeta32
#print axioms LinnikLindelof.inv_norm_LFunction_le_zeta32
#print axioms LinnikLindelof.logDeriv_le_interp
#print axioms LinnikLindelof.lindelof
#print axioms LinnikSubconvex.primitive_bound
#print axioms LinnikSubconvex.prod_primeFactors_le
#print axioms LinnikSubconvex.critBoundχ
#print axioms LinnikSubconvex.linnik_seventeen_sixths
#print axioms MertensChi.LSeries_fχμ
#print axioms MertensChi.norm_sum_le
#print axioms MertensChi.isBigO
#print axioms LinnikGamma.norm_gammaFactor_ratio_le
#print axioms LinnikGamma.verticalIntegral_sub_eq
#print axioms LinnikGamma.afe
#print axioms LinnikFourth.norm_LFunction_four_le
#print axioms LinnikFourth.sum_norm_Pd_sq_le
#print axioms LinnikFourth.afeJ_split
#print axioms LinnikFourth.sum_norm_afeD_sq_le
#print axioms LinnikFourth.fourth_moment_primitive
#print axioms LinnikFourth.fourth_moment
#print axioms LinnikIngham.class2_count_ingham
#print axioms LinnikIngham.count_nontrivial_ingham
#print axioms LinnikIngham.charDensity_ingham
#print axioms LinnikIngham.linnik_thirtysix_thirteenths
#print axioms LinnikPower.card_divisors_le
#print axioms LinnikPower.pv_pow
#print axioms LinnikPower.hm_duality
#print axioms LinnikOffDiag.left_line
#print axioms LinnikOffDiag.norm_offK_le
#print axioms LinnikHuxley.power_count
#print axioms LinnikHuxley.class2_count_small
#print axioms LinnikHuxley.class1_huxley
#print axioms LinnikHuxley.count_huxley
#print axioms LinnikHuxley.charDensity_huxley
#print axioms LinnikHuxley.linnik_eighty_seven_thirty_fifths
#print axioms LinnikReflect.LFunction_eq_reflect
#print axioms LinnikReflect.reflect
#print axioms LinnikReflect.hm_duality_W
#print axioms LinnikReflect.norm_hTerm_le_reflect
#print axioms LinnikReflect.huxley_core
#print axioms LinnikReflect.pair_kernel_one
#print axioms LinnikReflect.pair_kernel_two
#print axioms LinnikReflect.pair_sum_pointwise
#print axioms LinnikReflect.kernel_sum_le
#print axioms LinnikReflect.huxley_large_values
#print axioms LinnikTwelve.block_bin_hux
#print axioms LinnikTwelve.count_middle_c10
#print axioms LinnikTwelve.term1_le
#print axioms LinnikTwelve.term2_le
#print axioms LinnikTwelve.class1_twelve
#print axioms LinnikTwelve.count_twelve_fifths
#print axioms LinnikTwelve.charDensity_twelve_fifths
#print axioms LinnikTwelve.linnik_twelve_fifths
#print axioms LinnikMoment.moment_three
#print axioms LinnikMoment.moment_three_chars
#print axioms LinnikMoment.refined_moment
#print axioms LinnikMoment.refined_moment_cube
#print axioms LinnikMoment.refined_moment_chars
#print axioms LinnikLines.triple_eq
#print axioms LinnikLines.line_sum_identity
#print axioms LinnikLines.line_sum_identity_of_zero
#print axioms LinnikLines.gram_eq_gramZ
#print axioms LinnikLines.large_values_lines
#print axioms LinnikSplit.lineSum_zero
#print axioms LinnikSplit.sum_lines_split
#print axioms LinnikSplit.large_values_split
#print axioms LinnikS2.S2_closed
#print axioms LinnikS2.large_values_socket
EOT
echo "== axioms"
# every #print axioms line must print an axiom list inside the three, and no axiom line may name another axiom
out="$(LEAN_PATH="$LP" lean "$AX" 2>&1)" || { printf '%s\n' "$out"; echo "axioms check FAILED: lean exited nonzero" >&2; exit 1; }
printf '%s\n' "$out"
want=$(grep -c '^#print axioms' "$AX" || true)
good=$(printf '%s\n' "$out" | grep -Ec "$CLEAN|' does not depend on any axioms" || true)
bad=$(dirty "$out")
if [ "$bad" != 0 ] || [ "$good" != "$want" ]; then
  echo "axioms check FAILED: $good of $want #print axioms lines are inside [propext, Classical.choice, Quot.sound]; $bad axiom lines are not" >&2
  exit 1
fi
rm -f "$AX"
