#!/usr/bin/env bash
# Build the external layer (rungs 1–3 of the wander ladder, rounds 191–216) on the pilot's own toolchain.
# Usage: ./build.sh, after ../../build.sh. Set MATHLIB as for ../../build.sh. Optionally set PNT to a
# PrimeNumberTheoremAnd clone that contains commit 650d312; otherwise that one commit is fetched.
# The script takes the 19 PrimeNumberTheoremAnd (PNT+) files that the layer imports, at 650d312 (Lean v4.33.1),
# applies pnt_port.patch (the port to the pilot's Lean and Mathlib), and compiles Architect.lean (a no-op
# stand-in for the LeanArchitect blueprint package), those files and this directory's files into ../../build.
# It then prints the axioms of the final theorems. The build fails if Lean reports a use of sorry in one of this
# directory's files, or if this directory's files or the final check print an axiom outside propext,
# Classical.choice and Quot.sound (round 327, the rule of ../../build.sh). The vendored PNT+ files are not checked:
# two lemmas of PNT+'s Wiener.lean are sorry, outside the dependency cone of every theorem here, and the final
# check gates the theorems built on PNT+.
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
# c GATE ROOT MODULE [lean options]: compile ROOT/MODULE.lean to B/MODULE.olean. With GATE = 1, fail, removing
# that olean, if Lean reports a use of sorry in the file or it prints an axiom outside the three.
c() {
  local gate=$1 root=$2 rel=${3//.//} out; shift 3
  echo "== ${rel//\//.}"; mkdir -p "$B/$(dirname "$rel")"
  out="$(LEAN_PATH="$LP" lean "$@" -R "$root" -o "$B/$rel.olean" -i "$B/$rel.ilean" "$root/$rel.lean" 2>&1)" \
    || { printf '%s\n' "$out"; exit 1; }
  [ -z "$out" ] || printf '%s\n' "$out"
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
for f in WanderLadderPNT Rung3 Landau KVBridge LandauKV LogDerivKV MediumPNTW PNTKV KaiserKV TwinKV ShortKV DetectEM KVSubsumes Domination HalfPlanePNT; do c 1 "$HERE" $f; done
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
import HalfPlanePNT
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
