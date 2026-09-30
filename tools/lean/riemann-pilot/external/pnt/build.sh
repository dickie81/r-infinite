#!/usr/bin/env bash
# Build the external layer (rungs 1–3 of the wander ladder, rounds 191–216) on the pilot's own toolchain.
# Usage: ./build.sh, after ../../build.sh. Set MATHLIB as for ../../build.sh. Optionally set PNT to a
# PrimeNumberTheoremAnd clone that contains commit 650d312; otherwise that one commit is fetched.
# The script takes the 19 PrimeNumberTheoremAnd (PNT+) files that the layer imports, at 650d312 (Lean v4.33.1),
# applies pnt_port.patch (the port to the pilot's Lean and Mathlib), and compiles Architect.lean (a no-op
# stand-in for the LeanArchitect blueprint package), those files and this directory's files into ../../build.
# It then prints the axioms of the final theorems.
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
# c ROOT MODULE [lean options]: compile ROOT/MODULE.lean to B/MODULE.olean
c() {
  local root=$1 rel=${2//.//}; shift 2
  echo "== ${rel//\//.}"; mkdir -p "$B/$(dirname "$rel")"
  LEAN_PATH="$LP" lean "$@" -R "$root" -o "$B/$rel.olean" -i "$B/$rel.ilean" "$root/$rel.lean"
}
c "$HERE" Architect
# PNT+'s lakefile sets these two options for its own files.
for f in $PNTFILES; do c "$UP" "PrimeNumberTheoremAnd.${f//\//.}" -DautoImplicit=false -DrelaxedAutoImplicit=false; done
for f in WanderLadderPNT Rung3 Landau KVBridge LandauKV LogDerivKV MediumPNTW PNTKV KaiserKV TwinKV ShortKV DetectEM; do c "$HERE" $f; done
AX="$(mktemp --suffix=.lean)"
cat > "$AX" <<'EOT'
import WanderLadderPNT
import Rung3
import PNTKV
import KaiserKV
import TwinKV
import DetectEM
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
#print axioms PNTKV.PNT_KV
#print axioms KaiserKV.lam_prefactor_KV
#print axioms TwinLandau.Q_ge_of_rates
#print axioms TwinKV.twins_lower_KV
#print axioms TwinKV.twins_lower_KV'
#print axioms ShortKV.zeroFreeXi_KV
#print axioms DetectEM.density_unconditional
#print axioms DetectEM.short_primes
EOT
echo "== axioms"
LEAN_PATH="$LP" lean "$AX"
rm -f "$AX"
