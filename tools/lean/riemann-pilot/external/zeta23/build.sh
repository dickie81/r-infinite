#!/usr/bin/env bash
# Build the zeta23 layer on the pilot's toolchain. Usage: ./build.sh, after ../../build.sh. Set MATHLIB as for
# ../../build.sh. Optionally set ZETA23 to a clone of anthropics/formal-math that contains commit fbdc36b;
# otherwise that one commit is fetched.
# The script takes the 59 zeta23 files that this layer uses (Montgomery–Vaughan, Riemann–von Mangoldt, the Γ
# facts, the zero side's block structure, and their dependencies), at commit fbdc36b (Lean v4.33.0-rc2), applies zeta23_port.patch (the port to
# the pilot's Lean and Mathlib), and compiles those files and this directory's files into ../../build.
# It then prints the axioms of the final theorems, and fails unless each is [propext, Classical.choice, Quot.sound].
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PILOT="$(cd "$HERE/../.." && pwd)"
REV=fbdc36bbf17d20af3fd0447c6d1a8a02773c9844
UP="$HERE/upstream"
# In dependency order.
MODS="Zeta23.MV.Spacing Zeta23.MV.Quadratic Zeta23.MV.EigenIdentity Zeta23.MV.Eigen Zeta23.Defs Zeta23.Hypotheses Zeta23.MV Zeta23.LinAlg.PosIndex Zeta23.LinAlg.HermitianPosPart Zeta23.MV.Duality Zeta23.MV.Final Zeta23.Defs.Counting Zeta23.Statement Zeta23.Statement.Seam Zeta23.ZetaReflect Zeta23.Statement.SeamClosed Zeta23.RvM.Defs Zeta23.Prelude.InstancePriorities Zeta23.FromPNTPlus.StrongPNTPrefix Zeta23.FromPNTPlus.Auxiliary Zeta23.FromPNTPlus.Sobolev Zeta23.FromPNTPlus.Fourier Zeta23.FromPNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic Zeta23.FromPNTPlus.Rectangle Zeta23.FromPNTPlus.Tactic.AdditiveCombination Zeta23.FromPNTPlus.ResidueCalcOnRectangles Zeta23.FromPNTPlus.EulerMaclaurin Zeta23.FromPNTPlus.ZetaBounds Zeta23.RvM.ZetaGrowth Zeta23.RvM.Halving Zeta23.RvM.LocalCount Zeta23.WeilEF.XiLogDeriv Zeta23.Analytic.RectangleLogDeriv Zeta23.RvM.GammaSide Zeta23.RvM.BacklundDefs Zeta23.RvM.ReZeroCount Zeta23.RvM.Backlund Zeta23.RvM.CountByIntegral Zeta23.FromPNTPlus.ZetaConj Zeta23.RvM.Fold Zeta23.RvM.NcountWindow Zeta23.RvM.MainTerm Zeta23.RvM.Statement Zeta23.GammaFacts Zeta23.GammaFacts.Series Zeta23.Analytic.Stirling Zeta23.GammaFacts.Mu Zeta23.GammaFacts.IntMu Zeta23.GammaFacts.StirlingVert Zeta23.GammaFacts.Complete Zeta23.LinAlg.VonNeumann Zeta23.LinAlg.RankTrace Zeta23.LinAlg.Sylvester Zeta23.LinAlg.Inertia Zeta23.LinAlg.Weyl Zeta23.LinAlg Zeta23.Hypotheses.GzGp Zeta23.Assembly.Inputs Zeta23.ZeroSide "
# Re-fetch when the patch is newer than the last port, or when MODS names a file the last port did not fetch.
stale=0
{ [ -f "$UP/.ported" ] && [ ! "$HERE/zeta23_port.patch" -nt "$UP/.ported" ]; } || stale=1
for m in $MODS; do [ -f "$UP/${m//.//}.lean" ] || stale=1; done
if [ "$stale" = 1 ]; then
  rm -rf "$UP"; mkdir -p "$UP"
  if [ -n "${ZETA23:-}" ]; then G="$ZETA23"; else
    G="$UP/.src"; git init -q "$G"
    git -C "$G" fetch -q --depth 1 https://github.com/anthropics/formal-math "$REV"
  fi
  for m in $MODS; do
    f="${m//.//}.lean"; mkdir -p "$UP/$(dirname "$f")"
    git -C "$G" show "$REV:zeta23/$f" > "$UP/$f"
  done
  git -C "$G" show "$REV:zeta23/LICENSE" > "$UP/LICENSE"
  git -C "$G" show "$REV:zeta23/NOTICE" > "$UP/NOTICE"
  (cd "$UP" && patch -s -p1 < "$HERE/zeta23_port.patch")
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
# zeta23's lakefile sets relaxedAutoImplicit = false for its own files.
for m in $MODS; do c "$UP" "$m" -DrelaxedAutoImplicit=false; done
for f in SlogZeta ZeroWindow Dictionary CountCompare HybridCertificate CoImportMV CoImportGamma; do c "$HERE" $f; done
# ax FILE: run FILE's #print axioms lines; fail unless each prints exactly [propext, Classical.choice, Quot.sound]
ax() {
  local out want good
  out="$(LEAN_PATH="$LP" lean "$1" 2>&1)" || { printf '%s\n' "$out"; echo "axioms check FAILED: lean exited nonzero" >&2; exit 1; }
  printf '%s\n' "$out"
  want=$(grep -c '^#print axioms' "$1")
  good=$(printf '%s\n' "$out" | grep -c "' depends on axioms: \[propext, Classical.choice, Quot.sound\]\$" || true)
  if [ "$good" != "$want" ]; then
    echo "axioms check FAILED: $good of $want printed axiom lines are [propext, Classical.choice, Quot.sound]" >&2
    exit 1
  fi
}
AX="$(mktemp --suffix=.lean)"
trap 'rm -f "$AX"' EXIT
cat > "$AX" <<'EOT'
import SlogZeta
import Zeta23.MV.Final
import ZeroWindow
import Dictionary
import CountCompare
import HybridCertificate
#print axioms ZeroWindow.zero_in_window
#print axioms Dictionary.mu_eq_psiRe
#print axioms CountCompare.local_count_le
#print axioms Zeta23.MV.mv_hilbert
#print axioms Zeta23.gammaFacts
#print axioms Zeta23.RvM.riemannVonMangoldt
#print axioms Zeta23.RvM.zeta_local_zero_count
#print axioms HybridCert.cert_general
#print axioms HybridCert.cert_offline
#print axioms HybridCert.hybrid_cert
#print axioms HybridCert.hybrid_cert_pairs
#print axioms HybridCert.hybrid_cert_of_offline
#print axioms HybridCert.hybrid_cert_of_moments
#print axioms HybridCert.hybrid_cert_of_no_offline
#print axioms HybridCert.hybrid_cert_eta_zero
EOT
echo "== axioms"
ax "$AX"
# the co-import files load the pnt layer (PNT+ at 650d312), which clashes with the vendored FromPNTPlus copies that SlogZeta uses
cat > "$AX" <<'EOT'
import CoImportMV
import CoImportGamma
#print axioms CoImportMV.large_values_amgm
#print axioms CoImportMV.dedekindZeta_eq_zeta_mul_L
#print axioms CoImportGamma.amgm_factor_le
EOT
echo "== axioms (co-import files)"
ax "$AX"
rm -f "$AX"
