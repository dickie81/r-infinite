#!/usr/bin/env bash
# Build rung 3 end to end on PNT+'s toolchain (round 212).
# Usage: PNT=<PrimeNumberTheoremAnd checkout at 650d312, built> ./kv_port.sh [workdir]
# Copies the pilot's layer I–II files, applies the three lemma renames needed by PNT+'s older
# Mathlib (the monoid `Finset.prod_le_prod` was `prod_le_prod'`; `prod_le_prod₀`/`prod_le_one₀`
# were `prod_le_prod`/`prod_le_one`), then compiles them, Landau.lean and KVBridge.lean, and
# prints the axioms of the final theorems.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
PILOT="$HERE/../../src"
W="${1:-$HERE/kvbuild}"
: "${PNT:?set PNT to the PNT+ checkout}"
mkdir -p "$W/src" "$W/build"
FILES="Vinogradov VinoPadic VinoStep VinoIter VinoHolder VinoSplit VinoRec VinoConst VinoConst2 ExpSum ExpSum2 ExpSum3 ExpSum4 ExpSum5 ExpSum6 ExpSum7 ExpSum8 ExpSum9 ExpSum10 VinoBad VinoRec2 VinoFam"
for f in $FILES; do cp "$PILOT/$f.lean" "$W/src/"; done
cp "$HERE/Landau.lean" "$HERE/KVBridge.lean" "$W/src/"
sed -i "s/Finset.prod_le_prod fun e _ => card_residue_le/Finset.prod_le_prod' fun e _ => card_residue_le/" \
  "$W/src/VinoPadic.lean" "$W/src/VinoStep.lean"
sed -i 's/prod_le_one₀/prod_le_one/g; s/prod_le_prod₀/prod_le_prod/g' "$W/src/"*.lean
cat > "$W/src/KVAxioms.lean" <<'EOT'
import KVBridge
#print axioms KVBridge.polylogGrowth_kv
#print axioms KVBridge.polylogGrowth_sharp
#print axioms KVBridge.zeroFree_kv
#print axioms KVBridge.rung3_kv
EOT
cd "$PNT"
export PATH="$HOME/.elan/bin:$PATH"
for f in $FILES Landau KVBridge KVAxioms; do
  echo "== $f"
  W="$W" N="$f" lake env bash -c 'LEAN_PATH="$LEAN_PATH:$W/build" lean -R $W/src -o $W/build/$N.olean -i $W/build/$N.ilean $W/src/$N.lean' \
    2>&1 | grep -v "^warning" | grep -E "error|axioms" || true
done
