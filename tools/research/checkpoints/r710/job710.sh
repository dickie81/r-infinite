#!/bin/bash
# job710.sh [LANES]: the round-710 kernel job, round 705's job705.sh with its names changed, at L = 899/400. Compiles SieveCert2Defs
# and SieveGrid22475R one at a time; then the first part file alone, as a calibration; then the other part files in up to LANES parallel lean
# processes (default 2; 1 if the calibration's peak exceeds 6 GiB), never launching a new one while the lean processes'
# total resident memory exceeds 8 GiB. Each module is compiled with external/pnt/build.sh's own lean invocation into
# the pilot's build/, skipped if its olean is newer than its source and its imports' oleans (build.sh's rule), checked
# for errors, `sorry` and axioms outside the three, and its olean and ilean copied to tools/research/checkpoints/r710/
# (committed and pushed every 10 min by tools/research/run_with_checkpoints.sh). Progress:
# checkpoints/r710/progress.txt. After a container loss, rebuild the pilot and the external layer, run restore710.sh,
# and start this script again: finished modules are skipped.
set -u
S=/tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad
REPO=/home/user/r-infinite; PILOT=$REPO/tools/lean/riemann-pilot; HERE=$PILOT/external/pnt; B=$PILOT/build
CK=$REPO/tools/research/checkpoints/r710; mkdir -p "$CK"; LANES=${1:-2}
export PATH="$HOME/.elan/bin:$PATH"
cd "${MATHLIB:-$S/mathlib4}" || exit 1
LP="$(lake env printenv LEAN_PATH):$B"
STD='(propext|Classical\.choice|Quot\.sound)'
log() { echo "$(date -u +%FT%TZ) $*" >> "$CK/progress.txt"; }
uptodate() {
  local src="$HERE/$1.lean" olean="$B/$1.olean" dep d
  [ -f "$olean" ] && [ ! "$src" -nt "$olean" ] || return 1
  for dep in $(sed -nE 's/^[[:space:]]*(public[[:space:]]+)?import[[:space:]]+//p' "$src"); do
    d="$B/${dep//.//}.olean"; [ -f "$d" ] && [ "$d" -nt "$olean" ] && return 1
  done
  return 0
}
leanrss() { ps -o rss= -C lean 2>/dev/null | awk '{s += $1} END {print s + 0}'; }
compile_one() {
  local m=$1 src="$HERE/$1.lean" olean="$B/$1.olean" t0 peak=0 r pid rc
  if uptodate "$m"; then log "$m up-to-date"; return 0; fi
  t0=$(date +%s)
  LEAN_PATH="$LP" lean -R "$HERE" -o "$olean" -i "$B/$m.ilean" "$src" > "$CK/$m.out" 2>&1 &
  pid=$!
  while kill -0 $pid 2>/dev/null; do
    r=$(ps -o rss= -p $pid 2>/dev/null | tr -d ' '); [ -n "$r" ] && [ "$r" -gt "$peak" ] && peak=$r; sleep 2
  done
  wait $pid; rc=$?
  log "$m rc=$rc $(( $(date +%s) - t0 ))s peak=${peak}KiB"
  if [ "$rc" != 0 ] || grep -qE ': error|declaration uses .sorry.' "$CK/$m.out" || \
     grep "depends on axioms" "$CK/$m.out" | grep -vqE "\[$STD(, $STD)*\]\$"; then
    log "FAILED $m"; touch "$CK/FAILED"; rm -f "$olean" "$B/$m.ilean"; return 1
  fi
  cp "$olean" "$B/$m.ilean" "$CK/"
}
rm -f "$CK/FAILED"; log "START lanes<=$LANES"
for m in SieveCert2Defs SieveGrid22475R; do compile_one "$m" || exit 1; done
mapfile -t PARTS < <(tr ' ' '\n' < $S/r710b/modules22475r.txt | grep '^SieveCert22475RP')
CAL=${PARTS[0]}; compile_one "$CAL" || exit 1
act=$(grep " $CAL rc=0 " "$CK/progress.txt" | tail -n 1 | sed -E 's/.*peak=([0-9]+)KiB.*/\1/')
L=$LANES
if [ -n "$act" ] && [ "$act" -gt 6291456 ]; then L=1; fi
log "CALIBRATION $CAL measured ${act:-?}KiB -> lanes $L"
for m in "${PARTS[@]:1}"; do
  [ -f "$CK/FAILED" ] && break
  while [ "$(jobs -rp | wc -l)" -ge "$L" ]; do wait -n; done
  while [ "$(leanrss)" -gt 8388608 ]; do sleep 5; done
  compile_one "$m" &
done
wait
[ -f "$CK/FAILED" ] && { log "STOPPED (a part failed)"; exit 1; }
log "JOB710DONE"
