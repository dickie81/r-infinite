#!/bin/bash
# start710.sh: round 710's job start, round 705's start705.sh with its names changed — copy the window file, the grid
# and the 135 part files into
# external/pnt (not into build.sh: the landing adds them), commit them as work in progress so a
# container loss keeps them, push, then run job710.sh under tools/research/run_with_checkpoints.sh (checkpoints committed
# and pushed every 10 min) with an RSS watcher. Idempotent: files already identical are left alone; the job skips
# modules whose oleans are up to date.
set -euo pipefail
S=/tmp/claude-0/-home-user-r-infinite/db46f946-fd0e-58a3-baf6-61ea74b579d4/scratchpad
REPO=/home/user/r-infinite; HERE=$REPO/tools/lean/riemann-pilot/external/pnt
n=0
for f in $S/r710b/src/SieveTypeIIU22475C.lean $S/r710b/out/SieveGrid22475R.lean $S/r710b/out/SieveCert22475RP*.lean; do
  b=$(basename "$f")
  if [ -f "$HERE/$b" ] && cmp -s "$f" "$HERE/$b"; then continue; fi
  cp "$f" "$HERE/$b"; n=$((n + 1))
done
echo "copied $n files"
cd $REPO
if [ -n "$(git status --porcelain tools/lean/riemann-pilot/external/pnt)" ]; then
  # round 710 began at 2249/1000 (55c3f48) and moved to 899/400: its files go
  git rm -q --ignore-unmatch tools/lean/riemann-pilot/external/pnt/SieveTypeIIU2249C.lean \
    tools/lean/riemann-pilot/external/pnt/SieveGrid2249R.lean 'tools/lean/riemann-pilot/external/pnt/SieveCert2249RP*.lean'
  git add tools/lean/riemann-pilot/external/pnt/SieveTypeIIU22475C.lean tools/lean/riemann-pilot/external/pnt/SieveGrid22475R.lean \
    tools/lean/riemann-pilot/external/pnt/SieveCert22475RP*.lean
  git commit -q -F $S/r710b/wip_commit_msg.txt
  for d in 0 2 4 8 16; do [ $d = 0 ] || sleep $d; git push -q -u origin claude/cascade-series-review-1axe9q && break; done
  git log --oneline -1
fi
mkdir -p $REPO/tools/research/checkpoints/r710
# the job's scripts beside its checkpoints, which the wrapper commits, so a container loss keeps them too
cp $S/r710b/job710.sh $S/r710b/restore710.sh $S/r710b/start710.sh $S/r710b/modules22475r.txt $REPO/tools/research/checkpoints/r710/
( while true; do r=$(ps -o rss= -C lean 2>/dev/null | tr -d ' ' | paste -sd+ | bc 2>/dev/null); echo "$(date -u +%T) $(pgrep -x lean | wc -l) ${r:-0}"; sleep 10; done ) >> $S/r710b/rss_watch.log 2>&1 &
echo $! > $S/r710b/watcher.pid
nohup bash $REPO/tools/research/run_with_checkpoints.sh $S/r710b/job710.log bash $S/r710b/job710.sh > $S/r710b/wrapper.log 2>&1 &
echo $! > $S/r710b/wrapper.pid
echo "job started $(date -u +%FT%TZ) wrapper pid $(cat $S/r710b/wrapper.pid)"
