#!/bin/bash
# restore710.sh: after a container loss, once ../../build.sh and external/pnt/build.sh have rebuilt the pilot and the
# external layer (the round-710 modules are not in build.sh until the landing), put the checkpointed oleans back into
# build/ with mtimes newer than their sources and imports, so job710.sh skips them.
set -u
REPO=/home/user/r-infinite; B=$REPO/tools/lean/riemann-pilot/build; CK=$REPO/tools/research/checkpoints/r710
n=0
for f in "$CK"/*.olean; do
  [ -f "$f" ] || continue
  m=$(basename "$f" .olean); cp "$f" "$B/$m.olean"; [ -f "$CK/$m.ilean" ] && cp "$CK/$m.ilean" "$B/$m.ilean"
  touch "$B/$m.olean" "$B/$m.ilean" 2>/dev/null; n=$((n + 1))
done
echo "restored $n oleans"
