#!/bin/bash
# One node of the round-47 covering: certified lower bound on lambda_2 (even sector) at L = p/q.
# usage: runnode.sh name L T# N lo hi     (e.g. runnode.sh n150 75/100 400 248 1e-13 1e-8)
set -e
D="$(cd "$(dirname "$0")" && pwd)"
mkdir -p "$1" && cd "$1"
export GAP_L=$2 GAP_T=$3 GAP_N=$4 PYTHONPATH=$D
t0=$(date +%s)
python3 $D/nodes.py > nodes.log 2>&1
for k in 0 1 2 3; do python3 $D/assemble.py $k 4 > asm_$k.log 2>&1 & done; wait
python3 $D/la.py lam2 $5 16 0 $6 > la.log 2>&1
echo "elapsed $(($(date +%s)-t0))" >> la.log
