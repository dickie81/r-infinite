#!/bin/bash
# Reproduce round 47's cells (outputs in ./work/<node>/la_lam2.json and ./work/lam1up.jsonl).
cd "$(dirname "$0")"; mkdir -p work; cd work
for d in 0.72 1.02 1.28 1.50 1.70 1.87 2.02; do python3 ../lam1up.py $d 120 400 >> lam1up.jsonl; done
../runnode.sh n102 51/100 120 67 1e-4 5e-2
../runnode.sh n128 64/100 240 137 1e-8 1e-4
../runnode.sh n150 75/100 400 248 1e-13 1e-8
../runnode.sh n170 85/100 1000 666 1e-18 1e-13
../runnode.sh n187 935/1000 1000 731 1e-23 1e-17
../runnode.sh n202 101/100 2496 1936 1e-28 1e-22
../runnode.sh n207 1035/1000 2496 1983 1e-29 1e-23
