#!/usr/bin/env bash
cd "$(dirname "$0")"
run() { timeout 4h python3 angle_gap.py "$@" >> angle_gap_results.jsonl 2>> err.txt; }
run 1.4 90 500 & run 1.8 120 700 & run 2.2 160 900 & run 2.6 200 1000 & wait
run 3.0 240 1100 & run 3.4 280 1400 & wait
echo DONE >> err.txt
