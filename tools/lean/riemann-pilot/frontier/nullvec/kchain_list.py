#!/usr/bin/env python3
"""Round 90 driver: run kchain.run on an explicit list of x = e^delta values.
Usage: kchain_list.py Kfac PF x1 x2 ...  (JSON lines to stdout, as kchain.py)"""
import sys, math, json
src = open(__file__.replace("kchain_list.py", "kchain.py")).read().split("d0, d1, st =")[0]
exec(src)
Kf, PF = float(sys.argv[1]), float(sys.argv[2])
for xv in map(float, sys.argv[3:]):
    d = round(math.log(xv), 7); K = max(40, int(Kf*math.exp(d)) + 40); prec = int(300 + PF*math.exp(d))
    print(json.dumps(run(d, K, prec)), flush=True)
