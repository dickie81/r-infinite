#!/usr/bin/env python3
"""Round 83: is the fine structure of the potential q(a) real or a truncation artefact?
Computes q = l' + l''/l' (d/d delta; = phi'(a)) from two grids with different basis sizes on the common range,
by local cubic fits (half-width hw), and compares the residual q - 4 pi e^delta and its extrema.
Usage: kcompare.py 'gridA*.jsonl' 'gridB*.jsonl' [hw]"""
import sys, json, glob
import numpy as np
from mpmath import mpf
def load(pat):
    rows = []
    for f in sorted(glob.glob(pat)): rows += [json.loads(l) for l in open(f) if l.strip()]
    rows.sort(key=lambda x: x["delta"])
    return np.array([x["delta"] for x in rows]), np.array([float(mpf(x["lnK00"])) for x in rows])
hw = float(sys.argv[3]) if len(sys.argv) > 3 else 0.02
def qcurve(d, l, grid):
    out = []
    for dd in grid:
        m = np.abs(d - dd) <= hw + 1e-12
        c = np.polyfit(d[m] - dd, l[m], 3); lp, lpp = c[2], 2*c[1]
        out.append(lp + lpp/lp - 4*np.pi*np.exp(dd))
    return np.array(out)
dA, lA = load(sys.argv[1]); dB, lB = load(sys.argv[2])
lo = max(dA[0], dB[0]) + hw; hi = min(dA[-1], dB[-1]) - hw
grid = np.arange(lo, hi, 0.0025)
rA, rB = qcurve(dA, lA, grid), qcurve(dB, lB, grid)
def ext(r): return [grid[i] for i in range(1, len(r) - 1) if (r[i] - r[i-1])*(r[i+1] - r[i]) < 0]
eA, eB = ext(rA), ext(rB)
print(f"range delta [{lo:.3f}, {hi:.3f}] ; residual rms A {np.sqrt(np.mean(rA**2)):.3f}  B {np.sqrt(np.mean(rB**2)):.3f} ; rms(A-B) {np.sqrt(np.mean((rA-rB)**2)):.3f} ; corr {np.corrcoef(rA, rB)[0,1]:.4f}")
print("extrema A:", [round(x, 4) for x in eA]); print("extrema B:", [round(x, 4) for x in eB])
if eA and eB:
    print("mean |shift| A->nearest B:", round(float(np.mean([min(abs(x - y) for y in eB) for x in eA])), 4))
