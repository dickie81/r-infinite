#!/usr/bin/env python3
"""Round 83: counting law of the extrema of the chain potential's fine structure.
q - 4 pi e^delta from local cubic fits with a scale-adaptive half-window hw(delta) = min(hwmax, f e^{-delta});
counts maxima N(delta) and fits  A e^delta + B  vs  A e^delta delta + B  vs the zero count N_zeta(c 2 pi e^delta).
Usage: kcount.py 'grid*.jsonl' [f] [hwmax]"""
import sys, json, glob, math
import numpy as np
from mpmath import mpf, nzeros
rows = {}
for f in sorted(glob.glob(sys.argv[1])):
    for l in open(f):
        if l.strip():
            x = json.loads(l); rows[round(x["delta"], 6)] = float(mpf(x["lnK00"]))
d = np.array(sorted(rows)); l = np.array([rows[k] for k in d])
fac = float(sys.argv[2]) if len(sys.argv) > 2 else 0.15; hwmax = float(sys.argv[3]) if len(sys.argv) > 3 else 0.02
grid = []; r = []
for dd in d[(d > d[0] + 0.03) & (d < d[-1] - 0.03)]:
    hw = min(hwmax, fac*math.exp(-dd))
    m = np.abs(d - dd) <= hw + 1e-12
    if m.sum() < 5: continue
    c = np.polyfit(d[m] - dd, l[m], 3); grid.append(dd); r.append(c[2] + 2*c[1]/c[2] - 4*np.pi*np.exp(dd))
grid = np.array(grid); r = np.array(r)
from scipy.signal import find_peaks
prom = float(sys.argv[4]) if len(sys.argv) > 4 else 1.0
pk, _ = find_peaks(r, prominence=prom); mx = grid[pk]
print(f"delta range [{grid[0]:.3f}, {grid[-1]:.3f}], {len(mx)} maxima")
N = np.arange(1, len(mx) + 1)
for name, X in (("e^d", np.exp(mx)), ("e^d*d", np.exp(mx)*mx)):
    A = np.vstack([X, np.ones_like(X)]).T; c = np.linalg.lstsq(A, N, rcond=None)[0]
    print(f"N ~ {c[0]:.4f}*{name} + {c[1]:.2f}   rms {np.sqrt(np.mean((A@c - N)**2)):.3f}")
# zero count at horizon c * 2 pi e^delta, best c
best = None
for cc in np.linspace(0.3, 3.0, 271):
    Z = np.array([float(nzeros(cc*2*math.pi*math.exp(x))) for x in mx])
    A = np.vstack([Z, np.ones_like(Z)]).T; c = np.linalg.lstsq(A, N, rcond=None)[0]
    rms = np.sqrt(np.mean((A@c - N)**2))
    if best is None or rms < best[0]: best = (rms, cc, c)
print(f"N ~ {best[2][0]:.3f}*N_zeta({best[1]:.2f}*T0) + {best[2][1]:.2f}   rms {best[0]:.3f}")
bins = np.arange(0.5, grid[-1] + 0.25, 0.25)
print("maxima per 0.25 in delta, and / (pi e^delta * 0.25):")
for b0 in bins[:-1]:
    k = ((mx >= b0) & (mx < b0 + 0.25)).sum(); pred = math.pi*(math.exp(b0 + 0.25) - math.exp(b0))
    print(f"  [{b0:.2f},{b0+0.25:.2f}) {k:3d}   ratio {k/pred:.2f}")
np.save("runs/hgridX/residual.npy", np.vstack([grid, r]))
