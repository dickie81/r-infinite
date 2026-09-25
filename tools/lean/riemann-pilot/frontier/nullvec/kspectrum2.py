#!/usr/bin/env python3
"""Round 85: spectrum of the Hamiltonian's fine structure on larger windows.
Inputs: the K=30 grid (x <= 20) and the K=15 x-grid (x in [20, 54.6]). Smooth fit A e^d + B d + C + D e^{-d}
plus a step at the x = 20 junction (basis factor change); residual resampled uniformly in x = e^delta, detrended,
Hann-windowed. Lines on the new range alone, on the combined range, and per segment (stability).
Usage: kspectrum2.py old.jsonl 'new*.jsonl'"""
import sys, json, glob, math, numpy as np
from mpmath import mpf
def load(files):
    r = {}
    for f in files:
        for l in open(f):
            if l.strip():
                x = json.loads(l); r[round(x["delta"], 7)] = float(mpf(x["lnK00"]))
    return r
old = load([sys.argv[1]]); new = load(glob.glob(sys.argv[2]))
d = np.array(sorted(set(old) | set(new))); d = d[d >= 0.5]
l = np.array([new.get(k, old.get(k)) for k in d]); isnew = np.array([k in new and k not in old for k in d], float)
x = np.exp(d)
A = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d), isnew, isnew*d]).T
c = np.linalg.lstsq(A, l, rcond=None)[0]; r = l - A@c
print("fit (e^d, d, 1, e^-d, step, step*d):", np.round(c, 5), " residual rms", round(float(np.std(r)), 4), " n", len(d))
def lines(lo, hi, nl=8):
    s = (x >= lo) & (x <= hi); u = x[s]
    g = np.linspace(u[0], u[-1], 8192); y = np.interp(g, u, r[s]); y = (y - np.polyval(np.polyfit(g, y, 3), g))*np.hanning(len(g))
    F = np.abs(np.fft.rfft(y))**2; w = 2*np.pi*np.fft.rfftfreq(len(g), g[1] - g[0]); pk = []
    for i in np.argsort(F)[::-1]:
        if i < 3 or w[i] > 26: continue
        if all(abs(i - j) > 3 for j in pk): pk.append(i)
        if len(pk) == nl: break
    tot = F[3:(w <= 26).sum()].sum()
    return sorted([(round(float(w[i]), 2), round(float(F[i]/tot), 3)) for i in pk]), round(float(w[1]), 3)
for lo, hi in ((1.65, 20), (20, 54.6), (20, 37), (37, 54.6), (1.65, 54.6)):
    p, res = lines(lo, hi); print(f"x in [{lo},{hi}] res {res}: {p}")
