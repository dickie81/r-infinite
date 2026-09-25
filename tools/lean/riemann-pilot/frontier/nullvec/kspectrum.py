#!/usr/bin/env python3
"""Round 84: spectrum of the Hamiltonian's fine structure. Residual of ln K_a(0,0) after the smooth fit
A e^delta + B delta + C + D e^{-delta}, resampled uniformly in x = e^delta (and, for contrast, in delta),
cubic-detrended, Hann-windowed; top spectral lines on sub-ranges; correlation with sum_{n<=x} Lambda(n)/sqrt n.
Usage: kspectrum.py grid.jsonl"""
import sys, json, math, numpy as np
from mpmath import mpf
rows = {}
for l in open(sys.argv[1]):
    x = json.loads(l); rows[round(x["delta"], 6)] = float(mpf(x["lnK00"]))
d = np.array(sorted(rows)); l = np.array([rows[k] for k in d]); m = d >= 0.5; d = d[m]; l = l[m]; x = np.exp(d)
A = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; c = np.linalg.lstsq(A, l, rcond=None)[0]; r = l - A@c
print("smooth fit (e^d, d, 1, e^-d):", np.round(c, 5), " residual rms", round(float(np.std(r)), 4))
def spec(lo, hi, var):
    s = (x >= lo) & (x <= hi); u = x[s] if var == "x" else d[s]
    g = np.linspace(u[0], u[-1], 4096); y = np.interp(g, u, r[s]); y = (y - np.polyval(np.polyfit(g, y, 3), g))*np.hanning(len(g))
    F = np.abs(np.fft.rfft(y))**2; w = 2*np.pi*np.fft.rfftfreq(len(g), g[1] - g[0]); pk = []
    for i in np.argsort(F)[::-1]:
        if i < 3: continue
        if all(abs(i - j) > 3 for j in pk): pk.append(i)
        if len(pk) == 8: break
    tot = F[3:].sum()
    return [(round(float(w[i]), 2), round(float(F[i]/tot), 3)) for i in sorted(pk)], round(float(w[1]), 3), float(sum(F[max(3, i-2):i+3].sum() for i in pk)/tot)
for var in ("x", "delta"):
    for lo, hi in ((1.65, 10), (10, 20.1), (1.65, 20.1)):
        p, res, share = spec(lo, hi, var)
        print(f"[{var}] x in [{lo},{hi}] res {res}: lines {p}  top-8 share {share:.2f}")
