#!/usr/bin/env python3
"""Round 90: score pre-registration 5 (PREREG_bott.md). Uniform 0.03 x-grid on [20, 37.04] (existing 0.12 grid +
the fine file). Residual after (e^d, d, 1, e^-d); Hann spectrum; omega1 = top peak in [8, 11];
B1: 3w1 or 4w1 line; B2: 8w1 line. Usage: kbott.py fine.jsonl [out.json]"""
import sys, json, numpy as np
from mpmath import mpf
def load(f):
    return {round(x["delta"], 7): float(mpf(x["lnK00"])) for x in map(json.loads, filter(str.strip, open(f)))}
g = load("hamiltonian_grid_x20_55.jsonl"); g.update(load(sys.argv[1]))
d = np.array(sorted(k for k in g if np.exp(k) <= 37.05)); l = np.array([g[k] for k in d]); x = np.exp(d)
dx = np.diff(x); assert len(d) == 569 and dx.min() > 0.0299 and dx.max() < 0.0301, (len(d), dx.min(), dx.max())
B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T
r = l - B @ np.linalg.lstsq(B, l, rcond=None)[0]
G = np.linspace(x[0], x[-1], 8192); y = np.interp(G, x, r); y = (y - np.polyval(np.polyfit(G, y, 3), G))*np.hanning(len(G))
P = np.abs(np.fft.rfft(y))**2; w = 2*np.pi*np.fft.rfftfreq(len(G), G[1] - G[0]); L = x[-1] - x[0]; res = 2*np.pi/L
s = (w >= 8) & (w <= 11); w1 = float(w[s][np.argmax(P[s])])
def line(t):
    m = np.abs(w - t) <= res; at = P[m].max(); fl = P[(w >= t - 4) & (w <= t + 4) & (np.abs(w - t) > 1)]
    return dict(target=round(t, 3), peak_at=round(float(w[m][np.argmax(P[m])]), 3),
                power_over_q95=round(float(at/np.percentile(fl, 95)), 3), flank_rank=round(float((fl < at).mean()), 3),
                passes=bool(at > np.percentile(fl, 95)))
H = {k: line(k*w1) for k in range(2, 9)}
t = (w >= 50) & (w <= 100); i = np.argmax(P[t])
out = dict(n=len(d), L=round(L, 3), res=round(res, 4), omega1=round(w1, 3), slope_s=round(8*w1/(2*np.pi), 3),
           B1=bool(H[3]["passes"] or H[4]["passes"]), B2=bool(H[8]["passes"]),
           harmonics={k: H[k] for k in H}, top_50_100=dict(omega=round(float(w[t][i]), 3), ratio=round(float(w[t][i]/w1), 3)),
           rms_residual=float(np.std(r)))
for k, v in out.items(): print(k, v)
if len(sys.argv) > 2: json.dump(out, open(sys.argv[2], "w"), indent=1)
