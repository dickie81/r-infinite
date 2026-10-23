#!/usr/bin/env python3
"""Round 89: score pre-registration 4 (PREREG_topology.md). Residual of ln K00 as kspectrum2.py; line tests H2-H4,
one-shot test H1 at x = (217 - 1/2)/(4 pi). Usage: ktopology.py [out.json]"""
import sys, json, numpy as np
from mpmath import mpf
def load(f):
    return {round(x["delta"], 7): float(mpf(x["lnK00"])) for x in map(json.loads, filter(str.strip, open(f)))}
old = load("hamiltonian_grid_to3.jsonl"); new = load("hamiltonian_grid_x20_55.jsonl")
d = np.array(sorted(set(old) | set(new))); d = d[d >= 0.5]
l = np.array([new.get(k, old.get(k)) for k in d]); isnew = np.array([k in new and k not in old for k in d], float)
x = np.exp(d)
A = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d), isnew, isnew*d]).T
r = l - A @ np.linalg.lstsq(A, l, rcond=None)[0]
def spec(lo, hi):
    s = (x >= lo) & (x <= hi); u = x[s]
    g = np.linspace(u[0], u[-1], 8192); y = np.interp(g, u, r[s]); y = (y - np.polyval(np.polyfit(g, y, 3), g))*np.hanning(len(g))
    return 2*np.pi*np.fft.rfftfreq(len(g), g[1] - g[0]), np.abs(np.fft.rfft(y))**2, u[-1] - u[0]
def line(target, lo, hi, band):
    w, P, L = spec(lo, hi); res = 2*np.pi/L
    at = P[np.abs(w - target) <= res].max()
    fl = P[(w >= band[0]) & (w <= band[1]) & (np.abs(w - target) > 1)]
    q95 = np.percentile(fl, 95); rank = float((fl < at).mean())
    wpk = float(w[(np.abs(w - target) <= res)][np.argmax(P[np.abs(w - target) <= res])])
    return dict(target=round(target, 3), peak_at=round(wpk, 3), power_over_q95=round(float(at/q95), 3), flank_rank=round(rank, 3), passes=bool(at > q95))
out = {"H2_period2": line(4*np.pi**2, 1.65, 20, (30, 50)),
       "H3_period8": line(np.pi**2, 1.65, 54.6, (5, 15)),
       "H4_period4": line(2*np.pi**2, 1.65, 54.6, (15, 25))}
xs = x[(x >= 3) & (x <= 19)]; J = []; R = []
for c in xs:
    a = (x >= c - 1) & (x <= c); b = (x >= c) & (x <= c + 1)
    J.append(abs(np.polyval(np.polyfit(x[a], r[a], 1), c) - np.polyval(np.polyfit(x[b], r[b], 1), c)))
    R.append(np.sqrt(np.mean(r[(x >= c - .5) & (x <= c + .5)]**2)))
J, R = np.array(J), np.array(R); x217 = (217 - .5)/(4*np.pi); near = np.abs(xs - x217) <= 0.1
rk = lambda S: float((S < S[near].max()).mean())
out["H1_d2_217"] = dict(x=round(x217, 4), J_rank=round(rk(J), 4), R_rank=round(rk(R), 4),
                        J_argmax_x=round(float(xs[np.argmax(J)]), 3), R_argmax_x=round(float(xs[np.argmax(R)]), 3),
                        passes=bool(rk(J) >= .975 or rk(R) >= .975))
out["T_supported"] = bool(out["H1_d2_217"]["passes"] or out["H2_period2"]["passes"])
for k, v in out.items(): print(k, v)
w, P, L = spec(1.65, 20); s = (w > 26) & (w < 62); top = np.argsort(P[s])[::-1][:6]
print("top lines in (26, 62) on [1.65,20]:", [round(float(v), 2) for v in w[s][top]])
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
