#!/usr/bin/env python3
"""Round 94: score PREREG_superposition.md (the "smooth" slots hold the superposed zero set). Adapted from round 91. Usage: kresonance.py [out.json]"""
import sys, json, glob, numpy as np
from mpmath import mpf
def zs(tag):
    r = {}
    for f in [f"zeroside_{tag}.jsonl"]:
        for l in open(f):
            if l.strip(): o = json.loads(l); r[o["x"]] = float(o["lnK00"])
    x = np.array(sorted(r)); return x, np.array([r[k] for k in x])
x0, l0 = zs("true"); x1, l1 = zs("superposed"); assert len(x0) == len(x1) == 451 and np.allclose(x0, x1)
x = x0; d = np.log(x)
m = {}
for l in open("hamiltonian_grid_to3.jsonl"):
    if l.strip(): o = json.loads(l); m[o["delta"]] = float(mpf(o["lnK00"]))
md = np.array(sorted(m)); lm = np.interp(d, md, [m[k] for k in md])
B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T
res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
r0, r1, rm = res(l0), res(l1), res(lm)
def spec(r):
    G = np.linspace(x[0], x[-1], 8192); y = np.interp(G, x, r); y = (y - np.polyval(np.polyfit(G, y, 3), G))*np.hanning(len(G))
    return 2*np.pi*np.fft.rfftfreq(len(G), G[1] - G[0]), np.abs(np.fft.rfft(y))**2
res_w = 2*np.pi/(x[-1] - x[0])
def peak(r):
    w, P = spec(r); s = (w >= 8) & (w <= 11); return float(w[s][np.argmax(P[s])])
def line(r, t):
    w, P = spec(r); mm = np.abs(w - t) <= res_w; at = P[mm].max(); fl = P[(w >= 5) & (w <= 15) & (np.abs(w - t) > 1)]
    return dict(target=round(t, 3), peak_at=round(float(w[mm][np.argmax(P[mm])]), 3), power_over_q95=round(float(at/np.percentile(fl, 95)), 3), passes=bool(at > np.percentile(fl, 95)))
def top(r, n=6):
    w, P = spec(r); s = (w > 0.8) & (w < 26); idx = []; 
    for i in np.argsort(P[s])[::-1]:
        if all(abs(i - j) > 3 for j in idx): idx.append(i)
        if len(idx) == n: break
    tot = P[s].sum(); return [(round(float(w[s][i]), 2), round(float(P[s][i]/tot), 3)) for i in idx]
p0, p1 = peak(r0), peak(r1)
V = float(np.corrcoef(r0, rm)[0, 1])
L0, L1, Lm = line(r0, p0), line(r1, p0), line(rm, p0)
R = bool(np.corrcoef(r1, rm)[0, 1] >= 0.9 and line(r1, p0)["passes"])
out = dict(validation_corr=round(V, 4), V=bool(V >= 0.9), peak_true=round(p0, 3), peak_smooth=round(p1, 3), peak_measured=round(peak(rm), 3),
           line_true=L0, line_smooth_at_true_peak=L1, line_measured=Lm, line_smooth_own=line(r1, p1),
           S_passes=R, corr_superposed_measured=float(np.corrcoef(r1, rm)[0, 1]), rms_true=float(r0.std()), rms_smooth=float(r1.std()), rms_ratio=float(r1.std()/r0.std()),
           corr_smooth_true=float(np.corrcoef(r0, r1)[0, 1]), top_true=top(r0), top_smooth=top(r1), top_measured=top(rm))
for k, v in out.items(): print(k, v)
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
np.savez("ksuperpose_series.npz", x=x, true=l0, smooth=l1, measured=lm, r_true=r0, r_smooth=r1, r_meas=rm)
