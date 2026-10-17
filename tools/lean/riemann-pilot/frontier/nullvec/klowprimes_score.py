#!/usr/bin/env python3
"""Round 95: score PREREG_lowprimes.md from the r95_*.jsonl chains. Usage: klowprimes_score.py [out.json]"""
import sys, json, numpy as np
def load(f):
    r = {}
    for l in open(f):
        if l.strip(): o = json.loads(l); r[o["x"]] = float(o["lnK00"])
    x = np.array(sorted(r)); return x, np.array([r[k] for k in x])
x, lt = load("r95_true.jsonl"); d = np.log(x); assert len(x) == 226
B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T
res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
rt = res(lt)
xf, lf = load("zeroside_true.jsonl")                      # round-91 full kernel, step 0.02
V = float(np.corrcoef(rt, res(np.interp(d, np.log(xf), lf)))[0, 1])
G = np.linspace(x[0], x[-1], 8192); resw = 2*np.pi/(x[-1] - x[0])
def spec(r):
    y = np.interp(G, x, r); y = (y - np.polyval(np.polyfit(G, y, 3), G))*np.hanning(len(G))
    return 2*np.pi*np.fft.rfftfreq(len(G), G[1] - G[0]), np.abs(np.fft.rfft(y))**2
def peak(r):
    w, P = spec(r); s = (w >= 8) & (w <= 11); return float(w[s][np.argmax(P[s])])
def line(r, t):
    w, P = spec(r); m = np.abs(w - t) <= resw; at = P[m].max(); fl = P[(w >= 5) & (w <= 15) & (np.abs(w - t) > 1)]
    return round(float(at/np.percentile(fl, 95)), 3), round(float(w[m][np.argmax(P[m])]), 3)
w0 = peak(rt); rows = {}
for P in (0, 2, 3, 5, 7, 13, 31, 101, 1009):
    xp, lp = load(f"r95_pzeros_{P}.jsonl"); assert np.allclose(xp, x); rp = res(lp)
    q, at = line(rp, w0)
    rows[P] = dict(corr_true=round(float(np.corrcoef(rp, rt)[0, 1]), 3), rms_ratio=round(float(rp.std()/rt.std()), 3),
                   line_at_w0=q, line_found_at=at, passes=bool(q > 1), own_peak=round(peak(rp), 3))
LPi = all(rows[P]["passes"] for P in (3, 5, 7, 13, 31, 101)); LPii = rows[3]["corr_true"] >= 0.5
first = next((P for P in (2, 3, 5, 7, 13, 31, 101, 1009) if rows[P]["passes"]), None)
out = dict(V_corr=round(V, 4), V=bool(V >= 0.99), omega0=round(w0, 3), res=round(resw, 3), true_line=line(rt, w0), variants=rows,
           LP_i=LPi, LP_ii=bool(LPii), LP=bool(LPi and LPii), first_P_line_passes=first)
for k, v in out.items():
    if k != "variants": print(k, v)
for P, r in rows.items(): print(" P =", P, r)
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
