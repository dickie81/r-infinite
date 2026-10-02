#!/usr/bin/env python3
"""Round 118: score PREREG_primeside.md. Prime-side chain (kprimeside.py, unconditional) vs the zero-side chain r95_true.jsonl
(zeros < 1000 + smooth tail to 6997). Same residual basis and peak finder as rounds 106-116."""
import json, glob, numpy as np
def lx(pat):
    r = {}
    for f in glob.glob(pat):
        for l in open(f):
            if l.strip(): o = json.loads(l); r[o["x"]] = float(o["lnK00"])
    return r
P = lx("rPS_*.jsonl"); Z = lx("r95_true.jsonl")
x = np.array(sorted(P)); assert len(x) == 226 and all(v in Z for v in x)
lp = np.array([P[v] for v in x]); lz = np.array([Z[v] for v in x])
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
def peaks(y, lo=1.5, hi=40, n=4):
    rr = res(y); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]
out = {}
out["corr_wiggles"] = round(float(np.corrcoef(res(lp), res(lz))[0, 1]), 4)
out["max_abs_diff_lnK"] = round(float(np.max(abs(lp - lz))), 4); out["rms_wiggle_prime"] = round(float(np.std(res(lp))), 4)
out["rms_wiggle_diff"] = round(float(np.std(res(lp - lz))), 4)
out["prime_lines"] = peaks(lp); out["zero_lines"] = peaks(lz); out["diff_lines"] = peaks(lp - lz)
P1 = out["corr_wiggles"] >= 0.95
P2 = abs(out["prime_lines"][0][0] - 3*np.pi) <= 0.3
P3 = all(abs(a[0] - b[0]) <= 0.2 for a, b in zip(out["prime_lines"], out["zero_lines"]))
out.update(P1=bool(P1), P2=bool(P2), P3=bool(P3))
for k, v in out.items(): print(k, ":", v)
json.dump(out, open("kprimeside_score_results.json", "w"), indent=1)
