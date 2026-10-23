#!/usr/bin/env python3
"""Round 104: score PREREG_linresp.md."""
import sys, json, glob, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
R = {}
for f in glob.glob("r104_*.jsonl"):
    for l in open(f):
        if l.strip(): o = json.loads(l); R[o["x"]] = o
x = np.array(sorted(R)); assert len(x) == 226
xt, lt = load("r95_true.jsonl"); x0, l0 = load("r95_pzeros_0.jsonl"); x7, l7 = load("r95_pzeros_7.jsonl")
assert np.allclose(xt, x) and np.allclose(x0, x)
base = np.array([float(R[v]["lnK_base"]) for v in x]); print("base vs round-95 smooth: max diff", float(np.max(abs(base - l0))))
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T
res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
out = {}
for name, lact in (("true", lt), ("P7", l7)):
    act = lact - l0; ra = res(act)
    for o in ("d1", "d2"):
        pr = np.array([R[v][f"{o}_{name}"] for v in x]); rp = res(pr)
        out[f"{o}_{name}"] = dict(corr=round(float(np.corrcoef(rp, ra)[0, 1]), 4), rms_ratio=round(float(rp.std()/ra.std()), 3),
                                 raw_max_abs_err=round(float(np.max(abs(pr - act))), 4), raw_rms_err=round(float(np.std(pr - act)), 4), raw_rms_act=round(float(np.std(act)), 4))
    # tones of the predicted residual (second order) vs actual
    for lab, series in (("pred", np.array([R[v][f"d2_{name}"] for v in x])), ("act", act)):
        rr = res(series); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
        Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > 1.5) & (w < 30); ws, Ps = w[s], Y[s]
        loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:5]
        out[f"tones_{lab}_{name}"] = sorted([(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc])
c = out["d2_true"]; out["LR2_pass"] = bool(c["corr"] >= 0.9 and 0.7 <= c["rms_ratio"] <= 1.3)
out["verdict"] = "LR2 pass" if out["LR2_pass"] else ("partial" if c["corr"] >= 0.5 else "fail")
for k, v in out.items(): print(k, v)
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
