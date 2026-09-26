#!/usr/bin/env python3
"""Round 96: score PREREG_primeablation.md from r96_*.jsonl (and round 95's r95_true / r95_pzeros_101)."""
import sys, json, numpy as np
def load(f):
    r = {}
    for l in open(f):
        if l.strip(): o = json.loads(l); r[o["x"]] = float(o["lnK00"])
    x = np.array(sorted(r)); return x, np.array([r[k] for k in x])
x, lt = load("r95_true.jsonl"); d = np.log(x)
B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T
res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
rt = res(lt); base = float(np.corrcoef(res(load("r95_pzeros_101.jsonl")[1]), rt)[0, 1])
G = np.linspace(x[0], x[-1], 8192); resw = 2*np.pi/(x[-1] - x[0])
def spec(r):
    y = np.interp(G, x, r); y = (y - np.polyval(np.polyfit(G, y, 3), G))*np.hanning(len(G))
    return 2*np.pi*np.fft.rfftfreq(len(G), G[1] - G[0]), np.abs(np.fft.rfft(y))**2
def top(r, lo=2, hi=40, n=4):
    w, P = spec(r); s = (w >= lo) & (w <= hi); ws, Ps = w[s], P[s]; idx = []
    for i in np.argsort(Ps)[::-1]:
        if all(abs(i - j) > 2 for j in idx): idx.append(i)
        if len(idx) == n: break
    tot = Ps.sum(); return [(round(float(ws[i]), 3), round(float(Ps[i]/tot), 3)) for i in idx]
def line(r, t):
    w, P = spec(r); m = np.abs(w - t) <= resw; at = P[m].max(); fl = P[(w >= 5) & (w <= 15) & (np.abs(w - t) > 1)]
    return round(float(at/np.percentile(fl, 95)), 2)
out = {"baseline_corr_P101": round(base, 4), "only": {}, "minus": {}}
for kind in ("only", "minus"):
    for p in (2, 3, 5, 7, 11, 13):
        xp, lp = load(f"r96_pzeros_{kind}_{p}.jsonl"); assert np.allclose(xp, x); rp = res(lp)
        c = float(np.corrcoef(rp, rt)[0, 1])
        out[kind][p] = dict(corr_true=round(c, 3), rms_ratio=round(float(rp.std()/rt.std()), 3), top_lines=top(rp), line_9075=line(rp, 9.075))
        if kind == "minus": out[kind][p]["drop"] = round(base - c, 3)
D = {p: out["minus"][p]["drop"] for p in out["minus"]}
out["D7"] = bool(max(D, key=D.get) == 7 and D[7] >= 1.5*D[5] and D[7] >= 1.5*D[11])
w2 = out["only"][2]["top_lines"][0][0]; F = {}
for p in (3, 5, 7, 11, 13):
    pred = w2*np.log(p)/np.log(2); got = out["only"][p]["top_lines"][0][0]
    F[p] = dict(predicted=round(float(pred), 2), strongest=got, hit=bool(abs(got - pred) <= resw),
                any_top4=bool(any(abs(l - pred) <= resw for l, _ in out["only"][p]["top_lines"])))
out["F_detail"] = F; out["F"] = bool(sum(v["hit"] for v in F.values()) >= 4); out["drop_ranking"] = sorted(D, key=D.get, reverse=True)
print(json.dumps(out, indent=1))
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
