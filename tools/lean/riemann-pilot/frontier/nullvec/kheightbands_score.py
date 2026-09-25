#!/usr/bin/env python3
"""Round 98: score PREREG_heightbands.md from r98_*.jsonl (round 97 scorer, band sets)."""
import sys, json, numpy as np
def load(f):
    r = {}
    for l in open(f):
        if l.strip(): o = json.loads(l); r[o["x"]] = float(o["lnK00"])
    x = np.array(sorted(r)); return x, np.array([r[k] for k in x])
def spectrum(f):
    x, l = load(f); d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T
    r = l - B @ np.linalg.lstsq(B, l, rcond=None)[0]
    G = np.linspace(x[0], x[-1], 4096); y = np.interp(G, x, r); y = (y - np.polyval(np.polyfit(G, y, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(y, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); return w, Y, r
def present(w, Y, target):
    s = (w > 1.5) & (w < 30); ws, Ps = w[s], Y[s]
    loc = [i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]]; top = max(Ps[i] for i in loc)
    near = [i for i in loc if abs(ws[i] - target) <= 0.3]
    if not near: return False, None
    i = max(near, key=lambda j: Ps[j]); fl = Y[(w >= target - 5) & (w <= target + 5) & (np.abs(w - target) > 1)]
    return bool(Ps[i] >= 0.3*top and Ps[i] > np.percentile(fl, 95)), round(float(ws[i]), 2)
def peaks(w, Y, n=5):
    s = (w > 1.5) & (w < 30); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return sorted([(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc])
wt, Yt, rt = spectrum("r95_true.jsonl"); out = {"true": dict(peaks=peaks(wt, Yt))}
for tgt in (9.42, 4.97, 16.75): out["true"][str(tgt)] = present(wt, Yt, tgt)[0]
for B in ("L", "U"):
    for H in (30, 50, 100, 200, 500):
        w, Y, r = spectrum(f"r98_pzeros_{B}{H}.jsonl")
        out[f"{B}{H}"] = dict(peaks=peaks(w, Y), rms_ratio=round(float(r.std()/rt.std()), 3), corr_true=round(float(np.corrcoef(r, rt)[0, 1]), 3),
                              **{str(t): present(w, Y, t)[0] for t in (9.42, 4.97, 16.75)})
out["LOW"] = bool(out["L50"]["9.42"] and out["L50"]["corr_true"] >= 0.7 and not out["U50"]["9.42"])
out["EDGE"] = bool((not out["L100"]["9.42"]) and out["L200"]["9.42"] and out["U30"]["9.42"])
for k, v in out.items(): print(k, v)
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
