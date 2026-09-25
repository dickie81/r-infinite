#!/usr/bin/env python3
"""Round 100: score PREREG_ladder.md from r100_*.jsonl."""
import sys, json, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
def top2(w, Y, lo=4, hi=35):
    s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc[:2]]
wt, Yt, rt = spectrum("r95_true.jsonl"); rows = []
for j in range(16):
    w, Y, r = spectrum(f"r100_{j}.jsonl"); t = top2(w, Y)
    rows.append(dict(band=[round(0.9 + 0.1*j, 1), round(1.0 + 0.1*j, 1)], r=round(0.95 + 0.1*j, 2), omega=t[0][0], second=t[1] if len(t) > 1 else None,
                     rms_ratio=round(float(r.std()/rt.std()), 3), corr_true=round(float(np.corrcoef(r, rt)[0, 1]), 3), linresp_p2=round(0.95*0 + 4*np.pi*np.log(2)*(0.95 + 0.1*j), 2)))
R = np.array([x["r"] for x in rows]); W = np.array([x["omega"] for x in rows])
c = np.polyfit(R, W, 1); rmsres = float(np.std(W - np.polyval(c, R))); maxjump = float(np.max(np.abs(np.diff(W))))
LIN = bool(rmsres <= 0.6 and maxjump <= 3)
fam = np.array([9.42, 16.75, 23.6]); sel = R >= 1.0
assign = [int(np.argmin(abs(fam - w))) if np.min(abs(fam - w)) <= 0.6 else -1 for w in W[sel]]
runs_ok = all(a >= 0 for a in assign) and all(b >= a for a, b in zip(assign, assign[1:])) and all(assign.count(v) >= 2 for v in set(assign))
STAIR = bool(runs_ok)
out = dict(rows=rows, linear_fit=[round(float(c[0]), 3), round(float(c[1]), 3)], linear_rms_residual=round(rmsres, 3), max_adjacent_jump=round(maxjump, 2),
           LIN=LIN, stair_assignment=assign, STAIR=STAIR)
for x in rows: print(x)
for k in ("linear_fit", "linear_rms_residual", "max_adjacent_jump", "LIN", "stair_assignment", "STAIR"): print(k, out[k])
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
