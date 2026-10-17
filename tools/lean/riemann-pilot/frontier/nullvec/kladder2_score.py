#!/usr/bin/env python3
"""Round 101: score PREREG_ladder2.md from r101_*.jsonl."""
import sys, json, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
def top2(w, Y, lo=4, hi=45):
    s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc[:3]]
rows = []
for j in range(10):
    w, Y, r = spectrum(f"r101_{j}.jsonl"); t = top2(w, Y)
    rows.append(dict(r=round(2.55 + 0.1*j, 2), omega=t[0][0], second=t[1], third=t[2], rms=round(float(r.std()), 4)))
W = [x["omega"] for x in rows]; S = [x["second"][0] for x in rows]
in4 = [29.0 <= w <= 31.0 for w in W]
runs4 = max((sum(1 for _ in g) for k, g in __import__("itertools").groupby(in4) if k), default=0); P4 = runs4 >= 2
f5 = [(35.5 <= W[i] <= 38.5) or (35.5 <= S[i] <= 38.5) for i in range(10)]
first4 = next((i for i, v in enumerate(in4) if v), None); first5 = next((i for i, v in enumerate(f5) if v), None)
P5 = bool(sum(f5) >= 2 and first4 is not None and first5 is not None and first5 > first4)
rungs = np.array([23.4, 30.0, 37.0]); assign = [int(np.argmin(abs(rungs - w))) for w in W]
ORDER = all(b >= a for a, b in zip(assign, assign[1:]))
out = dict(rows=rows, P4=bool(P4), P4_run=runs4, P5=P5, fifth_bands=[rows[i]["r"] for i in range(10) if f5[i]], assign=assign, ORDER=bool(ORDER), CONTINUES=bool(P4 and P5 and ORDER))
for x in rows: print(x)
for k in ("P4", "P4_run", "P5", "fifth_bands", "assign", "ORDER", "CONTINUES"): print(k, out[k])
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
