#!/usr/bin/env python3
"""Round 103: score PREREG_tonesprimes.md."""
import sys, json, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
def top(f, lo=4, hi=45):
    w, Y, r = spectrum(f); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])
    return [round(float(ws[i]), 2) for i in loc[:3]]
target = {"1.1": 9.29, "1.5": 16.75, "2.1": 23.56, "2.6": 30.14, "3.0": 36.69, "3.4": 42.97}
out = {}
for T in ("Q2", "Q3", "Q23", "Q235", "A"):
    pre = "r102_" if T == "A" else "r103_"; rows = {}
    for b, t in target.items():
        p = top(f"{pre}{T}_{b}.jsonl"); rows[b] = dict(expected=t, peaks=p, hit=bool(abs(p[0] - t) <= 0.3))
    out[T] = rows; out[T + "_hits"] = sum(v["hit"] for v in rows.values())
out["T23"] = out["Q23_hits"] >= 5; out["T2"] = out["Q2_hits"] <= 3; out["T3"] = out["Q3_hits"] <= 3
out["minimal_full_set"] = next((T for T in ("Q2", "Q3", "Q23", "Q235", "A") if out[T + "_hits"] == 6), None)
for k, v in out.items(): print(k, v)
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
