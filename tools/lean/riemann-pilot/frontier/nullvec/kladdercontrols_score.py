#!/usr/bin/env python3
"""Round 102: score C and D of PREREG_laddercontrols.md (S is in kladder_S_results.json)."""
import sys, json, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
def top(f, lo=4, hi=45):
    w, Y, r = spectrum(f); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])
    return [round(float(ws[i]), 2) for i in loc[:3]]
target = {"1.1": 9.29, "1.5": 16.75, "2.1": 23.56, "2.6": 30.14, "3.0": 36.69, "3.4": 42.97}
out = {}
for T in ("W", "A"):
    rows = {}
    for b, t in target.items():
        p = top(f"r102_{T}_{b}.jsonl"); rows[b] = dict(expected=t, peaks=p, hit=bool(abs(p[0] - t) <= 0.6))
    out[T] = rows; out[T + "_hits"] = sum(v["hit"] for v in rows.values())
out["C_ARTEFACT"] = out["W_hits"] >= 4; out["C_ARITH"] = out["W_hits"] <= 1; out["D_UNIVERSAL"] = out["A_hits"] >= 4
out["S"] = json.load(open("kladder_S_results.json"))["S"]
for k, v in out.items(): print(k, v)
if len(sys.argv) > 1: json.dump(out, open(sys.argv[1], "w"), indent=1)
