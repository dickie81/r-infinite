#!/usr/bin/env python3
"""Round 119: score PREREG_counterexample.md from rCT_*.jsonl."""
import json, glob, math, numpy as np
R = [json.loads(l) for f in glob.glob("rCT_*.jsonl") for l in open(f) if l.strip()]
und = [r for r in R if r.get("status") == "UNDECIDED"]; R = [r for r in R if r.get("status") in ("PD", "LOST")]
xh = lambda g0: g0/(4*math.pi*0.8613)
out = {"undecided": len(und), "cases": {}}
S1 = S2 = S3 = True; S4r = []
for n in sorted({r["n"] for r in R}):
    g0 = [r["g0"] for r in R if r["n"] == n][0]; xc = {}
    for d in sorted({r["delta"] for r in R if r["n"] == n}, key=float):
        rows = sorted([r for r in R if r["n"] == n and r["delta"] == d], key=lambda r: r["x"])
        lost = [r["x"] for r in rows if r["status"] == "LOST"]; xc[d] = min(lost) if lost else None
        if any(x < 0.9*xh(g0) for x in lost): S1 = False
        if 1.3*xh(g0) <= 12 and not (xc[d] is not None and xc[d] <= 1.3*xh(g0)): S2 = False
        for r in rows:
            if r["status"] == "PD" and r["x"] < 0.9*xh(g0) and r["dlnK_first"] and abs(r["dlnK_exact"]) > 1e-12:
                S4r.append(r["dlnK_first"]/r["dlnK_exact"])
        out["cases"][f"n={n} g0={g0:.2f} x_h={xh(g0):.2f} delta={d}"] = {"x_c": xc[d], "x_c/x_h": round(xc[d]/xh(g0), 3) if xc[d] else None,
            "lost_windows": len(lost), "pd_windows": len(rows) - len(lost)}
    ds = sorted(xc, key=float)
    vals = [xc[d] if xc[d] is not None else 99 for d in ds]
    if any(vals[i + 1] > vals[i] for i in range(len(vals) - 1)): S3 = False
S4r = np.array(S4r)
out.update(S1_no_loss_below_0p9xh=S1, S2_loss_by_1p3xh=S2, S3_xc_nonincreasing_in_delta=S3,
           S4_first_order_ratio_outside_horizon={"n": int(len(S4r)), "median": round(float(np.median(S4r)), 3) if len(S4r) else None,
           "frac_within_20pct": round(float(np.mean(abs(S4r - 1) <= 0.2)), 3) if len(S4r) else None})
for k, v in out.items(): print(k, ":", json.dumps(v, indent=1) if isinstance(v, dict) else v)
json.dump(out, open("kcounter_score_results.json", "w"), indent=1)
