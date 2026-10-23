#!/usr/bin/env python3
"""Round 105 A: score the third-order part of PREREG_linresp3.md on x in [3, 12]."""
import json, glob, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
R = {}
for f in glob.glob("r105A_*.jsonl"):
    for l in open(f): o = json.loads(l); R[o["x"]] = o
x = np.array(sorted(R)); assert len(x) == 226
_, lt = load("r95_true.jsonl"); _, l0 = load("r95_pzeros_0.jsonl"); _, l7 = load("r95_pzeros_7.jsonl")
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
out = {}
for nm, la in (("true", lt), ("P7", l7)):
    act = la - l0
    for o in ("d1", "d2", "d3"):
        pr = np.array([R[v][f"{o}_{nm}"] for v in x])
        out[f"{o}_{nm}"] = dict(corr=round(float(np.corrcoef(res(pr), res(act))[0, 1]), 4), rms_ratio=round(float(res(pr).std()/res(act).std()), 3),
                               raw_max_err=round(float(np.max(abs(pr - act))), 4), raw_rms_err=round(float(np.std(pr - act)), 4))
        print(o, nm, out[f"{o}_{nm}"])
c3 = out["d3_true"]["corr"]; out["A_verdict"] = "PERT" if (c3 >= 0.97 and out["d3_true"]["raw_max_err"] < 0.080) else ("NONPERT" if c3 <= 0.945 else "partial")
print("A verdict:", out["A_verdict"]); json.dump(out, open("klinresp3_A_results.json", "w"), indent=1)
