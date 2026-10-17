#!/usr/bin/env python3
"""Round 105 B: score the larger-window part of PREREG_linresp3.md."""
import json, glob, numpy as np
def loadx(pat, key="lnK00"):
    r = {}
    for f in glob.glob(pat):
        for l in open(f):
            if l.strip(): o = json.loads(l); r[o["x"]] = o
    return r
R = loadx("r105B_resp_*.jsonl"); Tt = loadx("r105B_true_*.jsonl"); Bb = loadx("r105B_base_*.jsonl")
x = np.array(sorted(R)); assert len(x) == 151 and all(v in Tt and v in Bb for v in x)
lt = np.array([float(Tt[v]["lnK00"]) for v in x]); l0 = np.array([float(Bb[v]["lnK00"]) for v in x]); base = np.array([float(R[v]["lnK_base"]) for v in x])
print("base check (response base vs Gamma chain): max diff", float(np.max(abs(base - l0))))
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
act = lt - l0; out = {"act_rms_resid": float(res(act).std())}
for o in ("d1", "d2", "d3"):
    pr = np.array([R[v][f"{o}_true"] for v in x])
    out[o] = dict(corr=round(float(np.corrcoef(res(pr), res(act))[0, 1]), 4), rms_ratio=round(float(res(pr).std()/res(act).std()), 3),
                  raw_max_err=round(float(np.max(abs(pr - act))), 4), raw_rms_err=round(float(np.std(pr - act)), 4)); print(o, out[o])
out["HOLDS"] = bool(out["d2"]["corr"] >= 0.9); c3 = out["d3"]["corr"]
out["third_order_verdict"] = "PERT" if (c3 >= 0.97 and out["d3"]["raw_max_err"] < 0.080) else ("NONPERT" if c3 <= 0.945 else "partial")
G = np.linspace(x[0], x[-1], 4096)
for lab, series in (("pred_d3", np.array([R[v]["d3_true"] for v in x])), ("act", act)):
    rr = res(series); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > 1.5) & (w < 25); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:5]
    out[f"tones_{lab}"] = sorted([(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]); print(lab, out[f"tones_{lab}"])
print("HOLDS", out["HOLDS"], "third order:", out["third_order_verdict"]); json.dump(out, open("klinresp3_B_results.json", "w"), indent=1)
