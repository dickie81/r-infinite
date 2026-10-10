"""Round 178 post-hoc (not pre-registered): does the planted tone appear in the floor?
Fit F(x)/x^{3/4} and D(x)/x^{3/4} on [1e5, 1e7] to a + b cos(5 log x) + c sin(5 log x)."""
import json, numpy as np
import kfakegears as K
out = {}
for name, sign in (("Z1", -1), ("P1", +1)):
    N, th = K.build(K.plant_gears(sign))
    x = np.arange(K.X + 1, dtype=float)
    s = np.unique(np.geomspace(10**5, K.X, 4000).astype(int))
    A = float(np.sum(N[s] * x[s]) / np.sum(x[s]**2))
    F, D = (N - A * x)[s] / x[s]**0.75, (th - x)[s] / x[s]**0.75
    M = np.c_[np.ones(s.size), np.cos(5 * np.log(x[s])), np.sin(5 * np.log(x[s]))]
    r = {}
    for lab, y in (("floor", F), ("drift", D)):
        c, *_ = np.linalg.lstsq(M, y, rcond=None)
        r[lab] = dict(tone_amp=float(np.hypot(c[1], c[2])), tone_phase=float(np.arctan2(-c[2], c[1])),
                      resid_rms=float(np.std(y - M @ c)))
    out[name] = r; print(name, json.dumps(r))
json.dump(out, open("kfakegears_posthoc.json", "w"), indent=1)

# Post-hoc 2: does the floor/drift tone ratio shrink like 1/log x (linear leakage) or stay fixed (a true x^{3/4} term)?
ranges = [(10**4, 10**5), (10**5, 10**6), (10**6, 10**7)]
out2 = {}
for name, sign in (("Z1", -1), ("P1", +1)):
    N, th = K.build(K.plant_gears(sign))
    x = np.arange(K.X + 1, dtype=float)
    s0 = np.unique(np.geomspace(10**5, K.X, 4000).astype(int))
    A = float(np.sum(N[s0] * x[s0]) / np.sum(x[s0]**2))
    rows = []
    for lo, hi in ranges:
        s = np.unique(np.geomspace(lo, hi, 3000).astype(int))
        M = np.c_[np.ones(s.size), np.cos(5 * np.log(x[s])), np.sin(5 * np.log(x[s]))]
        amp = []
        for y in ((N - A * x)[s] / x[s]**0.75, (th - x)[s] / x[s]**0.75):
            c, *_ = np.linalg.lstsq(M, y, rcond=None); amp.append(float(np.hypot(c[1], c[2])))
        lmid = float(np.log(np.sqrt(lo * hi)))
        rows.append(dict(range=[lo, hi], ratio=amp[0] / amp[1], ratio_times_logx=amp[0] / amp[1] * lmid))
    out2[name] = rows; print(name, json.dumps(rows))
json.dump({"tone_fit": out, "ratio_by_range": out2}, open("kfakegears_posthoc.json", "w"), indent=1)
