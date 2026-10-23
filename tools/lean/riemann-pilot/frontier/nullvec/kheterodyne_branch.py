#!/usr/bin/env python3
"""Round 107, POST HOC variant (not registered): kappa restricted to the branch [ln x - 0.5, ln x + 1]. Model kernels M1 (smooth) and M2 (smooth + one wave beyond the edge) from the
round-106 kernel dumps; per-prime first-order responses and their strongest tones."""
import json, glob, numpy as np
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
R = {}
for f in glob.glob("r106_*.jsonl"):
    for l in open(f): o = json.loads(l); R[o["x"]] = o
x = np.array(sorted(R)); q = np.array(json.load(open("pzeros_0.json"))); rho = np.log(q/(2*np.pi))/(2*np.pi)
re = np.array(json.load(open("ktonederive_results.json"))["r_e"])
spacing = 1/rho
def gsmooth(v, g, mask):
    out = np.zeros_like(v); idx = np.where(mask)[0]
    for i in idx:
        wts = np.exp(-0.5*((g[idx] - g[i])/(3*spacing[i]))**2); out[i] = np.sum(wts*v[idx])/np.sum(wts)
    return out
W, M1, M2, KAP, FRAC = [], [], [], [], []
kap = np.linspace(0.2, 5, 2401)
for i, xv in enumerate(x):
    w = np.array(R[xv]["w"]); r = q/(4*np.pi*xv); ins = r < re[i]; out = ~ins
    s = gsmooth(w, q, ins) + gsmooth(w, q, out); osc = w - s
    beyond = out & (r <= 2.2); env = np.sqrt(2)*gsmooth(np.abs(osc), q, out)
    g = q[beyond]; e = env[beyond]; o = osc[beyond]
    kk = kap[(kap > np.log(xv) - 0.5) & (kap < np.log(xv) + 1.0)]; A = np.abs((np.exp(1j*np.outer(kk, g))*e) @ o); k = kk[np.argmax(A)]
    X = np.vstack([e*np.cos(k*g), e*np.sin(k*g)]).T; c, *_ = np.linalg.lstsq(X, o, rcond=None)
    wave = np.zeros_like(w); wave[out] = env[out]*(c[0]*np.cos(k*q[out]) + c[1]*np.sin(k*q[out]))
    frac = 1 - np.sum((o - X @ c)**2)/np.sum(o**2)
    W.append(w); M1.append(s); M2.append(s + wave); KAP.append(k); FRAC.append(frac)
W, M1, M2 = map(np.array, (W, M1, M2))
def Sp(g, p): return -np.imag(np.log(1 - p**(-0.5 - 1j*g)))/np.pi
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
def peaks(y, lo=1.5, hi=40, n=3):
    rr = res(y); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]
out = {"kappa_minus_lnx": [round(float(k - np.log(v)), 3) for k, v in zip(KAP, x)][::25], "wave_variance_fraction_mean": round(float(np.mean(FRAC)), 3)}
ref = {2: 9.47, 3: 16.75}; ok = {}
for name, K in (("true", W), ("M1", M1), ("M2", M2)):
    for p in (2, 3):
        pk = peaks(-K @ (Sp(q, p)/rho)); out[f"{name}_p{p}"] = pk; ok[(name, p)] = abs(pk[0][0] - ref[p]) <= 0.3
        print(f"{name:4s} p={p}: {pk}")
out["HET_a"] = bool(ok[("M2", 2)] and ok[("M2", 3)]); out["HET_b"] = bool(not (ok[("M1", 2)] and ok[("M1", 3)])); out["HET"] = out["HET_a"] and out["HET_b"]
print("kappa - ln x (every 25th window):", out["kappa_minus_lnx"], "| single-wave variance fraction:", out["wave_variance_fraction_mean"])
print("HET (a):", out["HET_a"], " (b):", out["HET_b"], " -> HET", out["HET"])
json.dump(out, open("kheterodyne_branch_results.json", "w"), indent=1)
