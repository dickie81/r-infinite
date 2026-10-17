#!/usr/bin/env python3
"""Round 106: score PREREG_tonederive.md from the kernel dumps r106_*.jsonl."""
import json, glob, numpy as np
from sympy import primerange
from scipy.special import loggamma
exec(open("kresonator_score.py").read().split("wt, Yt, rt = ")[0])
R = {}
for f in glob.glob("r106_*.jsonl"):
    for l in open(f): o = json.loads(l); R[o["x"]] = o
x = np.array(sorted(R)); assert len(x) == 226
q = np.array(json.load(open("pzeros_0.json"))); T = np.array([g for g in json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json")) if g < 1000])
W = np.array([R[v]["w"] for v in x]); Gm = np.array([R[v]["g"] for v in x])
# E1: r_e(x) where g = F'^2/s crosses 1 (log-linear interpolation), scanning upward in height
re = []
for i, v in enumerate(x):
    lg = np.log10(np.abs(Gm[i]) + 1e-300); r = q/(4*np.pi*v); j = np.where((lg[:-1] > 0) & (lg[1:] <= 0))[0]
    j = j[0] if len(j) else None
    re.append(float(r[j] + (r[j + 1] - r[j])*(lg[j]/(lg[j] - lg[j + 1]))) if j is not None else np.nan)
re = np.array(re); rbar = float(np.nanmean(re))
print(f"E1: r_e mean {rbar:.4f}, sd {np.nanstd(re):.4f}, range [{np.nanmin(re):.3f}, {np.nanmax(re):.3f}]  -> {'PASS' if np.nanstd(re) < 0.05 else 'FAIL'}")
rho = np.log(q/(2*np.pi))/(2*np.pi)
def Sp(g, p): return -np.imag(np.log(1 - p**(-0.5 - 1j*g)))/np.pi
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
def peaks(y, lo=1.5, hi=40, n=4):
    rr = res(y); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]
d1_exact = W @ (T - q)
lin_all = -W @ (sum(Sp(q, p) for p in primerange(2, 102))/rho)
print("linearised S_{<=101} vs exact first order: corr", round(float(np.corrcoef(res(lin_all), res(d1_exact))[0, 1]), 3))
out = dict(r_e=re.tolist(), rbar=rbar, E1=bool(np.nanstd(re) < 0.05), per_prime={})
hits = 0
for p in (2, 3, 5, 7):
    Dp = -W @ (Sp(q, p)/rho); pk = peaks(Dp); pred = 4*np.pi*rbar*np.log(p); hit = abs(pk[0][0] - pred) <= 0.5; hits += hit
    out["per_prime"][p] = dict(predicted=round(pred, 2), peaks=pk, hit=bool(hit)); print(f"p={p}: predicted 4 pi r_e ln p = {pred:.2f}; per-prime first-order lines {pk} -> {'hit' if hit else 'miss'}")
out["E2"] = bool(hits >= 3); main = 9.42; out["E3"] = bool(abs(4*np.pi*rbar*np.log(2) - main) <= 0.5)
print("E2", out["E2"], f"({hits}/4)", "| E3", out["E3"], f"(4 pi r_e ln 2 = {4*np.pi*rbar*np.log(2):.2f} vs 9.42)")
print("first-order total lines:", peaks(d1_exact))
json.dump(out, open("ktonederive_results.json", "w"), indent=1)
