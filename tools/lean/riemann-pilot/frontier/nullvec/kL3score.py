#!/usr/bin/env python3
"""Round 112: score the chi_-3 part of PREREG_Lwide.md (narrow-method prediction p = 2 -> 3.22)."""
import json, glob, numpy as np
from sympy import primerange
def lx(pat, key):
    r = {}
    for f in glob.glob(pat):
        for l in open(f):
            if l.strip(): o = json.loads(l); r[o["x"]] = o
    return r
T = lx("rL3_true_*.jsonl", 0); Bs = lx("rL3_base_*.jsonl", 0); K = lx("L3106_*.jsonl", 0)
x = np.array(sorted(T)); assert len(x) == 226 and all(v in Bs and v in K for v in x)
lt = np.array([float(T[v]["lnK00"]) for v in x]); lb = np.array([float(Bs[v]["lnK00"]) for v in x])
q = np.array(json.load(open("L3quant.json"))); W = np.array([K[v]["w"] for v in x]); q = q[:W.shape[1]]
Z = np.array(json.load(open("L3zeros.json")))[:W.shape[1]]
rho = np.log(3*q/(2*np.pi))/(2*np.pi)
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
def peaks(y, lo=1.5, hi=40, n=4):
    rr = res(y); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]
def chi(p): return 0 if p == 3 else (1 if p % 3 == 1 else -1)
def Sp(g, p): return -np.imag(np.log(1 - chi(p)*p**(-0.5 - 1j*g)))/np.pi
out = {}
d1 = W @ (Z - q); act = lt - lb
out["first_order_vs_actual_corr"] = round(float(np.corrcoef(res(d1), res(act))[0, 1]), 3)
out["L_chain_lines"] = peaks(lt); out["L_chain_minus_base_lines"] = peaks(act); out["first_order_total_lines"] = peaks(d1)
per = {}
for p in (2, 5, 7, 11, 13):
    per[p] = peaks(-W @ (Sp(q, p)/rho)); print(f"p={p} (chi={chi(p):+d}) first-order lines: {per[p]}")
out["per_prime"] = per
single = abs(per[2][0][0] - 3.22) <= 0.5; L3 = all(abs(w - 16.75) > 0.5 for w, _ in out["L_chain_lines"][:3])
L2 = [(w, abs(w - 3.22) <= 0.5) for w, _ in out["L_chain_lines"][:2]]
out.update(single_prime_check=bool(single), L3=bool(L3), L2=L2)
print("first order vs actual (L chain - base) residual corr:", out["first_order_vs_actual_corr"])
print("L chain lines:", out["L_chain_lines"]); print("L chain - base lines:", out["L_chain_minus_base_lines"]); print("first-order total lines:", out["first_order_total_lines"])
print("single-prime check (p=2 strongest within 0.5 of 3.22):", single, "| zeta p=3 line 16.75 absent from top 3:", L3, "| L2:", L2)
json.dump(out, open("kL3score_results.json", "w"), indent=1)
