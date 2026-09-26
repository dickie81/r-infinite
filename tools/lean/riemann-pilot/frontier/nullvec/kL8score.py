#!/usr/bin/env python3
"""Round 115: score PREREG_L8law.md -- blind test of the parameter-free tone law omega_p = 2 pi (p - 1/p)/q on L(s, chi_-8).
Written and committed before any chi_-8 zero, kernel, chain or response exists. Same peak finder and pipeline as kL3score.py."""
import json, glob, numpy as np
Q = 8; TOL = 0.3
def lx(pat):
    r = {}
    for f in glob.glob(pat):
        for l in open(f):
            if l.strip(): o = json.loads(l); r[o["x"]] = o
    return r
T = lx("rL8_true_*.jsonl"); Bs = lx("rL8_base_*.jsonl"); K = lx("L8106_*.jsonl")
x = np.array(sorted(T)); assert len(x) == 226 and all(v in Bs and v in K for v in x)
lt = np.array([float(T[v]["lnK00"]) for v in x]); lb = np.array([float(Bs[v]["lnK00"]) for v in x])
q = np.array(json.load(open("L8quant.json"))); W = np.array([K[v]["w"] for v in x]); q = q[:W.shape[1]]
Z = np.array(json.load(open("L8zeros.json")))[:W.shape[1]]
rho = np.log(Q*q/(2*np.pi))/(2*np.pi)
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
def peaks(y, lo=1.5, hi=40, n=4):
    rr = res(y); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]
def chi(p): return 0 if p == 2 else (1 if p % 8 in (1, 3) else -1)
def Sp(g, p): return -np.imag(np.log(1 - chi(p)*p**(-0.5 - 1j*g)))/np.pi
law = lambda n: 2*np.pi*(n - 1/n)/Q
out = {"law": {p: round(law(p), 3) for p in (3, 5, 7, 11, 13)}}
d1 = W @ (Z - q); act = lt - lb
out["first_order_vs_actual_corr"] = round(float(np.corrcoef(res(d1), res(act))[0, 1]), 3)
out["L8_chain_lines"] = peaks(lt); out["L8_chain_minus_base_lines"] = peaks(act); out["first_order_total_lines"] = peaks(d1)
per, hit = {}, {}
for p in (3, 5, 7, 11, 13):
    per[p] = peaks(-W @ (Sp(q, p)/rho)); hit[p] = bool(abs(per[p][0][0] - law(p)) <= TOL)
    print(f"p={p} (chi={chi(p):+d}) law {law(p):.3f} | first-order lines {per[p]} | hit {hit[p]}")
out["per_prime"] = per; out["per_prime_hit"] = hit
B1 = hit[3] and hit[5]; B2 = abs(out["L8_chain_lines"][0][0] - law(3)) <= TOL; B3 = sum(hit[p] for p in (7, 11, 13))
lawset = [law(n) for n in (3, 5, 7, 9, 11, 13, 15)]
out["chain_top4_nearest_law_dist"] = [(w, round(float(min(abs(w - v) for v in lawset)), 2)) for w, _ in out["L8_chain_lines"]]
out.update(B1=bool(B1), B2=bool(B2), B3_hits_of_3=int(B3), PASS=bool(B1 and B2))
print("first order vs actual residual corr:", out["first_order_vs_actual_corr"])
print("L8 chain lines:", out["L8_chain_lines"]); print("L8 chain - base lines:", out["L8_chain_minus_base_lines"]); print("first-order total:", out["first_order_total_lines"])
print("chain top-4 distance to nearest law line (unscored):", out["chain_top4_nearest_law_dist"])
print(f"B1 (p=3 and p=5 per-prime hits): {B1} | B2 (chain strongest within {TOL} of {law(3):.3f}): {B2} | B3 far primes hit: {B3}/3 | PASS: {B1 and B2}")
json.dump(out, open("kL8score_results.json", "w"), indent=1)
