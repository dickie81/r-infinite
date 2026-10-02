#!/usr/bin/env python3
"""Round 108: score PREREG_chirp.md. M3 = smooth kernel + one chirped wave beyond the edge, fitted per window."""
import json, glob, numpy as np
from scipy.optimize import least_squares
src = open("kheterodyne.py").read()
exec(src.split("W, M1, M2, KAP, FRAC = [], [], [], [], []")[0])      # data, gsmooth, re, rho, q, x
def Sp(g, p): return -np.imag(np.log(1 - p**(-0.5 - 1j*g)))/np.pi
d = np.log(x); B = np.vstack([np.exp(d), d, np.ones_like(d), np.exp(-d)]).T; res = lambda y: y - B @ np.linalg.lstsq(B, y, rcond=None)[0]
def peaks(y, lo=1.5, hi=40, n=3):
    rr = res(y); G = np.linspace(x[0], x[-1], 4096); yy = np.interp(G, x, rr); yy = (yy - np.polyval(np.polyfit(G, yy, 3), G))*np.hanning(len(G))
    Y = np.abs(np.fft.rfft(yy, 16*len(G)))**2; w = 2*np.pi*np.fft.rfftfreq(16*len(G), G[1] - G[0]); s = (w > lo) & (w < hi); ws, Ps = w[s], Y[s]
    loc = sorted([i for i in range(1, len(Ps) - 1) if Ps[i] > Ps[i - 1] and Ps[i] > Ps[i + 1]], key=lambda i: -Ps[i])[:n]
    return [(round(float(ws[i]), 2), round(float(Ps[i]/Ps[loc[0]]), 2)) for i in loc]
def wave(par, g, xv, env):
    c0, c1, c2, ph, amp = par; L = 4*np.pi*xv; u = g - 1.4*L
    Psi = ph + (np.log(xv) + c0)*u + c1*u**2/(2*L) + c2*u**3/(3*L*L)   # kappa = ln x + c0 + c1 (r-1.4) + c2 (r-1.4)^2
    return amp*env*np.cos(Psi)
W, S, M3, PARS, FRAC = [], [], [], [], []
for i, xv in enumerate(x):
    w = np.array(R[xv]["w"]); r = q/(4*np.pi*xv); ins = r < re[i]; out = ~ins
    s = gsmooth(w, q, ins) + gsmooth(w, q, out); osc = w - s; env = np.sqrt(2)*gsmooth(np.abs(osc), q, out)
    b = out & (r <= 2.2); g, e, o = q[b], env[b], osc[b]; best = None
    for ph0 in np.linspace(0, 2*np.pi, 8, endpoint=False):
        f = least_squares(lambda p: wave(p, g, xv, e) - o, [0.33, 0.0, 0.0, ph0, 1.0], bounds=([-0.5, -3, -3, -20, 0], [1.2, 3, 3, 20, 3]))
        if best is None or f.cost < best.cost: best = f
    wv = np.zeros_like(w); wv[out] = wave(best.x, q[out], xv, env[out])
    W.append(w); S.append(s); M3.append(s + wv); PARS.append(best.x); FRAC.append(1 - 2*best.cost/np.sum(o**2))
W, S, M3, PARS = map(np.array, (W, S, M3, PARS))
perm = np.random.default_rng(0).permutation(len(x)); M3s = []
for i, xv in enumerate(x):   # control: parameters taken from another window
    r = q/(4*np.pi*xv); out = r >= re[i]; env = np.sqrt(2)*gsmooth(np.abs(W[i] - S[i]), q, out)
    wv = np.zeros_like(W[i]); wv[out] = wave(PARS[perm[i]], q[out], xv, env[out]); M3s.append(S[i] + wv)
M3s = np.array(M3s)
out = {"params_mean": [round(float(v), 3) for v in PARS.mean(0)], "params_sd": [round(float(v), 3) for v in PARS.std(0)], "var_captured_mean": round(float(np.mean(FRAC)), 3)}
ok = {}
for name, K in (("true", W), ("M3", M3), ("M3_shuffled", M3s)):
    for p, ref in ((2, 9.47), (3, 16.75)):
        pk = peaks(-K @ (Sp(q, p)/rho)); out[f"{name}_p{p}"] = pk; ok[(name, p)] = abs(pk[0][0] - ref) <= 0.3; print(f"{name:12s} p={p}: {pk}")
out["CHIRP"] = bool(ok[("M3", 2)] and ok[("M3", 3)]); out["control_same"] = bool(ok[("M3_shuffled", 2)] and ok[("M3_shuffled", 3)])
c = PARS.mean(0); out["kappa_minus_lnx_profile"] = {round(float(v), 2): round(float(c[0] + c[1]*(v - 1.4) + c[2]*(v - 1.4)**2), 3) for v in np.linspace(1.0, 2.2, 7)}
print("mean (c0,c1,c2,phi0,amp):", out["params_mean"], "sd:", out["params_sd"], "| variance captured:", out["var_captured_mean"])
print("kappa - ln x vs r:", out["kappa_minus_lnx_profile"]); print("CHIRP:", out["CHIRP"], "| shuffled control reproduces:", out["control_same"])
json.dump(out, open("kchirp_results.json", "w"), indent=1); np.save("kchirp_params.npy", np.column_stack([x, PARS]))
