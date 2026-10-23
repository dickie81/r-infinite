#!/usr/bin/env python3
"""Round 94: zeros of the octonion superposition G(t) = Xi(t + 3i/2) + Xi(t - 3i/2) = 2 Re xi(2 + it):
the solutions of arg xi(2 + it) = pi/2 + k pi (continuous argument). zeta(2 + it) by its absolutely convergent series
(N = 20000 terms + Euler-Maclaurin tail). Writes superposed_zeros.json (first 6700) and a check against mpmath."""
import json, numpy as np, mpmath as mp
from scipy.special import loggamma
N = 20000; n = np.arange(1, N + 1, dtype=float); ln = np.log(n); w = n**-2.0
def zeta2(t):
    t = np.atleast_1d(np.asarray(t, float)); s = 2 + 1j*t; out = np.empty(len(t), complex)
    for i in range(0, len(t), 500):
        tt = t[i:i + 500]; out[i:i + 500] = np.exp(-1j*np.outer(tt, ln)) @ w
    return out + N**(1 - s)/(s - 1) - N**(-s)/2
def argxi(t):
    s = 2 + 1j*np.atleast_1d(np.asarray(t, float))
    return np.imag(np.log(s) + np.log(s - 1) - s/2*np.log(np.pi) + loggamma(s/2) + np.log(zeta2(t)))
for t in (14.0, 3000.0, 7000.0):
    print("zeta check", t, abs(complex(mp.zeta(mp.mpc(2, t))) - zeta2(t)[0]))
ts = np.arange(0.01, 7200.0, 0.02); ph = np.unwrap(argxi(ts))
k = np.floor((ph - np.pi/2)/np.pi); idx = np.where(np.diff(k) != 0)[0]
# vectorised bisection on the continuous phase for all crossings at once
tg = np.pi/2 + np.maximum(k[idx], k[idx + 1])*np.pi; base = ph[idx] - argxi(ts[idx]); a, b = ts[idx].copy(), ts[idx + 1].copy()
for _ in range(40):
    m = (a + b)/2; f = argxi(m) + base - tg; lo = f < 0; a = np.where(lo, m, a); b = np.where(lo, b, m)
Z = list(((a + b)/2)[:6700]); json.dump(Z, open("superposed_zeros.json", "w"))
zt = json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json"))
print(len(Z), [round(z, 3) for z in Z[:8]], round(Z[-1], 2), "vs zeta", round(zt[-1], 2), "phase monotone:", bool(np.all(np.diff(ph) > 0)))
