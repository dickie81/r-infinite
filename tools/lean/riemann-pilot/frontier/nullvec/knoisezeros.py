#!/usr/bin/env python3
"""Round 97: noise-driven zero sets below t = 1000. N1: smooth quantiles + iid Gaussian jitter (sd 0.383), re-sorted.
N2: theta/pi + 1 + S_rand = k - 1/2 with S_rand the p <= 101 Euler sum with iid uniform phases (all crossings, t >= 10).
Writes pzeros_N1_s<seed>.json, pzeros_N2_s<seed>.json for seeds 1..4."""
import json, numpy as np, mpmath as mp
from sympy import primerange
q = json.load(open("pzeros_0.json"))                    # round 95: smooth quantiles below 1000
t = np.arange(1.0, 1000.0, 0.001)
theta = np.interp(t, t[::100], np.array([float(mp.siegeltheta(x)) for x in t[::100]]))
P = list(primerange(2, 102))
for seed in (1, 2, 3, 4):
    rng = np.random.default_rng(seed)
    z1 = np.sort(np.array(q) + rng.normal(0, 0.383, len(q))); z1 = z1[(z1 >= 10) & (z1 < 1000)]
    json.dump([float(v) for v in z1], open(f"pzeros_N1_s{seed}.json", "w"))
    ph = rng.uniform(0, 2*np.pi, len(P)); S = np.zeros_like(t)
    for p, f in zip(P, ph): S -= np.imag(np.log(1 - p**-0.5*np.exp(-1j*(t*np.log(p) + f))))/np.pi
    Nf = theta/np.pi + 1 + S - 0.5; k = np.floor(Nf); idx = np.where(np.diff(k) != 0)[0]
    z2 = [float(t[i] + (t[i + 1] - t[i])*((max(k[i], k[i + 1]) - Nf[i])/(Nf[i + 1] - Nf[i]))) for i in idx]
    z2 = [v for v in z2 if v >= 10]; json.dump(z2, open(f"pzeros_N2_s{seed}.json", "w"))
    print(seed, "N1", len(z1), "mean|dev|", round(float(np.mean(abs(z1 - np.array(q)[:len(z1)]))), 3) if len(z1) == len(q) else len(z1), "| N2", len(z2), "down", int(np.sum(np.diff(k)[idx] < 0)), "min spacing", round(float(np.min(np.diff(z2))), 3))
