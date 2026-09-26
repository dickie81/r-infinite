#!/usr/bin/env python3
"""Round 95: prime-truncated zero sets. Solutions of theta(t)/pi + 1 + S_P(t) = k - 1/2 (all crossings, t < 1000),
S_P(t) = -(1/pi) sum_{p <= P} Im log(1 - p^{-1/2 - it}). Writes pzeros_P.json for each P in argv."""
import sys, json, numpy as np, mpmath as mp
from sympy import primerange
t = np.arange(1.0, 1000.0, 0.001)
theta = np.array([float(mp.siegeltheta(x)) for x in t[::100]]); theta = np.interp(t, t[::100], theta)  # smooth, 0.1-spaced samples
Zt = np.array(json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json"))); Zt = Zt[Zt < 1000]
for P in map(int, sys.argv[1:]):
    S = np.zeros_like(t)
    for p in primerange(2, P + 1): S -= np.imag(np.log(1 - p**(-0.5 - 1j*t)))/np.pi
    Nf = theta/np.pi + 1 + S - 0.5
    k = np.floor(Nf); idx = np.where(np.diff(k) != 0)[0]
    Z = [float(t[i] + (t[i + 1] - t[i])*((max(k[i], k[i + 1]) - Nf[i])/(Nf[i + 1] - Nf[i]))) for i in idx]
    json.dump(Z, open(f"pzeros_{P}.json", "w"))
    m = min(len(Z), len(Zt)); up = int(np.sum(np.diff(k)[idx] > 0))
    print(P, "zeros", len(Z), "(up", up, ") true", len(Zt), " mean|dev| vs true (index-matched)", round(float(np.mean(abs(np.array(Z[:m]) - Zt[:m]))), 3))
