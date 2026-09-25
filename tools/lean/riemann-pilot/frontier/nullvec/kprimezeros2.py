#!/usr/bin/env python3
"""Round 96: zero sets from a chosen prime set Q: theta(t)/pi + 1 + S_Q(t) = k - 1/2 (t < 1000),
S_Q(t) = -(1/pi) sum_{p in Q} Im log(1 - p^{-1/2 - it}). Specs: 'only:p', 'minus:p' or 'set:p1,p2,..' (round 103) (primes <= 101 without p).
Writes pzeros_<spec>.json."""
import sys, json, numpy as np, mpmath as mp
from sympy import primerange
t = np.arange(1.0, 1000.0, 0.001)
theta = np.interp(t, t[::100], np.array([float(mp.siegeltheta(x)) for x in t[::100]]))
Zt = np.array(json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json"))); Zt = Zt[Zt < 1000]
for spec in sys.argv[1:]:
    kind, p = spec.split(":"); p = int(p.split(",")[0])
    Q = [p] if kind == "only" else ([int(v) for v in spec.split(":")[1].split(",")] if kind == "set" else [q for q in primerange(2, 102) if q != p])
    S = np.zeros_like(t)
    for q in Q: S -= np.imag(np.log(1 - q**(-0.5 - 1j*t)))/np.pi
    Nf = theta/np.pi + 1 + S - 0.5; k = np.floor(Nf); idx = np.where(np.diff(k) != 0)[0]
    Z = [float(t[i] + (t[i + 1] - t[i])*((max(k[i], k[i + 1]) - Nf[i])/(Nf[i + 1] - Nf[i]))) for i in idx]
    Z = [z for z in Z if z >= 10]   # crossings below t = 10 (smooth N < 1/2 there) are scan-start artefacts
    name = spec.replace(":", "_").replace(",", "-"); json.dump(Z, open(f"pzeros_{name}.json", "w")); m = min(len(Z), len(Zt))
    print(spec, "zeros", len(Z), "down-crossings", int(np.sum(np.diff(k)[idx] < 0)), "mean|dev|", round(float(np.mean(abs(np.array(Z[:m]) - Zt[:m]))), 3))
