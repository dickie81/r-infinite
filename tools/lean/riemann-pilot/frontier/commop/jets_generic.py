#!/usr/bin/env python3
"""Gram-Schmidt of the jets of an even function f on [-a,a] (mpmath), same output format as phijets.py.
which = 'cosh': f = exp(-2 pi cosh 2t);  'phi1': the n=1 term of Riemann's kernel made even:
f = e^{t/2}(2q^2 - 3q)e^{-q}, q = pi e^{2t}, for t>=0 mirrored (not smooth at 0: excluded); 'sech': sech(t)^6."""
import sympy as sp, mpmath as mp, numpy as np, sys, pickle
from numpy.polynomial.legendre import leggauss
mp.mp.dps = 60
which, a, M, n = sys.argv[1], float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
T = sp.symbols('t')
f = {"cosh": sp.exp(-2*sp.pi*sp.cosh(2*T)), "sech": sp.sech(T)**6,
     "gauss4": sp.exp(-T**4)}[which]
ders = [f]
for k in range(M + 1): ders.append(sp.simplify(sp.diff(ders[-1], T)) if k < 6 else sp.diff(ders[-1], T))
fn = [sp.lambdify(T, d, "mpmath") for d in ders]
x, w = leggauss(n); t = a*x; w = a*w
F = [[fn[m](mp.mpf(float(tt))) for tt in t] for m in range(M + 1)]
wm = [mp.mpf(float(x_)) for x_ in w]
ip = lambda f_, g: mp.fsum(wi*fi*gi for wi, fi, gi in zip(wm, f_, g))
out = {"a": a, "t": t, "w": w}
for par in (0, 1):
    ks = [k for k in range(M) if k % 2 == par]; Vs, dVs = [], []
    for k in ks:
        v, dv = list(F[k]), list(F[k + 1])
        for _ in range(2):
            for (u, du) in zip(Vs, dVs):
                c = ip(v, u); v = [vi - c*ui for vi, ui in zip(v, u)]; dv = [di - c*ui for di, ui in zip(dv, du)]
        nr = mp.sqrt(ip(v, v)); Vs.append([vi/nr for vi in v]); dVs.append([di/nr for di in dv])
    out["even" if par == 0 else "odd"] = [(np.array([float(z) for z in v]), np.array([float(z) for z in d])) for v, d in zip(Vs, dVs)]
pickle.dump(out, open(f"jets_{which}_{a}_{M}.pkl", "wb")); print("done", which)
