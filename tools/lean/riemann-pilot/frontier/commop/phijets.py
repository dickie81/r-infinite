#!/usr/bin/env python3
"""Gram-Schmidt of Riemann's kernel jets Phi^{(k)} on [-a,a] (a large: edge-flat), per parity.
Phi^{(m)}(u) = e^{u/2} sum_n p_m(q_n) e^{-q_n}, q_n = pi n^2 e^{2u}, p_0 = 2q^2 - 3q, p_{m+1} = 2q p_m' + (1/2 - 2q) p_m.
Saves samples v, v' of the orthonormal ladder functions (even k -> even, odd k -> odd) on Gauss nodes."""
import mpmath as mp, numpy as np, sys, pickle
from numpy.polynomial.legendre import leggauss
mp.mp.dps = 60
a, M, n = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
# polynomials in q
P = [mp.polynomial if False else None]
polys = [[0, -3, 2]]  # coefficients c_j of q^j
for m in range(M + 1):
    c = polys[-1]; new = [mp.mpf(0)]*(len(c) + 1)
    for j, cj in enumerate(c):
        if j > 0: new[j] += 2*j*cj          # 2q p'
        new[j] += cj/2                       # p/2
        new[j + 1] += -2*cj                  # -2q p
    polys.append(new)
def phi(m, u):
    u = mp.mpf(u); s = mp.mpf(0); N = 1
    while True:
        q = mp.pi*N*N*mp.e**(2*u)
        if q > 400 + 10*m: break
        s += sum(cj*q**j for j, cj in enumerate(polys[m]))*mp.e**(-q); N += 1
    return mp.e**(u/2)*s
x, w = leggauss(n); t = a*x; w = a*w
def vals(m):
    # Phi is even in u: use |u| for even m, sign for odd m (Phi^{(m)}(-u) = (-1)^m Phi^{(m)}(u))
    return [(1 if (tt >= 0 or m % 2 == 0) else -1)*phi(m, abs(tt)) for tt in t]
F = [vals(m) for m in range(M + 1)]   # F[m] = Phi^{(m)}; derivative of Phi^{(m)} is F[m+1]
out = {"a": a, "t": t, "w": w, "even": [], "odd": []}
for par in (0, 1):
    ks = [k for k in range(M) if k % 2 == par]
    Vs, dVs = [], []
    wm = [mp.mpf(float(x)) for x in w]
    ip = lambda f, g: mp.fsum(wi*fi*gi for wi, fi, gi in zip(wm, f, g))
    for k in ks:
        v, dv = list(F[k]), list(F[k + 1])
        for _ in range(2):
            for (u, du) in zip(Vs, dVs):
                c = ip(v, u); v = [vi - c*ui for vi, ui in zip(v, u)]; dv = [di - c*ui for di, ui in zip(dv, du)]
        nr = mp.sqrt(ip(v, v)); Vs.append([vi/nr for vi in v]); dVs.append([di/nr for di in dv])
    out["even" if par == 0 else "odd"] = [(np.array([float(x) for x in v]), np.array([float(x) for x in d])) for v, d in zip(Vs, dVs)]
pickle.dump(out, open(f"phijets_{a}_{M}.pkl", "wb"))
print("done", a, M, [round(float(np.sum(w*v*v)), 6) for v, _ in out["even"]][:3])
