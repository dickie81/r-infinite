#!/usr/bin/env python3
"""Rung upper bounds from jet trial spaces, evaluated on the ZERO side (explicit formula, proved in round 156):
for g = sum_k c_k Phi^{(m_k)} 1_[-a,a], ghat(t_rho) = -tail_g(t_rho) exactly (Phihat^{(m)} = (-iz)^m Xi/2 vanishes at
every zero), so Q(g) = sum_rho |tail_g(t_rho)|^2 (zeros on the line assumed here for the numerics; the rigorous
version only needs |Im t_rho| <= 1/2). tail via incomplete gamma: with q = pi n^2 e^{2u},
int_a^inf Phi^{(m)} e^{itu} du = sum_n (1/2) c_n^{-s} sum_j p_{m,j} Gamma(s + j, X_n),  s = 1/4 + it/2, X_n = c_n e^{2a}."""
import mpmath as mp, json, sys
delta, J, dps, nz = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = dps; a = mp.mpf(delta)/2
Z = json.load(open(__import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../../research/checkpoints/zeta_zeros_6700.json')))[:nz]
M = 2*J + 1
polys = [[mp.mpf(0), mp.mpf(-3), mp.mpf(2)]]
for _ in range(M):
    c = polys[-1]; new = [mp.mpf(0)]*(len(c)+1)
    for j, cj in enumerate(c):
        if j > 0: new[j] += 2*j*cj
        new[j] += cj/2; new[j+1] += -2*cj
    polys.append(new)
NT = 4
def I_all(t):
    """I_m(t) = int_a^inf Phi^{(m)}(u) e^{itu} du for m = 0..M."""
    s = mp.mpf(1)/4 + 1j*mp.mpf(t)/2
    out = [mp.mpc(0)]*(M + 1)
    for n in range(1, NT + 1):
        cn = mp.pi*n*n; X = cn*mp.e**(2*a)
        deg = len(polys[M])
        G = [mp.gammainc(s, X)]
        for j in range(deg):  # Gamma(s+j+1, X) = (s+j) Gamma(s+j, X) + X^{s+j} e^{-X}
            G.append((s + j)*G[-1] + X**(s + j)*mp.e**(-X))
        pre = cn**(-s)/2
        for m in range(M + 1):
            out[m] += pre*mp.fsum(cj*G[j] for j, cj in enumerate(polys[m]))
    return out
# tails at zeros
T_even = []; T_odd = []
for g in Z:
    I = I_all(g)
    T_even.append([2*mp.re(I[2*k]) for k in range(J + 1)])       # tail of Phi^{(2k)} (real)
    T_odd.append([2*mp.im(I[2*k + 1]) for k in range(J)])       # |tail| of Phi^{(2k+1)} (tail = 2i Im I)
# norms on the window (Gauss-Legendre on [0, a], doubled)
import numpy as np
from numpy.polynomial.legendre import leggauss
xg, wg = leggauss(300)
U = [a*(mp.mpf(float(x)) + 1)/2 for x in xg]; Wg = [a*mp.mpf(float(w))/2 for w in wg]
def Phi(u, m):
    s = 0; n = 1
    while True:
        q = mp.pi*n*n*mp.e**(2*u)
        if q > 2.3*dps + 60: break
        s += mp.polyval(polys[m][::-1], q)*mp.e**(-q); n += 1
    return mp.e**(u/2)*s
vals = [[Phi(u, m) for u in U] for m in range(M + 1)]
def gram(ms):
    return mp.matrix([[2*mp.fsum(w*vals[p][i]*vals[q][i] for i, w in enumerate(Wg)) for q in ms] for p in ms])
def minrq(T, ms, Jj):
    A = mp.matrix(Jj, Jj)
    for p in range(Jj):
        for q in range(Jj):
            A[p, q] = 2*mp.fsum(row[p]*row[q] for row in T)
    B = gram(ms[:Jj]); L = mp.cholesky(B); Li = mp.inverse(L); C = Li*A*Li.T
    return sorted(mp.eigsy((C + C.T)/2, eigvals_only=True))
out = {"delta": delta, "nzeros": nz, "Phi(a)^2": mp.nstr(Phi(a, 0)**2, 4), "rows": []}
for Jj in range(1, J + 1):
    ee = minrq(T_even, [2*k for k in range(J + 1)], Jj); oo = minrq(T_odd, [2*k + 1 for k in range(J)], Jj)
    out["rows"].append({"J": Jj, "even": [mp.nstr(x, 4) for x in ee[:3]], "odd": [mp.nstr(x, 4) for x in oo[:3]]})
    print(json.dumps(out["rows"][-1]), flush=True)
print(json.dumps({k: v for k, v in out.items() if k != "rows"}))
