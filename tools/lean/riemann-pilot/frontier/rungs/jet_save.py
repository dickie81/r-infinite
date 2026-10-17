#!/usr/bin/env python3
"""Rung upper bounds from jet trial spaces, evaluated on the ZERO side (explicit formula, proved in round 156):
for g = sum_k c_k Phi^{(m_k)} 1_[-a,a], ghat(t_rho) = -tail_g(t_rho) exactly (Phihat^{(m)} = (-iz)^m Xi/2 vanishes at
every zero), so Q(g) = sum_rho |tail_g(t_rho)|^2 (zeros on the line assumed here for the numerics; the rigorous
version only needs |Im t_rho| <= 1/2). tail via incomplete gamma: with q = pi n^2 e^{2u},
int_a^inf Phi^{(m)} e^{itu} du = sum_n (1/2) c_n^{-s} sum_j p_{m,j} Gamma(s + j, X_n),  s = 1/4 + it/2, X_n = c_n e^{2a}."""
import mpmath as mp, json, sys
delta, J, dps, nz = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = dps; a = mp.mpf(delta)/2
Z = json.load(open("/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research/checkpoints/zeta_zeros_6700.json"))[:nz]
M = 2*J
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
    T_even.append([2*mp.re(I[2*k]) for k in range(J)])       # tail of Phi^{(2k)} (real)
# norms on the window (Gauss-Legendre on [0, a], doubled)
import numpy as np
from numpy.polynomial.legendre import leggauss
NQ = int(sys.argv[6]) if len(sys.argv) > 6 else 300
xg0, _ = leggauss(NQ)
def gl_mp(n, x0):
    xs, ws = [], []
    for x in x0:
        x = mp.mpf(float(x))
        for _ in range(60):
            p0, p1 = mp.mpf(1), x
            for k in range(2, n + 1):
                p0, p1 = p1, ((2*k - 1)*x*p1 - (k - 1)*p0)/k
            dp = n*(x*p1 - p0)/(x*x - 1)
            dx = p1/dp; x -= dx
            if abs(dx) < mp.mpf(10)**(-mp.mp.dps + 5): break
        p0, p1 = mp.mpf(1), x
        for k in range(2, n + 1):
            p0, p1 = p1, ((2*k - 1)*x*p1 - (k - 1)*p0)/k
        dp = n*(x*p1 - p0)/(x*x - 1)
        xs.append(x); ws.append(2/((1 - x*x)*dp*dp))
    return xs, ws
XG, WG = gl_mp(NQ, xg0)
U = [a*(x + 1)/2 for x in XG]; Wg = [a*w/2 for w in WG]
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
def fullA(T, Jj):
    A = mp.matrix(Jj, Jj)
    for p in range(Jj):
        for q in range(p, Jj):
            A[p, q] = A[q, p] = 2*mp.fsum(row[p]*row[q] for row in T)
    return A
Js = [int(v) for v in sys.argv[5].split(",")] if len(sys.argv) > 5 else list(range(1, J + 1))
A = fullA(T_even, J); B = gram([2*k for k in range(J)])
import pickle
pickle.dump({'dps': dps, 'delta': delta, 'A': [[str(A[i,j]) for j in range(J)] for i in range(J)], 'B': [[str(B[i,j]) for j in range(J)] for i in range(J)]}, open(f'AB_{delta}_{J}.pkl', 'wb'))
for Jj in Js:
    Aj = A[:Jj, :Jj]; Bj = B[:Jj, :Jj]
    L = mp.cholesky(Bj); Li = mp.inverse(L); C = Li*Aj*Li.T
    ev = sorted(mp.eigsy((C + C.T)/2, eigvals_only=True))
    print(json.dumps({"J": Jj, "even": [mp.nstr(x, 5) for x in ev[:2]], "-ln": mp.nstr(-mp.log(ev[0]), 6)}), flush=True)
