#!/usr/bin/env python3
"""Upper bounds on rungs from jet trial spaces: min Rayleigh quotient of Weil's form over
span{Phi^(k) 1_[-a,a] : k = par, par+2, ..., par+2(J-1)} (cosine/sine truncation K), vs the Galerkin eigenvalues.
The truncated series of a trial is itself a probe, so each value is an upper bound on the true rung."""
import sys, json
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../../research'))
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
delta, K, J, d = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = d; a = mp.mpf(delta)/2
polys = [[0, -3, 2]]
for _ in range(2*J + 2):
    c = polys[-1]; new = [mp.mpf(0)]*(len(c)+1)
    for j, cj in enumerate(c):
        if j > 0: new[j] += 2*j*cj
        new[j] += cj/2; new[j+1] += -2*cj
    polys.append(new)
def Phi(u, m):
    sg = 1
    if u < 0: u = -u; sg = (-1)**m
    s = 0; n = 1
    while True:
        q = mp.pi*n*n*mp.e**(2*u)
        if q > 3*d + 50: break
        s += mp.polyval(polys[m][::-1], q)*mp.e**(-q); n += 1
    return sg*mp.e**(u/2)*s
xs, ws = mp.gauss_legendre if False else (None, None)
# Gauss-Legendre nodes on [0,a] (use symmetry)
nodes = mp.mpf(1)
def gl(n):
    import numpy as np
    from numpy.polynomial.legendre import leggauss
    x, w = leggauss(n)
    return [mp.mpf(float(v)) for v in x], [mp.mpf(float(v)) for v in w]
X, Wt = gl(int(sys.argv[5]) if len(sys.argv) > 5 else 600)
T = [a*(x + 1)/2 for x in X]; Wq = [a*w/2 for w in Wt]  # [0, a]
def coeffs(m, kind):
    vals = [Phi(t, m) for t in T]
    out = []
    ks = range(K) if kind == "even" else range(1, K)
    for k in ks:
        om = k*mp.pi/a
        basisv = [mp.cos(om*t) if kind == "even" else mp.sin(om*t) for t in T]
        ip = 2*mp.fsum(w*v*b for w, v, b in zip(Wq, vals, basisv))   # symmetric doubling
        N = 2*a if (kind == "even" and k == 0) else a
        out.append(ip/N)
    return out
def run(kind, G, N):
    n = G.nrows()
    Gm = mp.matrix(n, n); Nm = [tomp(N[i], d) for i in range(n)]
    for i in range(n):
        for j in range(n): Gm[i, j] = tomp(G[i, j], d)
    # Galerkin eigenvalues
    Dg = [1/mp.sqrt(x) for x in Nm]; S = mp.matrix(n, n)
    for i in range(n):
        for j in range(n): S[i, j] = Dg[i]*Gm[i, j]*Dg[j]
    gal = sorted(mp.eigsy(S, eigvals_only=True))[:3]
    par = 0 if kind == "even" else 1
    V = [coeffs(par + 2*j, kind) for j in range(J)]
    res = []
    for Jj in range(1, J + 1):
        A = mp.matrix(Jj, Jj); B = mp.matrix(Jj, Jj)
        for p in range(Jj):
            for q in range(Jj):
                A[p, q] = mp.fsum(V[p][i]*Gm[i, j]*V[q][j] for i in range(n) for j in range(n))
                B[p, q] = mp.fsum(V[p][i]*Nm[i]*V[q][i] for i in range(n))
        L = mp.cholesky(B); Li = mp.inverse(L)
        C = Li*A*Li.T
        ev = sorted(mp.eigsy((C + C.T)/2, eigvals_only=True))
        res.append([mp.nstr(e, 4) for e in ev[:min(3, Jj)]])
    return gal, res
Ge, Ne, _ = W.gram(delta, K, 4*d); Go, No, _ = WO.gram_odd(delta, K, 4*d)
ge, re_ = run("even", Ge, Ne); go, ro = run("odd", Go, No)
print(json.dumps({"delta": delta, "K": K, "galerkin_even": [mp.nstr(x, 4) for x in ge], "galerkin_odd": [mp.nstr(x, 4) for x in go]}))
for Jj in range(J):
    print(json.dumps({"J": Jj + 1, "even_jets": re_[Jj], "odd_jets": ro[Jj]}))
