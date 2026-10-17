#!/usr/bin/env python3
"""Measure, on the even sector at support [-a,a] (delta = 2a):
  c1, c2, c3 = lowest eigenvalues of the pole-free form Q0 = Q - 2 ghat(i/2)^2   (interlacing: lam_k(Q0) <= lam_k(Q) <= lam_{k+1}(Q0))
  lam1, lam2 = lowest eigenvalues of Q
  dist_J = || g_a - Pi_J g_a ||_{L^2[-a,a]}, g_a the normalised ground state of Q, Pi_J the L^2 projection
           onto span{Phi^{(2j)} restricted to [-a,a] : j <= J}  (true L^2 Gram, exact derivatives)
  hur_J = dist_J * e^{a/2} * sqrt(a)
Galerkin in cos(k pi t/a), k < K (weil_prime_gram.gram: arb entries)."""
import sys, json, math
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre
from flint import arb, acb, ctx
import weil_prime_gram as W

def dpolys(M):
    """p_m(q) as coefficient lists (Fractions), Phi^{(m)}(u) = sum_n p_m(q_n) e^{u/2 - q_n}."""
    from fractions import Fraction as F
    p = [F(0), F(-3), F(2)]
    out = [p]
    for m in range(M):
        dp = [i*p[i] for i in range(1, len(p))]              # p'
        new = [F(0)]*(len(p) + 1)
        for i, c in enumerate(dp): new[i + 1] += 2*c          # 2 q p'
        for i, c in enumerate(p): new[i] += c/2; new[i + 1] -= 2*c   # (1/2 - 2q) p
        out.append(new); p = new
    return out

def run(delta, K, prec, J=8, dps=int(__import__("os").environ.get("DPS", "150")), gl_deg=10):
    mp.mp.dps = dps
    a = mp.mpf(delta)/2
    G, N, pp = W.gram(delta, K, prec)
    with ctx.workprec(prec):
        half = arb(1)/2; aa = arb(delta)/2
        pv = []
        for k in range(K):
            w = acb(half, arb(k)*arb.pi()/aa)
            pv.append((2*(w*aa).sinh()/w).real)
    tomp = lambda x: mp.mpf(x.mid().str(dps + 10, radius=False))
    Gm = mp.matrix(K, K); Pm = [tomp(x) for x in pv]; Nm = [tomp(x) for x in N]
    for i in range(K):
        for j in range(K): Gm[i, j] = tomp(G[i, j])
    D = [1/mp.sqrt(x) for x in Nm]
    S = mp.matrix(K, K); S0 = mp.matrix(K, K)
    for i in range(K):
        for j in range(K):
            S[i, j] = D[i]*Gm[i, j]*D[j]
            S0[i, j] = D[i]*(Gm[i, j] - 2*Pm[i]*Pm[j])*D[j]
    E0 = sorted(mp.eigsy(S0, eigvals_only=True))
    E, V = mp.eigsy(S)
    order = sorted(range(K), key=lambda i: E[i])
    i1 = order[0]
    c = [V[k, i1]*D[k] for k in range(K)]                       # g = sum c_k cos(w_k t), ||g|| = 1
    # Phi^{(2j)} on [0,a] at Gauss-Legendre nodes (even functions)
    polys = dpolys(2*J)
    gl = GaussLegendre(mp.mp)
    nodes = gl.calc_nodes(gl_deg, mp.mp.prec)                        # on [-1,1]
    ts = [(x + 1)*a/2 for x, _ in nodes]; ws = [w*a/2 for _, w in nodes]
    def phider(m, u):
        s = mp.mpf(0); pm_ = polys[m]
        for n in range(1, 60):
            q = mp.pi*n*n*mp.e**(2*u)
            if q > 3*dps + 200: break
            s += sum(mp.mpf(cf.numerator)/cf.denominator*q**i for i, cf in enumerate(pm_))*mp.e**(u/2 - q)
        return s
    F = [[phider(2*j, t) for t in ts] for j in range(J + 1)]
    H = mp.matrix(J + 1, J + 1)
    for i in range(J + 1):
        for j in range(J + 1):
            H[i, j] = 2*mp.fsum(w*F[i][n]*F[j][n] for n, w in enumerate(ws))
    om = [k*mp.pi/a for k in range(K)]
    gvals = [mp.fsum(c[k]*mp.cos(om[k]*t) for k in range(K)) for t in ts]
    gg = 2*mp.fsum(w*gvals[n]**2 for n, w in enumerate(ws))            # quadrature check of ||g|| = 1
    b = [2*mp.fsum(w*gvals[n]*F[j][n] for n, w in enumerate(ws)) for j in range(J + 1)]
    dist = []; ang_phi = None
    for m in range(1, J + 2):
        Hm = mp.matrix([[H[i, j] for j in range(m)] for i in range(m)])
        bm = mp.matrix(b[:m])
        proj = (bm.T*mp.lu_solve(Hm, bm))[0, 0]
        dist.append(mp.sqrt(max(gg - proj, mp.mpf(0))))
    fac = mp.e**(a/2)*mp.sqrt(a)
    return {"delta": float(delta), "a": float(a), "K": K, "prec": prec, "primes": pp,
            "lam1": mp.nstr(E[order[0]], 8), "lam2": mp.nstr(E[order[1]], 8), "lam3": mp.nstr(E[order[2]], 8),
            "c1": mp.nstr(E0[0], 8), "c2": mp.nstr(E0[1], 8), "c3": mp.nstr(E0[2], 8),
            "gnorm_quad": mp.nstr(gg, 12),
            "dist": [mp.nstr(d, 6) for d in dist], "hur": [mp.nstr(d*fac, 6) for d in dist]}

if __name__ == "__main__":
    d = float(sys.argv[1]); K = int(sys.argv[2]); prec = int(sys.argv[3])
    print(json.dumps(run(d, K, prec)), flush=True)
