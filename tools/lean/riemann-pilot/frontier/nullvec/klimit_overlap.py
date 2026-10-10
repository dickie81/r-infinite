#!/usr/bin/env python3
"""Round 139b: how much of each ground state lies in span{Phi^(m)} (even m / odd m), restricted to [-a,a]."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
from kc2_hurwitz import dpolys
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
def ground(G, N, k, d):
    D = [1/mp.sqrt(tomp(N[i], d)) for i in range(k)]
    S = mp.matrix(k, k)
    for i in range(k):
        for j in range(k): S[i, j] = D[i]*tomp(G[i, j], d)*D[j]
    E, V = mp.eigsy(S); i0 = min(range(k), key=lambda i: E[i])
    return E[i0], [V[m, i0]*D[m] for m in range(k)]
delta, K, prec, d, M = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
mp.mp.dps = d; a = mp.mpf(delta)/2
le, ce = ground(*W.gram(delta, K, prec)[:2], K, d)
Go, No, _ = WO.gram_odd(delta, K + 1, prec); lo, co = ground(Go, No, K, d)
P = dpolys(2*M + 2)
def phid(m, u):
    s = mp.mpf(0)
    for n in range(1, 40):
        q = mp.pi*n*n*mp.e**(2*u)
        if q > 2*d + 100: break
        s += mp.fsum(mp.mpf(c.numerator)/c.denominator*q**i for i, c in enumerate(P[m]))*mp.e**(u/2 - q)
    return s
mp.mp.dps = 40
gl = mp.calculus.quadrature.GaussLegendre(mp.mp); nodes = gl.calc_nodes(9, mp.mp.prec)
ts = [(x + 1)*a/2 for x, _ in nodes]; ws = [w*a/2 for _, w in nodes]
om = [k*mp.pi/a for k in range(K + 1)]
ge = [mp.fsum(ce[k]*mp.cos(om[k]*t) for k in range(K)) for t in ts]
go = [mp.fsum(co[k - 1]*mp.sin(om[k]*t) for k in range(1, K + 1)) for t in ts]
ip = lambda f, g: 2*mp.fsum(w*f[i]*g[i] for i, w in enumerate(ws))
out = {"delta": delta, "K": K, "norm_e": mp.nstr(ip(ge, ge), 8), "norm_o": mp.nstr(ip(go, go), 8)}
for par, gs, ms in (("even", ge, [0, 2, 4, 6, 8]), ("odd", go, [1, 3, 5, 7, 9])):
    B = [[phid(m, t) for t in ts] for m in ms[:M]]
    res = []
    for r in range(1, M + 1):
        H = mp.matrix([[ip(B[i], B[j]) for j in range(r)] for i in range(r)]); b = mp.matrix([ip(gs, B[i]) for i in range(r)])
        res.append(mp.nstr(mp.sqrt(max(1 - (b.T*mp.lu_solve(H, b))[0, 0], 0)), 4))
    out["dist_" + par] = res
print(json.dumps(out), flush=True)
