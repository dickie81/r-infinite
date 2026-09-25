#!/usr/bin/env python3
"""Round 86 (pre-registered test, PREREG_tower_layers.md): the chain's kernel at the tower points z = i(d+1/2),
d = 0..60, computed directly from the Gram: ln[K_a(i(d+1/2),0)/K_a(0,0)] = ln[k0hat(i(d+1/2))/k0hat(0)].
Basis K = 15 e^delta + 40, precision 300 + 24 e^delta bits (the round-85 settings).
Usage: ztower.py delta"""
import sys, json, math
import nullvec_fast  # noqa
from weil_prime_gram import gram
from flint import arb, arb_mat, ctx
d = float(sys.argv[1]); K = int(15*math.exp(d)) + 40; prec = int(300 + 24*math.exp(d))
with ctx.workprec(prec):
    G, N, pp = gram(d, K, prec)
    D = [1/N[i].sqrt() for i in range(K)]
    M = arb_mat(K, K)
    for i in range(K):
        for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
    y = M.solve(arb_mat([[arb(1) if k == 0 else arb(0)] for k in range(K)]))
    c = [D[k]*y[k, 0] for k in range(K)]
    a = arb(d)/2; pi = arb.pi()
    def gi(v):
        v = arb(v); s = 2*c[0]*(v*a).sinh()/v
        for k in range(1, K):
            om = arb(k)*pi/a
            s += c[k]*2*(-1)**k*v*(v*a).sinh()/(v*v + om*om)
        return s
    g0 = 2*a*c[0]
    out = {"delta": d, "K": K, "prec": prec, "layers": {}}
    for L in range(61):
        v = arb(L) + arb(1)/2
        out["layers"][str(L)] = (gi(v)/g0).log().mid().str(25, radius=False)
print(json.dumps(out))
