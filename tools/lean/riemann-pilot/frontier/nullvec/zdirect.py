#!/usr/bin/env python3
"""Round 82: the chain's reproducing kernel k0 = Q_a^{-1} ev_0 and its normalised transform
K_a(z,0)/K_a(0,0) = k0hat(z)/k0hat(0) at real z and at z = i y, computed directly from the Gram.
Usage: zdirect.py delta Kfac   (prints JSON)"""
import sys, json, math
import nullvec_fast  # noqa
from weil_prime_gram import gram
from flint import arb, arb_mat, ctx
d = float(sys.argv[1]); Kf = float(sys.argv[2]); K = max(40, int(Kf*math.exp(d)) + 40); prec = int(300 + 40*math.exp(d))
ZR = [1, 2, 5, 8, 10, 14.134725, 18, 21.022040, 25, 30]
YI = [1, 2, 5, 10, 20, 40]
with ctx.workprec(prec):
    G, N, pp = gram(d, K, prec)
    D = [1/N[i].sqrt() for i in range(K)]
    M = arb_mat(K, K)
    for i in range(K):
        for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
    y = M.solve(arb_mat([[arb(1) if k == 0 else arb(0)] for k in range(K)]))
    c = [D[k]*y[k, 0] for k in range(K)]
    a = arb(d)/2; pi = arb.pi()
    def gr(x):
        x = arb(x); s = 2*c[0]*(x*a).sin()/x
        for k in range(1, K):
            om = arb(k)*pi/a
            s += c[k]*(((x - om)*a).sin()/(x - om) + ((x + om)*a).sin()/(x + om))
        return s
    def gi(yv):
        yv = arb(yv); s = 2*c[0]*(yv*a).sinh()/yv
        for k in range(1, K):
            om = arb(k)*pi/a
            s += c[k]*2*(-1)**k*yv*(yv*a).sinh()/(yv*yv + om*om)
        return s
    g0 = 2*a*c[0]
    out = {"delta": d, "K": K, "real": {str(z): (gr(z)/g0).mid().str(15, radius=False) for z in ZR},
           "imag": {str(v): (gi(v)/g0).mid().str(15, radius=False) for v in YI}}
print(json.dumps(out))
