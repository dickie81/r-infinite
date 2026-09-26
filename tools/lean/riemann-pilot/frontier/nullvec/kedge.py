#!/usr/bin/env python3
"""Round 81: K-convergence of the edge weight E = k(a)^2/K(0,0) of the reproducing kernel at delta (and of l).
Usage: kedge.py delta K1,K2,... prec"""
import sys, json
import nullvec_fast  # noqa
from weil_prime_gram import gram
from flint import arb, arb_mat, ctx
d = float(sys.argv[1]); Ks = [int(x) for x in sys.argv[2].split(",")]; prec = int(sys.argv[3])
for K in Ks:
    with ctx.workprec(prec):
        G, N, pp = gram(d, K, prec)
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        y = M.solve(arb_mat([[arb(1) if k == 0 else arb(0)] for k in range(K)]))
        k1 = y[0, 0]; edge = sum((-1)**k*D[k]*y[k, 0] for k in range(K))
        # also the kernel's value at t = a - h for a few h (the edge layer profile)
        a = arb(d)/2; pi = arb.pi()
        prof = []
        for h in [0.0, 0.005, 0.01, 0.02, 0.05]:
            t = a - arb(h)
            v = sum(D[k]*y[k, 0]*(arb(k)*pi*t/a).cos() for k in range(K))
            prof.append((v*v/k1).mid().str(6, radius=False))
        print(json.dumps({"delta": d, "K": K, "lnK": (k1.log()).mid().str(12, radius=False),
                          "E": (edge*edge/k1).mid().str(10, radius=False), "profile_h=0,.005,.01,.02,.05": prof}), flush=True)
