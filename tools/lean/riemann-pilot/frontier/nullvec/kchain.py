#!/usr/bin/env python3
"""Round 80: the Hamiltonian of the window chain a -> (PW_a, Q) (even part; a Krein string / diagonal
canonical system). For each support delta = 2a computes the 2x2 kernel matrix of the functionals
l0(F) = F(0) = int g and l2(F) = -[z^2]F = (1/2) int t^2 g:  Kmat = L Q^{-1} L^T.
Prints ln K00, r = K02/K00, s = K22/K00, det/K00^2.  Usage: kchain.py d0 d1 step [Kfac]"""
import sys, json, math
from flint import arb, arb_mat, ctx
import nullvec_fast  # noqa: puts tools/research on the path
from weil_prime_gram import gram
def run(d, K, prec):
    with ctx.workprec(prec):
        G, N, pp = gram(d, K, prec)
        a = arb(d)/2; pi = arb.pi()
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        L = arb_mat(K, 2)
        for k in range(K):
            l0 = 2*a if k == 0 else arb(0)
            if k == 0: l2 = a**3/3
            else:
                w = arb(k)*pi/a
                l2 = 2*a*(-1)**k/(w*w)          # (1/2) * 4a cos(ka pi)/w^2
            L[k, 0] = (l0*D[k]).mid(); L[k, 1] = (l2*D[k]).mid()
        Y = M.solve(L)
        Km = L.transpose()*Y
        k00, k02, k22 = Km[0, 0], Km[0, 1], Km[1, 1]
        f = lambda x: x.mid().str(20, radius=False)
        return {"delta": d, "K": K, "prec": prec, "lnK00": f(k00.log()), "r": f(k02/k00), "s": f(k22/k00),
                "detn": f((k00*k22 - k02*k02)/(k00*k00))}
d0, d1, st = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
Kf = float(sys.argv[4]) if len(sys.argv) > 4 else 20.0
n = int(round((d1 - d0)/st))
for i in range(n + 1):
    d = round(d0 + i*st, 6)
    K = max(40, int(Kf*math.exp(d)) + 40); prec = int(300 + 40*math.exp(d))
    print(json.dumps(run(d, K, prec)), flush=True)
