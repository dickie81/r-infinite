#!/usr/bin/env python3
"""Round 79: the ground state of Weil's form at support [-a, a] against the reproducing kernel at z = 0 of the
space PW_a with the Weil norm (the value at a of the Weil-Krein-de Branges chain a -> (PW_a, Q)).
k_0 = Q^{-1} ev_0, ev_0(g) = ghat(0) = int g. Reports sin^2 of the angle between k_0 and the ground state g1,
and lam1/lam2. Usage: repkernel.py <delta> <K> <prec>"""
import sys, json
from flint import arb, arb_mat, ctx
import nullvec_fast as nf
from weil_prime_gram import gram
d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
with ctx.workprec(p):
    G, N, pp = gram(d, K, p)
    D = [1/N[i].sqrt() for i in range(K)]
    M = arb_mat(K, K)
    for i in range(K):
        for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
    Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
    l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
    # ev_0 in normalised coordinates: ghat(0) = 2a c_0 = 2a D_0 x_0  ->  direction e_0
    e0 = arb_mat([[arb(1) if i == 0 else arb(0)] for i in range(K)])
    k0 = Minv*e0
    dot = sum(k0[i, 0]*g1[i, 0] for i in range(K)); nk = sum(k0[i, 0]**2 for i in range(K)); ng = sum(g1[i, 0]**2 for i in range(K))
    s2 = 1 - dot*dot/(nk*ng)
    l2, _ = nf.inv_iter(Minv, M, K, arb_mat([[arb((-1)**i)/(i + 2)] for i in range(K)]), ortho=g1)
    Kzz = (e0.transpose()*k0)[0, 0]
    f = lambda x: x.mid().str(6, radius=False)
    print(json.dumps({"delta": d, "K": K, "sin2_k0_g1": f(s2), "lam1": f(l1), "lam2": f(l2), "lam1/lam2": f(l1/l2),
                      "log_K00": f(Kzz.log()), "minus_log_lam1": f(-l1.log())}))
