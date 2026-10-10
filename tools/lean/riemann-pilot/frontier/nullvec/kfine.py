#!/usr/bin/env python3
"""Round 81: the prime jumps of the window chain's potential. Fixed-K fine scan of l = ln K_a(0,0) across
delta = log n, plus the ground state's edge weight E = g(a)^2/lam1 (||g|| = 1) at delta = log n.
First-order prediction: l' jumps at log n by J_n = 2 Lambda(n) n^{-1/2} E(log n).
Usage: kfine.py n halfwidth step"""
import sys, json, math
import nullvec_fast as nf
from weil_prime_gram import gram
from flint import arb, arb_mat, ctx
n, hw, st = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
KF = float(sys.argv[4]) if len(sys.argv) > 4 else 25.0
d0 = math.log(n); K = int(KF*math.exp(d0)) + 60; prec = int(400 + 40*math.exp(d0))
def lam(n):
    for p in range(2, n + 1):
        if all(p % q for q in range(2, p)):
            m = n
            while m % p == 0: m //= p
            if m == 1: return math.log(p)
            return 0.0
def setup(d):
    G, N, pp = gram(d, K, prec)
    D = [1/N[i].sqrt() for i in range(K)]
    M = arb_mat(K, K)
    for i in range(K):
        for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
    return M, D
out = {"n": n, "log_n": d0, "K": K, "prec": prec, "Lambda_over_sqrt_n": lam(n)/math.sqrt(n), "scan": []}
with ctx.workprec(prec):
    m = int(round(hw/st))
    for i in range(-m, m + 1):
        d = d0 + i*st
        M, D = setup(d)
        e0 = arb_mat([[D[0]*arb(d)] + [] for _ in range(1)])   # placeholder, replaced below
        L = arb_mat([[ (arb(d)*D[0]).mid() if k == 0 else arb(0)] for k in range(K)])   # l0 = 2a c0 = delta c0
        y = M.solve(L)
        k00 = (L.transpose()*y)[0, 0]
        out["scan"].append([i*st, k00.log().mid().str(25, radius=False)])
    # edge weight at log n (the side just below: the prime is not yet active)
    M, D = setup(d0)
    Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
    l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
    nrm = sum(g1[i, 0]**2 for i in range(K)).sqrt()
    ga = sum((-1)**k*D[k]*g1[k, 0] for k in range(K))/nrm        # g(a) = sum (-1)^k c_k
    out["lam1"] = l1.mid().str(10, radius=False); out["g_edge"] = ga.mid().str(10, radius=False)
    out["E"] = (ga*ga/l1).mid().str(12, radius=False)
print(json.dumps(out), flush=True)
