#!/usr/bin/env python3
"""Round 81: the jump of the chain potential at delta = log n, noise-free. At delta = log n + eps, compare
l = ln K_a(0,0) with and without the single prime-power term of n (same basis, so the truncation error
cancels): Dl(eps) = l(with) - l(without) = J_n eps + O(eps^2). Also the edge weight E = k(a)^2/K(0,0) of the
reproducing kernel k = Q^{-1} ev_0 at delta = log n + eps (first-order prediction J_n = 2 Lambda(n) n^{-1/2} E).
Usage: kprime.py n [Kfac]"""
import sys, json, math
import nullvec_fast  # noqa
from weil_prime_gram import gram
from flint import arb, arb_mat, ctx
n = int(sys.argv[1]); KF = float(sys.argv[2]) if len(sys.argv) > 2 else 25.0
EPS = [float(x) for x in sys.argv[3].split(',')] if len(sys.argv) > 3 else [0.0, 0.00025, 0.0005, 0.001]
def vonmangoldt(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return math.log(p) if m == 1 else 0.0
d0 = math.log(n); K = int(KF*math.exp(d0)) + 60; prec = int(400 + 40*math.exp(d0))
w_f = vonmangoldt(n)/math.sqrt(n)
out = {"n": n, "log_n": d0, "K": K, "prec": prec, "w": w_f, "eps": []}
with ctx.workprec(prec):
    for eps in EPS:
        d = arb(d0) + arb(eps)
        G, N, pp = gram(float(d0 + eps), K, prec)
        a = arb(float(d0 + eps))/2; twoa = 2*a; pi = arb.pi()
        om = [arb(k)*pi/a for k in range(K)]
        u = arb(n).log()
        pbase = [q for q in range(2, n + 1) if n % q == 0][0]
        wgt = arb(pbase).log()/arb(n).sqrt()
        s = [(om[k]*u).sin() for k in range(K)]; c = [(om[k]*u).cos() for k in range(K)]
        Pn = arb_mat(K, K)
        for j in range(K):
            for k in range(j, K):
                if j == k:
                    v = 2*wgt*(twoa - u) if k == 0 else 2*wgt*((twoa - u)*c[k] - s[k]/om[k])/2
                else:
                    sg = -1 if (j + k) % 2 else 1
                    v = 2*wgt*sg*(om[k]*s[k] - om[j]*s[j])/(om[j]*om[j] - om[k]*om[k])
                Pn[j, k] = v; Pn[k, j] = v
        D = [1/N[i].sqrt() for i in range(K)]
        M1 = arb_mat(K, K); M0 = arb_mat(K, K)
        for i in range(K):
            for j in range(K):
                M1[i, j] = (D[i]*G[i, j]*D[j]).mid(); M0[i, j] = (D[i]*(G[i, j] + Pn[i, j])*D[j]).mid()
        L = arb_mat([[arb(1) if k == 0 else arb(0)] for k in range(K)])
        y1 = M1.solve(L); y0 = M0.solve(L)
        k1 = y1[0, 0]; k0 = y0[0, 0]
        edge = sum((-1)**k*D[k]*y1[k, 0] for k in range(K))       # k(a) in the normalisation ev_0 = e_0
        E = (edge*edge/k1)*(D[0]*D[0])/(D[0]*D[0])              # k(a)^2/K(0,0) with K(0,0) = k1 (e_0 units)
        # convert: ev_0(g) = 2a c_0 = 2a D_0 x_0, so the true K(0,0) = (2a D_0)^2 k1 and k(a) scales by 2a D_0: E invariant
        dl = (k1/k0).log() if eps > 0 else arb(0)
        out["eps"].append({"eps": eps, "Dl": dl.mid().str(15, radius=False), "E": E.mid().str(12, radius=False),
                           "lnK": k1.log().mid().str(15, radius=False)})
print(json.dumps(out), flush=True)
