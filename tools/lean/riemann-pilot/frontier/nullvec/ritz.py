#!/usr/bin/env python3
"""Round 73: Rayleigh–Ritz of Weil's form on span{Phi, Phi'', ..., Phi^(2m)} restricted to [-a, a].
Each Phi^(2k) is a null direction on R (transform z^{2k} Xi vanishes at every zero), so the restricted
energy is edge cost only. Reports lambda_Ritz (vs lambda_1) and the ratio c1/c0 (vs the ground state's beta).
Usage: ritz.py <delta> <K> <prec> <mmax>"""
import sys, json, math
from flint import arb, arb_mat, acb_mat, ctx
from defect_fit import Phi_deriv, coeffs_f
from weil_prime_gram import gram
import nullvec_fast as nf

def run(delta, K, prec, mmax):
    with ctx.workprec(prec):
        a = arb(delta)/2; panels = max(96, K)
        G, N, pp = gram(delta, K, prec)
        B = [coeffs_f(a, K, panels, lambda t, m=m: Phi_deriv(t, 2*m)) for m in range(mmax + 1)]
        ip = lambda x, y: sum(N[i]*x[i]*y[i] for i in range(K))
        GB = [[sum(B[i][p]*G[p, q]*B[j][q] for p in range(K) for q in range(K)) if False else None for j in range(mmax + 1)] for i in range(mmax + 1)]
        # efficient: G*B_j as vectors
        Bm = arb_mat([[B[j][p] for j in range(mmax + 1)] for p in range(K)])
        A = Bm.transpose()*G*Bm
        Nm = arb_mat([[ip(B[i], B[j]) for j in range(mmax + 1)] for i in range(mmax + 1)])
        out = {"delta": delta, "K": K}
        for m in range(1, mmax + 1):
            n = m + 1
            As = arb_mat([[A[i, j].mid() for j in range(n)] for i in range(n)])
            Ns = arb_mat([[Nm[i, j].mid() for j in range(n)] for i in range(n)])
            # Cholesky-free: solve generalized problem via inverse iteration on Ns^{-1} As
            Ninv = Ns.inv()
            Mx = Ninv*As
            E, R = acb_mat(Mx).eig(right=True, algorithm="approx")
            k0 = min(range(n), key=lambda i: E[i].real.mid())
            v = [R[i, k0].real.mid() for i in range(n)]
            out[f"m={m}"] = {"lam_ritz": E[k0].real.mid().str(8, radius=False),
                             "c1/c0": (v[1]/v[0]).str(8, radius=False),
                             "c1/c0*e^delta": (v[1]/v[0]*arb(delta).exp()).str(6, radius=False),
                             "c2/c0": (v[2]/v[0]).str(6, radius=False) if n > 2 else None}
        # ground state for comparison
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
        l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
        out["lam1"] = l1.str(8, radius=False)
        return out

if __name__ == "__main__":
    print(json.dumps(run(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))))
