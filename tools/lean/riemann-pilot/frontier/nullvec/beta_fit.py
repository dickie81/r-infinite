#!/usr/bin/env python3
"""Round 69: least-squares g ≈ c0 Phi + c2 Phi'' + c4 Phi'''' on [-a, a] (ground state g); the predicted
transform is Xi(z)(c0 - c2 z^2 + c4 z^4)/2, whose extra zeros solve c0 - c2 s + c4 s^2 = 0, s = z^2.
Usage: beta_fit.py <delta> <K> <prec>"""
import sys, json
from flint import arb, arb_mat, ctx
import nullvec_fast as nf
from defect_fit import Phi_deriv, coeffs_f
from weil_prime_gram import gram

def run(delta, K, prec):
    with ctx.workprec(prec):
        a = arb(delta)/2; panels = max(96, K)
        G, N, pp = gram(delta, K, prec)
        ip = lambda x, y: sum(N[i]*x[i]*y[i] for i in range(K))
        B = [coeffs_f(a, K, panels, lambda t, m=m: Phi_deriv(t, m)) for m in (0, 2, 4)]
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
        l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
        g = [g1[i, 0]*D[i] for i in range(K)]
        A = arb_mat([[ip(B[i], B[j]) for j in range(3)] for i in range(3)])
        rhs = arb_mat([[ip(B[i], g)] for i in range(3)])
        c = A.solve(rhs)
        c0, c2, c4 = c[0, 0], c[1, 0], c[2, 0]
        beta, gam = c2/c0, c4/c0
        # roots of 1 - beta s + gam s^2
        disc = beta*beta - 4*gam
        out = {"delta": delta, "K": K, "beta": beta.mid().str(8, radius=False), "gamma": gam.mid().str(8, radius=False),
               "beta_e2a": (beta*(2*a).exp()).mid().str(6, radius=False),
               "gamma_e4a": (gam*(4*a).exp()).mid().str(6, radius=False)}
        if disc >= 0:
            s1 = (beta - disc.sqrt())/(2*gam); s2 = (beta + disc.sqrt())/(2*gam)
            out["extra_zeros_z"] = [float(s.sqrt().mid()) if s > 0 else f"s={float(s.mid()):.4g}" for s in (s1, s2)]
        else:
            out["extra_zeros_z"] = "complex s (disc < 0)"
        out["one_over_sqrt_beta"] = float((1/beta.sqrt()).mid()) if beta > 0 else None
        return out

if __name__ == "__main__":
    print(json.dumps(run(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))))
