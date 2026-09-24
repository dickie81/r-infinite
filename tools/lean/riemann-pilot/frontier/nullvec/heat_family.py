#!/usr/bin/env python3
"""Round 73: one-parameter reduced model. h_tau = sum_{k<=m} (-tau)^k Phi^(2k)/k! on [-a, a] (heat-flowed Phi,
series truncated at m). E(tau) = Q(h_tau)/||h_tau||^2 on the certified Gram; scan c = tau e^delta and report
the minimiser for several m, against 1/(16 pi) = 0.019894 and the ground state's measured value.
Usage: heat_family.py <delta> <K> <prec> <m1,m2,...>"""
import sys, json, math
from flint import arb, arb_mat, ctx
from defect_fit import Phi_deriv, coeffs_f
from weil_prime_gram import gram

def run(delta, K, prec, ms):
    mmax = max(ms)
    with ctx.workprec(prec):
        a = arb(delta)/2
        G, N, pp = gram(delta, K, prec)
        B = [coeffs_f(a, K, max(96, K), lambda t, m=m: Phi_deriv(t, 2*m)) for m in range(mmax + 1)]
        Bm = arb_mat([[B[j][p] for j in range(mmax + 1)] for p in range(K)])
        A = Bm.transpose()*G*Bm
        Nd = arb_mat(K, K)
        for i in range(K): Nd[i, i] = N[i]
        Nm = Bm.transpose()*Nd*Bm
        A = [[A[i, j].mid() for j in range(mmax + 1)] for i in range(mmax + 1)]
        Nm = [[Nm[i, j].mid() for j in range(mmax + 1)] for i in range(mmax + 1)]
        X = arb(delta).exp()
        def E(c, m):
            tau = arb(c)/X
            w = [(-tau)**k/arb(math.factorial(k)) for k in range(m + 1)]
            num = sum(w[i]*A[i][j]*w[j] for i in range(m + 1) for j in range(m + 1))
            den = sum(w[i]*Nm[i][j]*w[j] for i in range(m + 1) for j in range(m + 1))
            return num/den
        out = {"delta": delta, "K": K, "scan": {}}
        for m in ms:
            # golden-section on log E over c in [0.002, 0.06]
            lo, hi = 0.002, 0.06
            f = lambda c: float(E(c, m).log().mid()) if E(c, m) > 0 else 1e9
            gr = (math.sqrt(5) - 1)/2
            x1, x2 = hi - gr*(hi - lo), lo + gr*(hi - lo); f1, f2 = f(x1), f(x2)
            for _ in range(60):
                if f1 < f2: hi, x2, f2 = x2, x1, f1; x1 = hi - gr*(hi - lo); f1 = f(x1)
                else: lo, x1, f1 = x1, x2, f2; x2 = lo + gr*(hi - lo); f2 = f(x2)
            c = (lo + hi)/2
            out["scan"][m] = {"c_opt": c, "E_opt": E(c, m).mid().str(6, radius=False),
                              "E(1/16pi)": E(1/(16*math.pi), m).mid().str(6, radius=False)}
        return out

if __name__ == "__main__":
    ms = [int(x) for x in sys.argv[4].split(",")]
    print(json.dumps(run(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), ms)))
