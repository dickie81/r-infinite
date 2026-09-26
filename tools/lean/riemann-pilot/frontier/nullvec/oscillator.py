#!/usr/bin/env python3
"""Round 71: the harmonic-oscillator picture. Conjecture (round 70): g_a ~ c e^{-tau d^2} Phi with
tau = e^{-delta}/(16 pi), which on Phi's tail reads g/Phi ~ exp(-4 pi^2 tau x^2) = exp(-(pi/4) x^2/X),
x = e^{2t}, X = e^{delta}: a Gaussian in x. Evaluates the ground state pointwise on [0, a] from its cosine
coefficients, fits log(g/Phi) against x^2, and reports where the reconstruction is trustworthy (Phi
projected on the same basis, relative error). Usage: oscillator.py <delta> <K> <prec> <tau>"""
import sys, json, math
from flint import arb, arb_mat, ctx
import nullvec_fast as nf
from defect_fit import Phi_deriv
from weil_prime_gram import gram

def heat(t, tau, mmax=14):
    """e^{-tau d^2} Phi = sum_k (-tau)^k Phi^{(2k)}/k! (truncated at mmax terms; last term reported)."""
    tot = arb(0); fact = arb(1); last = arb(0)
    for k in range(mmax):
        if k: fact *= k
        term = (-tau)**k*Phi_deriv(t, 2*k)/fact
        tot += term; last = term
    return tot, last

def run(delta, K, prec, npts=60, tau=None):
    with ctx.workprec(prec):
        a = arb(delta)/2; X = math.exp(delta)
        G, N, pp = gram(delta, K, prec)
        c, _ = nf.coeffs(a, K, max(96, K))
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
        l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
        g = [g1[i, 0]*D[i] for i in range(K)]
        ip = lambda x, y: sum(N[i]*x[i]*y[i] for i in range(K))
        s = ip(g, c)/ip(g, g)              # scale g to best match Phi
        g = [s*v for v in g]
        pi_a = arb.pi()/a
        def ev(coef, t):
            c1 = (pi_a*t).cos(); ckm1, ck = arb(1), c1
            tot = coef[0] + coef[1]*c1
            for k in range(2, K):
                ckm1, ck = ck, 2*c1*ck - ckm1; tot += coef[k]*ck
            return tot
        rows = []
        for j in range(npts + 1):
            t = a*j/npts
            ph = nf.Phi(t); gv = ev(g, t); pr = ev(c, t)
            x = float((2*t).exp().mid())
            rec_err = float(abs((pr/ph - 1).mid()))
            lr = float((gv/ph).log().mid()) if gv > 0 else None
            h, last = heat(t, arb(tau))
            lh = float((h/ph).log().mid()) if h > 0 else None
            rows.append({"t": float(t.mid()), "x": x, "log_g_over_Phi": lr, "Phi_rec_relerr": rec_err,
                         "gauss_x_pred": -(math.pi/4)*x*x/X, "log_heat_over_Phi": lh,
                         "heat_last_term_rel": float(abs((last/h).mid()))})
        return {"delta": delta, "K": K, "X": X, "pred_slope_x2": -(math.pi/4)/X, "rows": rows}

if __name__ == "__main__":
    print(json.dumps(run(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), tau=float(sys.argv[4]))))
