#!/usr/bin/env python3
"""Round 69: the shape of the ground state's deviation from Phi.
r = g - <g, phi> phi (g, phi unit vectors in L^2(-a, a), sign fixed so <g, phi> > 0) has norm sin(theta).
Prints r(t)/sin(theta) on a grid, its L^2 mass split into |t| < a - 1 and the last unit near the edge,
and the energy Q(r)/||r||^2. Usage: defect.py <delta> <K> <prec>
"""
import sys, json, math
from flint import arb, arb_mat, ctx
import nullvec_fast as nf
from weil_prime_gram import gram

def run(delta, K, prec):
    with ctx.workprec(prec):
        a = arb(delta)/2
        G, N, pp = gram(delta, K, prec)
        c, _ = nf.coeffs(a, K, max(96, K))
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
        l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
        g = [g1[i, 0]*D[i] for i in range(K)]                       # true cosine coefficients
        ip = lambda x, y: sum(N[i]*x[i]*y[i] for i in range(K))
        ng = ip(g, g).sqrt(); nc = ip(c, c).sqrt()
        gu = [x/ng for x in g]; cu = [x/nc for x in c]
        s = ip(gu, cu)
        if s < 0: gu = [-x for x in gu]; s = -s
        r = [gu[i] - s*cu[i] for i in range(K)]
        sin2 = ip(r, r); sn = sin2.sqrt()
        av = float(a.mid())
        def ev(coef, t):
            x = arb.pi()*arb(t)/a
            return sum(coef[k]*(k*x).cos() for k in range(K))
        grid = [av*j/40 for j in range(41)]
        prof = [(round(t, 4), float((ev(r, t)/sn).mid()), float(ev(cu, t).mid())) for t in grid]
        # mass split: numerically on a fine grid
        n = 2000; w = av/n
        inner = 0.0; edge = 0.0
        for j in range(n):
            t = (j + 0.5)*w; val = float((ev(r, t)/sn).mid())**2*2*w
            if t < av - 1: inner += val
            else: edge += val
        rv = arb_mat([[r[i]] for i in range(K)])
        Qr = (rv.transpose()*G*rv)[0, 0]/sin2
        return {"delta": delta, "K": K, "sin2": float(sin2.mid()), "lam1": l1.str(6, radius=False),
                "Q_r_over_norm2": Qr.mid().str(6, radius=False),
                "mass_inner(|t|<a-1)": inner, "mass_edge(last unit)": edge, "profile(t, r/sin, phi_unit)": prof}

if __name__ == "__main__":
    print(json.dumps(run(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))))
