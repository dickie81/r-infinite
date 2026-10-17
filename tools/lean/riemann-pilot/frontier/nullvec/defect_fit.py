#!/usr/bin/env python3
"""Round 69: is the ground state's deviation from Phi made of Phi's even derivatives?
Fits r/sin(theta) (the unit component of the ground state orthogonal to Phi) against the Gram–Schmidt
sequence Phi, Phi'', Phi'''' (so transforms Xi, z^2 Xi, z^4 Xi, which vanish at every zeta zero).
Usage: defect_fit.py <delta> <K> <prec>
"""
import sys, json, math
from flint import arb, arb_mat, ctx
import mpmath as mp
import nullvec_fast as nf
from weil_prime_gram import gram

def Phi_deriv(t, m):
    """m-th derivative of Phi at t, termwise: T^{(m)} = L^m(P) e^{t/2 - cX}, X = e^{2t}."""
    s = arb(0); n = 1; X = (2*t).exp(); tiny = arb(2)**(-ctx.prec - 10)
    while True:
        c = arb.pi()*n*n
        p = {1: -3*c, 2: 2*c*c}                     # polynomial in X
        for _ in range(m):
            q = {}
            for k, v in p.items():
                q[k] = q.get(k, arb(0)) + 2*k*v + v/2
                q[k + 1] = q.get(k + 1, arb(0)) - 2*c*v
            p = q
        val = sum(v*X**k for k, v in p.items())*(t/2 - c*X).exp()
        s += val
        if abs(val.mid()) < tiny and n > 2: return s
        n += 1

def coeffs_f(a, K, panels, f):
    mp.mp.prec = ctx.prec
    gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
    nodes = [(arb(mp.nstr(x, int(ctx.prec*0.31))), arb(mp.nstr(w, int(ctx.prec*0.31))))
             for x, w in gl.calc_nodes(6, mp.mp.prec)]
    h = a/panels; pi_a = arb.pi()/a; acc = [arb(0)]*K
    for p in range(panels):
        for x, w in nodes:
            t = h*p + h*(x + 1)/2
            wf = w*h/2*f(t); c1 = (pi_a*t).cos(); ckm1, ck = arb(1), c1
            acc[0] += wf
            if K > 1: acc[1] += wf*c1
            for k in range(2, K):
                ckm1, ck = ck, 2*c1*ck - ckm1; acc[k] += wf*ck
    return [2*acc[0]/(2*a)] + [2*acc[k]/a for k in range(1, K)]

def run(delta, K, prec):
    with ctx.workprec(prec):
        a = arb(delta)/2; panels = max(96, K)
        G, N, pp = gram(delta, K, prec)
        ip = lambda x, y: sum(N[i]*x[i]*y[i] for i in range(K))
        basis = [coeffs_f(a, K, panels, lambda t, m=m: Phi_deriv(t, m)) for m in (0, 2, 4, 6)]
        # Gram–Schmidt
        ortho = []
        for b in basis:
            v = list(b)
            for u in ortho:
                pr = ip(v, u); v = [v[i] - pr*u[i] for i in range(K)]
            nv = ip(v, v).sqrt(); ortho.append([x/nv for x in v])
        D = [1/N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (D[i]*G[i, j]*D[j]).mid()
        Minv = M.inv(); Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
        l1, g1 = nf.inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
        g = [g1[i, 0]*D[i] for i in range(K)]
        ng = ip(g, g).sqrt(); g = [x/ng for x in g]
        comps = [ip(g, u) for u in ortho]
        if comps[0] < 0: comps = [-x for x in comps]
        sin2 = 1 - comps[0]**2
        out = {"delta": delta, "K": K, "sin2_vs_Phi": float(sin2.mid())}
        # fraction of the deviation captured by Phi'' , Phi'''' , Phi^(6) directions
        captured = arb(0)
        for m, cc in zip((2, 4, 6), comps[1:]):
            captured += cc*cc
            out[f"frac_dev_upto_Phi^({m})"] = float((captured/sin2).mid())
            out[f"coef_Phi^({m})_over_sin"] = float((cc/sin2.sqrt()).mid())
        out["residual_sin2_outside_span"] = float((sin2 - captured).mid())
        return out

if __name__ == "__main__":
    print(json.dumps(run(float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]))))
