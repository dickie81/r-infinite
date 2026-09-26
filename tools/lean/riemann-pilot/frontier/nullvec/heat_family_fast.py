#!/usr/bin/env python3
"""Round 73: heat_family.py, fast. All derivative orders Phi^(2k), k <= mmax, in one pass per quadrature
node (polynomial recursion shared across orders); Gauss–Legendre nodes generated once; cosine recurrence
once per node, accumulated into all orders. Same outputs as heat_family.py.
Usage: heat_family_fast.py <delta> <K> <prec> <m1,m2,...> [panels]"""
import sys, json, math
from flint import arb, arb_mat, ctx
import mpmath as mp
import nullvec_fast  # noqa: F401 (puts tools/research on the path)
from weil_prime_gram import gram

def phi_derivs(t, mmax):
    """[Phi^(0)(t), Phi^(2)(t), ..., Phi^(2 mmax)(t)] termwise; T^(j) = L^j(P) e^{t/2 - cX}."""
    X = (2*t).exp(); tiny = arb(2)**(-ctx.prec - 10)
    out = [arb(0)]*(mmax + 1); n = 1
    while True:
        c = arb.pi()*n*n; E = (t/2 - c*X).exp()
        p = {1: -3*c, 2: 2*c*c}
        big = arb(0)
        for j in range(2*mmax + 1):
            if j % 2 == 0:
                val = sum(v*X**k for k, v in p.items())*E
                out[j//2] += val
                if j == 0: big = abs(val.mid())
            if j < 2*mmax:
                q = {}
                for k, v in p.items():
                    q[k] = q.get(k, arb(0)) + 2*k*v + v/2
                    q[k + 1] = q.get(k + 1, arb(0)) - 2*c*v
                p = q
        if n > 2 and big < tiny: return out
        n += 1

def all_coeffs(a, K, panels, mmax):
    mp.mp.prec = ctx.prec
    gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
    nodes = [(arb(mp.nstr(x, int(ctx.prec*0.31))), arb(mp.nstr(w, int(ctx.prec*0.31))))
             for x, w in gl.calc_nodes(6, mp.mp.prec)]
    h = a/panels; pi_a = arb.pi()/a
    acc = [[arb(0)]*K for _ in range(mmax + 1)]
    for p in range(panels):
        for x, w in nodes:
            t = h*p + h*(x + 1)/2
            f = phi_derivs(t, mmax); wh = w*h/2
            wf = [wh*v for v in f]
            c1 = (pi_a*t).cos(); ckm1, ck = arb(1), c1
            for j in range(mmax + 1): acc[j][0] += wf[j]
            for j in range(mmax + 1): acc[j][1] += wf[j]*c1
            for k in range(2, K):
                ckm1, ck = ck, 2*c1*ck - ckm1
                for j in range(mmax + 1): acc[j][k] += wf[j]*ck
    return [[2*A[0]/(2*a)] + [2*A[k]/a for k in range(1, K)] for A in acc]

def run(delta, K, prec, ms, panels):
    mmax = max(ms)
    with ctx.workprec(prec):
        a = arb(delta)/2
        G, N, pp = gram(delta, K, prec)
        B = all_coeffs(a, K, panels, mmax)
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
        out = {"delta": delta, "K": K, "prec": prec, "panels": panels, "scan": {}}
        for m in ms:
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
    K = int(sys.argv[2])
    panels = int(sys.argv[5]) if len(sys.argv) > 5 else max(96, K//2)
    print(json.dumps(run(float(sys.argv[1]), K, int(sys.argv[3]), ms, panels)), flush=True)
