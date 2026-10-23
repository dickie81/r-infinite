#!/usr/bin/env python3
"""Round 69: nullvec.py with fast coefficients (arb, Chebyshev recurrence for cos(k x)) and
inverse iteration for lambda_1, lambda_2 and the ground vector (one high-precision inverse instead
of a full eigensolve). Same outputs as nullvec.py; validated against it at delta = 2.0 and 2.4.
Usage: nullvec_fast.py <delta> <K> <prec> [panels]
"""
import sys, os, json, math, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "..", "research"))
from weil_prime_gram import gram
from flint import arb, arb_mat, ctx
import mpmath as mp

def Phi(t):
    s = arb(0); n = 1; X = (2*t).exp(); tiny = arb(2)**(-ctx.prec - 10)
    while True:
        c = arb.pi()*n*n
        term = (2*c*c*X*X - 3*c*X)*(t/2 - c*X).exp()
        s += term
        if abs(term.mid()) < tiny: return s
        n += 1

def coeffs(a, K, panels, deg=192):
    mp.mp.prec = ctx.prec
    gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
    lev = int(math.log2(deg // 3))
    nodes = gl.calc_nodes(lev, mp.mp.prec)          # 3*2^lev nodes on [-1, 1]
    nodes = [(arb(mp.nstr(x, int(ctx.prec*0.31))), arb(mp.nstr(w, int(ctx.prec*0.31)))) for x, w in nodes]
    h = a/panels; pi_a = arb.pi()/a
    acc = [arb(0)]*K
    for p in range(panels):
        lo = h*p
        for x, w in nodes:
            t = lo + h*(x + 1)/2
            wf = w*h/2*Phi(t)
            c1 = (pi_a*t).cos()
            ckm1, ck = arb(1), c1                       # cos(0 x), cos(1 x)
            acc[0] += wf
            if K > 1: acc[1] += wf*c1
            for k in range(2, K):
                ckm1, ck = ck, 2*c1*ck - ckm1
                acc[k] += wf*ck
    return [2*acc[0]/(2*a)] + [2*acc[k]/a for k in range(1, K)], panels*len(nodes)

def inv_iter(Minv, M, K, x0, ortho=None, iters=8):
    x = x0
    lam = None
    for _ in range(iters):
        if ortho is not None:
            pr = (ortho.transpose()*x)[0, 0]
            x = x - ortho*pr
        x = Minv*x
        nrm = ((x.transpose()*x)[0, 0]).sqrt()
        x = arb_mat([[x[i, 0].mid()/nrm.mid()] for i in range(K)])
        lam_new = (x.transpose()*M*x)[0, 0].mid()
        lam = lam_new
    if ortho is not None:
        pr = (ortho.transpose()*x)[0, 0]; x = x - ortho*pr
        nrm = ((x.transpose()*x)[0, 0]).sqrt(); x = arb_mat([[x[i, 0].mid()/nrm.mid()] for i in range(K)])
        lam = (x.transpose()*M*x)[0, 0].mid()
    return lam, x

def run(delta, K, prec, panels):
    t0 = time.time()
    with ctx.workprec(prec):
        a = arb(delta)/2
        G, N, pp = gram(delta, K, prec)
        c, npts = coeffs(a, K, panels)
        t1 = time.time()
        v = arb_mat([[ci] for ci in c])
        num = (v.transpose()*G*v)[0, 0]
        den = arb(0)
        for i in range(K): den += N[i]*v[i, 0]*v[i, 0]
        Qphi = num/den
        D = arb_mat(K, K); Dm = []
        for i in range(K):
            D[i, i] = 1/N[i].sqrt(); Dm.append(D[i, i].mid())
        M = arb_mat(K, K)
        Gs = D*G*D
        for i in range(K):
            for j in range(K): M[i, j] = Gs[i, j].mid()
        Minv = M.inv()
        Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)])
        t2 = time.time()
        x0 = arb_mat([[arb(1)/(i + 1)] for i in range(K)])
        l1, g1 = inv_iter(Minv, M, K, x0)
        x0b = arb_mat([[arb((-1)**i)/(i + 1)] for i in range(K)])
        l2, g2 = inv_iter(Minv, M, K, x0b, ortho=g1)
        # angle in the N-inner product: g (true coords) = D g1; phi coords c
        g = [g1[i, 0]*Dm[i] for i in range(K)]
        gNg = sum(N[i]*g[i]*g[i] for i in range(K)); gNc = sum(N[i]*g[i]*v[i, 0] for i in range(K))
        sin2 = 1 - gNc*gNc/(gNg*den)
        R = (Qphi - l1)/(l2 - l1)
        return {"delta": delta, "K": K, "prec": prec, "panels": panels, "quad_pts": npts,
                "phi_norm2": den.mid().str(12, radius=False),
                "Qphi": Qphi.mid().str(12, radius=False), "Qphi_rad": Qphi.rad().str(3, radius=False),
                "lam1": l1.str(12, radius=False), "lam2": l2.str(12, radius=False),
                "R": R.mid().str(12, radius=False), "sin2_angle": sin2.mid().str(12, radius=False),
                "Phi_at_a": Phi(a).mid().str(12, radius=False),
                "t_coeff_s": round(t1 - t0, 1), "t_eig_s": round(time.time() - t1, 1)}

if __name__ == "__main__":
    d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    panels = int(sys.argv[4]) if len(sys.argv) > 4 else max(96, K)
    print(json.dumps(run(d, K, p, panels)), flush=True)
