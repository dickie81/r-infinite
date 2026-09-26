#!/usr/bin/env python3
"""Round 74: memory- and time-lean version of nullvec_fast.py for large K (delta = 5 confirmation).
 - Phi's cosine coefficients at low precision (they only need ~1e-40 accuracy for the angle), with
   panels = K/4 x 48 Gauss–Legendre nodes (quadrature error ~1e-70);
 - only the midpoint matrix M = D G D is kept (G freed immediately); Q(phi) from M;
 - FLINT threads for the O(K^3) inverse.
Outputs sin^2(theta), lambda_1, lambda_2, R as nullvec_fast.py. Usage: nullvec_big.py <delta> <K> <prec> [threads]"""
import sys, os, json, math, time, gc
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "..", "research"))
from weil_prime_gram import gram
from flint import arb, arb_mat, ctx
import mpmath as mp

def Phi(t):
    s = arb(0); n = 1; X = (2*t).exp(); tiny = arb(2)**(-ctx.prec - 10)
    while True:
        c = arb.pi()*n*n
        term = (2*c*c*X*X - 3*c*X)*(t/2 - c*X).exp(); s += term
        if abs(term.mid()) < tiny*abs(s.mid()) or n > 40: return s
        n += 1

def coeffs_low(delta, K, cprec=256):
    with ctx.workprec(cprec):
        a = arb(delta)/2; panels = max(96, K//4)
        mp.mp.prec = cprec
        gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
        nodes = [(arb(mp.nstr(x, 80)), arb(mp.nstr(w, 80))) for x, w in gl.calc_nodes(5, cprec)]  # 48 nodes
        h = a/panels; pi_a = arb.pi()/a; acc = [arb(0)]*K
        for p in range(panels):
            for x, w in nodes:
                t = h*p + h*(x + 1)/2
                wf = w*h/2*Phi(t); c1 = (pi_a*t).cos(); ckm1, ck = arb(1), c1
                acc[0] += wf; acc[1] += wf*c1
                for k in range(2, K):
                    ckm1, ck = ck, 2*c1*ck - ckm1; acc[k] += wf*ck
        return [(2*acc[0]/(2*a)).mid()] + [(2*acc[k]/a).mid() for k in range(1, K)], panels*len(nodes)

def inv_iter(Minv, M, K, x, ortho=None, iters=8):
    for _ in range(iters + 1):
        if ortho is not None:
            x = x - ortho*(ortho.transpose()*x)[0, 0]
        x = Minv*x
        nrm = ((x.transpose()*x)[0, 0]).sqrt().mid()
        x = arb_mat([[x[i, 0].mid()/nrm] for i in range(K)])
    if ortho is not None:
        x = x - ortho*(ortho.transpose()*x)[0, 0]
        nrm = ((x.transpose()*x)[0, 0]).sqrt().mid(); x = arb_mat([[x[i, 0].mid()/nrm] for i in range(K)])
    return (x.transpose()*M*x)[0, 0].mid(), x

def run(delta, K, prec, threads):
    ctx.threads = threads
    t0 = time.time()
    c, npts = coeffs_low(delta, K)
    t1 = time.time()
    with ctx.workprec(prec):
        G, N, pp = gram(delta, K, prec)
        sq = [N[i].sqrt() for i in range(K)]
        M = arb_mat(K, K)
        for i in range(K):
            for j in range(K): M[i, j] = (G[i, j]/(sq[i]*sq[j])).mid()
        del G; gc.collect()
        t2 = time.time()
        # phi in the orthonormal coordinates y = D^{-1} c
        y = arb_mat([[arb(c[i])*sq[i]] for i in range(K)])
        ny = (y.transpose()*y)[0, 0]
        Qphi = (y.transpose()*M*y)[0, 0]/ny
        Minv = M.inv()
        Minv = arb_mat([[Minv[i, j].mid() for j in range(K)] for i in range(K)]); gc.collect()
        t3 = time.time()
        l1, g1 = inv_iter(Minv, M, K, arb_mat([[arb(1)/(i + 1)] for i in range(K)]))
        l2, g2 = inv_iter(Minv, M, K, arb_mat([[arb((-1)**i)/(i + 1)] for i in range(K)]), ortho=g1)
        cos = (g1.transpose()*y)[0, 0]/ny.sqrt()
        sin2 = 1 - cos*cos
        R = (Qphi - l1)/(l2 - l1)
        return {"delta": delta, "K": K, "prec": prec, "quad_pts": npts, "threads": threads,
                "Qphi": Qphi.mid().str(12, radius=False), "lam1": l1.str(12, radius=False),
                "lam2": l2.str(12, radius=False), "R": R.mid().str(12, radius=False),
                "sin2_angle": sin2.mid().str(12, radius=False),
                "t_coeff_s": round(t1 - t0, 1), "t_gram_s": round(t2 - t1, 1), "t_inv_s": round(t3 - t2, 1),
                "t_total_s": round(time.time() - t0, 1)}

if __name__ == "__main__":
    d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    th = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    print(json.dumps(run(d, K, p, th)), flush=True)
