#!/usr/bin/env python3
"""Round 68: is Riemann's kernel Phi a near-ground-state of Weil's form on [-a, a]?

For each support delta = 2a: the Gram G (weil_prime_gram, arb balls) in the cosine basis, the
two lowest eigenvalues lam1 < lam2 of G v = lam N v, the cosine coefficients of the truncation
phi_a = Phi 1_[-a,a], its energy Q(phi_a)/||phi_a||^2 (arb enclosure for the projected vector),
the relative excess R = (Q(phi_a) - lam1)/(lam2 - lam1) that rh_of_relgap needs -> 0 faster than
a^-1 e^{-2ba}, and the angle between phi_a and the ground state (the hclose quantity).
Usage: nullvec.py <delta> <K> <prec>
"""
import sys, os, json, math, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "..", "research"))
from weil_prime_gram import gram
from flint import arb, acb, arb_mat, acb_mat, ctx
import mpmath as mp

def Phi(t):
    s = mp.mpf(0); n = 1
    while True:
        c = mp.pi*n*n; X = mp.exp(2*t)
        term = (2*c*c*X*X - 3*c*X)*mp.exp(t/2 - c*X)
        s += term
        if abs(term) < mp.mpf(10)**(-mp.mp.dps-5): return s
        n += 1

def coeffs(a, K, panels=96, deg=48):
    """c_k = (1/N_k) int_{-a}^{a} Phi(t) cos(omega_k t) dt, omega_k = k pi / a."""
    gl = mp.calculus.quadrature.GaussLegendre(mp.mp)
    nodes = gl.calc_nodes(int(math.log2(deg)) + 1, mp.mp.prec)   # [(x, w)] on [-1, 1]
    h = a/panels
    pts = []
    for p in range(panels):
        lo = p*h
        for x, w in nodes:
            t = lo + h*(x + 1)/2
            pts.append((t, w*h/2, Phi(t)))
    c = []
    for k in range(K):
        om = k*mp.pi/a
        I = 2*mp.fsum(w*f*mp.cos(om*t) for t, w, f in pts)     # even: 2 int_0^a
        N = 2*a if k == 0 else a
        c.append(I/N)
    return c, len(pts)

def run(delta, K, prec):
    mp.mp.prec = prec
    a = mp.mpf(delta)/2
    t0 = time.time()
    G, N, pp = gram(delta, K, prec)
    c, npts = coeffs(a, K)
    t1 = time.time()
    with ctx.workprec(prec):
        v = arb_mat(K, 1)
        for i in range(K): v[i, 0] = arb(mp.nstr(c[i], int(prec*0.3), min_fixed=-10**9, max_fixed=10**9))
        num = (v.transpose()*G*v)[0, 0]
        den = arb(0)
        for i in range(K): den += N[i]*v[i, 0]*v[i, 0]
        Qphi = num/den
        D = arb_mat(K, K)
        for i in range(K): D[i, i] = 1/N[i].sqrt()
        Gs = D*G*D
        E, Rv = acb_mat(Gs.mid()).eig(right=True, algorithm="approx")
        order = sorted(range(K), key=lambda i: E[i].real.mid())
        l1 = E[order[0]].real.mid(); l2 = E[order[1]].real.mid()
        g = [Rv[i, order[0]].real.mid()*D[i, i].mid() for i in range(K)]   # ground state coeffs
        gNg = sum(N[i]*g[i]*g[i] for i in range(K)); gNc = sum(N[i]*g[i]*v[i, 0] for i in range(K))
        cos2 = gNc*gNc/(gNg*den)
        sin2 = 1 - cos2
        R = (Qphi - l1)/(l2 - l1)
        out = {"delta": delta, "K": K, "prec": prec, "quad_pts": npts,
               "phi_norm2": den.mid().str(12, radius=False),
               "Qphi": Qphi.mid().str(12, radius=False), "Qphi_rad": Qphi.rad().str(3, radius=False),
               "lam1": l1.str(12, radius=False), "lam2": l2.str(12, radius=False),
               "R": R.mid().str(12, radius=False),
               "a_exp_a_R": (arb(delta)/2*(arb(delta)/2).exp()*R).mid().str(8, radius=False),
               "sin2_angle": sin2.mid().str(12, radius=False),
               "Phi_at_a": mp.nstr(Phi(a), 12), "time_s": round(time.time() - t0, 1)}
    return out

if __name__ == "__main__":
    d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    print(json.dumps(run(d, K, p)))
