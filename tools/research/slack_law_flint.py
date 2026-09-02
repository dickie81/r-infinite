"""Zero-side lambda_1(delta) with flint's C eigensolver (acb_mat.eig, approx mode
for the value, radius-free), for the delta range beyond mpmath's reach.  Same
Gram as slack_law_mp.py (2000 zeros + smooth density tail; orthonormal Legendre
basis of the parity; exact Gauss-Legendre nodes in arb).  Reports lambda_1 by
an eigenvalue of the ball-midpoint matrix, and (as the check) the Rayleigh
quotient of the returned eigenvector evaluated in ball arithmetic.
Usage: slack_law_flint.py <prec> <parity> delta [delta ...]
Environment: EXTRA (Legendre modes beyond 2 a T_0/pi; default 35 -- the
lambda_1 values converge slowly in it: at delta = 2, 5.896e-30 / 5.775e-30 /
5.715e-30 for EXTRA = 35 / 80 / 140), CASCADE_ZEROS (zero list).
Precision: the Bessel evaluations lose ~n/2 nats at order n ~ argument, so prec
must exceed ~0.75*nmax bits plus the digits wanted; the Rayleigh ball printed
is the check (a radius comparable to lambda_1 means the run is under-precise --
the 512-bit delta = 3 entry of Addendum 438's table failed this way).
Research instrument (Addendum 439): cited by no paper surface, keyed by nothing.
"""
import sys, math, json, os, time
from flint import arb, acb, arb_mat, acb_mat, ctx

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = [float(z) for z in json.load(open(os.environ.get("CASCADE_ZEROS", os.path.join(HERE, "checkpoints", "zeta_zeros_2000.json"))))]

def gl(n):
    out = [arb.legendre_p_root(n, k, weight=True) for k in range(n)]
    return [r for r, w in out], [w for r, w in out]

def gram(delta, parity, nz, nmax_extra=35):
    a = arb(delta)/2
    zs = [arb(z) for z in ZEROS[:nz]]
    T0 = 2*arb.pi()*arb(delta).exp()
    nmax = 2*(int(float((2*a*T0/arb.pi()).mid())) + nmax_extra)
    ns = list(range(0 if parity == "even" else 1, nmax, 2)); m = len(ns)
    gmax = zs[-1]
    edges = [gmax*(arb(200)**(arb(i)/50)) for i in range(51)]
    xg, wg = gl(16)
    rs = []; ws = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        for xx, ww in zip(xg, wg):
            rs.append((hi - lo)/2*xx + (hi + lo)/2); ws.append((hi - lo)/2*ww)
    dens = [(r/(2*arb.pi())).log()/(2*arb.pi()) for r in rs]
    fac = [(arb(2*n + 1)/(2*a)).sqrt()*a*2 for n in ns]
    sgn = [1 if n % 4 in (0, 1) else -1 for n in ns]
    half = arb(1)/2; pi2 = (arb.pi()/2)
    def jn(n, x):
        x = a*x
        return (pi2/x).sqrt()*x.bessel_j(arb(n) + half)
    Gz = arb_mat(m, len(zs)); Gt = arb_mat(m, len(rs))
    for i, n in enumerate(ns):
        for k, z in enumerate(zs):
            Gz[i, k] = sgn[i]*fac[i]*jn(n, z)
        for k, r in enumerate(rs):
            Gt[i, k] = sgn[i]*fac[i]*jn(n, r)*(ws[k]*dens[k]).sqrt()
    Z = 2*(Gz*Gz.transpose() + Gt*Gt.transpose())
    return Z, m, Gz

def lam1(delta, parity, prec, nz=2000, extra=35):
    with ctx.workprec(prec):
        t0 = time.time()
        Z, m, Gz = gram(delta, parity, nz, extra)
        t1 = time.time()
        Zc = acb_mat(Z.mid())
        E, R = Zc.eig(right=True, algorithm="approx")
        k0 = min(range(m), key=lambda i: E[i].real.mid())
        v = arb_mat(m, 1)
        for i in range(m): v[i, 0] = R[i, k0].real.mid()
        num = (v.transpose()*Z*v)[0, 0]; den = (v.transpose()*v)[0, 0]
        rq = num/den
        t2 = time.time()
        return E[k0].real.mid(), rq, m, t1 - t0, t2 - t1

if __name__ == "__main__":
    prec = int(sys.argv[1]); parity = sys.argv[2]; extra = int(os.environ.get("EXTRA", "35"))
    for d in [float(s) for s in sys.argv[3:]]:
        lam, rq, m, tg, te = lam1(d, parity, prec, extra=extra)
        ed = math.exp(d); ln = float(lam.log())
        print(f"{d:8.4f} {parity} lambda_1 {lam.str(8, radius=False)} (Rayleigh {rq.str(8)}) ln {ln:10.3f} ln/e^d {ln/ed:8.4f} ln/(d e^d) {ln/(d*ed):8.4f} | m {m} | gram {tg:.0f}s eig {te:.0f}s", flush=True)
