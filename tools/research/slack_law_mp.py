"""Zero-side lambda_1(delta) beyond the double-precision floor (the slack law).
Same object as slack_law.py: Z_jk = 2 sum_{gamma <= gmax} ghat_j ghat_k + the
smooth zero-density tail beyond gmax; basis = orthonormal Legendre on [-a, a]
of the given parity, ghat_n(r) = sqrt((2n+1)/(2a)) a 2 i^n j_n(a r).
The Gram is assembled in 256-bit ball arithmetic (python-flint: bessel_j and
matrix products in C), its midpoints handed to mpmath's symmetric eigensolver
at 60 digits.  A research measurement, not a certificate.

Usage: slack_law_mp.py <nz> delta [delta ...]
"""
import sys, math, json, os, time
import numpy as np
from flint import arb, arb_mat, ctx
from mpmath import mp, mpf, matrix, eigsy, log

HERE = os.path.dirname(os.path.abspath(__file__))
ZEROS = json.load(open(os.path.join(HERE, "checkpoints", "zeta_zeros_2000.json")))

def zero_side(delta, parity, nz, prec=256, dps=60):
    with ctx.workprec(prec):
        a = arb(delta)/2
        zs = [arb(z) for z in ZEROS[:nz]]
        T0 = 2*arb.pi()*arb(delta).exp()
        nmax = 2*(int(float((2*a*T0/arb.pi()).mid())) + 35)
        ns = list(range(0 if parity == "even" else 1, nmax, 2))
        m = len(ns)
        gmax = zs[-1]
        edges = [gmax*(arb(200)**(arb(i)/50)) for i in range(51)]
        xg, wg = np.polynomial.legendre.leggauss(16)
        rs = []; ws = []
        for lo, hi in zip(edges[:-1], edges[1:]):
            for xx, ww in zip(xg, wg):
                rs.append((hi - lo)/2*arb(float(xx)) + (hi + lo)/2); ws.append((hi - lo)/2*arb(float(ww)))
        dens = [(r/(2*arb.pi())).log()/(2*arb.pi()) for r in rs]
        fac = [(arb(2*n + 1)/(2*a)).sqrt()*a*2 for n in ns]
        sgn = [1 if n % 4 in (0, 1) else -1 for n in ns]      # the real-ified phase i^n within a parity
        def jn(n, x):
            x = a*x
            return (arb.pi()/(2*x)).sqrt()*x.bessel_j(arb(n) + arb(1)/2)
        Gz = arb_mat(m, len(zs)); Gt = arb_mat(m, len(rs))
        for i, n in enumerate(ns):
            for k, z in enumerate(zs):
                Gz[i, k] = sgn[i]*fac[i]*jn(n, z)
            for k, r in enumerate(rs):
                Gt[i, k] = sgn[i]*fac[i]*jn(n, r)*(ws[k]*dens[k]).sqrt()
        Z = 2*(Gz*Gz.transpose() + Gt*Gt.transpose())
        mp.dps = dps
        M = matrix(m, m)
        for i in range(m):
            for j in range(m):
                M[i, j] = mpf(Z[i, j].mid().str(dps + 10, radius=False))
        E, Q = eigsy(M)
        k0 = min(range(m), key=lambda i: E[i])
        lam1 = E[k0]; vec = [Q[i, k0] for i in range(m)]
        # which zeros carry the form: cumulative share over the zero list
        contrib = []
        for k in range(len(zs)):
            g = sum(vec[i]*mpf(Gz[i, k].mid().str(40, radius=False)) for i in range(m))
            contrib.append(2*g*g)
        tot = sum(contrib); cum = mpf(0); k50 = None; k90 = None
        for k, cv in enumerate(contrib):
            cum += cv
            if k50 is None and cum >= tot/2: k50 = k + 1
            if k90 is None and cum >= 9*tot/10: k90 = k + 1
        return lam1, k50, k90, float(tot/lam1), m

if __name__ == "__main__":
    nz = int(sys.argv[1]); prec = int(sys.argv[2]); dps = int(sys.argv[3]); deltas = [float(s) for s in sys.argv[4:]]
    print(f"nz {nz}; {prec}-bit Gram, {dps}-digit eigensolve", flush=True)
    for d in deltas:
        for par in ("even", "odd"):
            t0 = time.time()
            lam1, k50, k90, share, m = zero_side(d, par, nz, prec, dps)
            ln = float(log(lam1)) if lam1 > 0 else float('nan')
            ed = math.exp(d)
            print(f"{d:8.4f} {par:>4} lambda_1 {mp.nstr(lam1, 8):>14} ln {ln:9.3f} ln/e^d {ln/ed:8.4f} ln/(d e^d) {ln/(d*ed):8.4f} | "
                  f"half of Q above zero #{k50} (gamma {ZEROS[k50-1]:.1f}), 90% above #{k90} (gamma {ZEROS[k90-1]:.1f}) | listed zeros' share {share:.5f} | m {m} | {time.time()-t0:.0f}s", flush=True)
