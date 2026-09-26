"""The constant of the slack law: is the ground state the constrained prolate?

Family F(T_d, T_c): the unit probe g of exponential type a (support [-a, a],
even sector) that (i) vanishes at every zero gamma < T_d and (ii) among such
probes maximises its band concentration on [-T_c, T_c].  Its leakage
L = 1 - <g, K_{T_c} g> is exactly computable (the top eigenvalue of P K P, P the
projector orthogonal to the K evaluation functionals), and its zero-side value
Q(g) = sum_gamma |ghat(gamma)|^2 is a RIGOROUS upper bound on lambda_1(delta).
For each delta the script scans (T_d, T_c) and reports the best trial's Q
against the exact lambda_1, its leakage exponent -ln L against the Slepian
ceiling 2 a T_c, and the dodging cost -ln L_0 + ln L (L_0 the unconstrained
prolate's leakage).  Even sector.  Precision: the flint/mp machinery of
slack_law_mp.py (Gram in 256-512-bit balls, eigenproblems at dps digits).

Usage: constrained_prolate.py <prec> <dps> delta [delta ...]
Environment: CASCADE_THC / CASCADE_THD (comma lists of theta_c / theta_d),
CASCADE_ZEROS (zero list; default checkpoints/zeta_zeros_2000.json),
CASCADE_OUT (JSON record of every trial; default constrained_prolate.json).
Precision: the Legendre-basis Bessel evaluations lose ~n/2 nats at order n ~
argument, so prec must exceed ~0.75*nmax bits plus the digits wanted (256 bits
is enough for delta <= 1.4 with theta_c <= 2.5; 512 for delta <= 2.3).
Research instrument (Addendum 439): cited by no paper surface, keyed by nothing.
"""
import sys, math, json, os, time
import numpy as np
from flint import arb, arb_mat, ctx
from mpmath import mp, mpf, matrix, eigsy, log, sqrt

HERE = os.path.dirname(os.path.abspath(__file__))
RECS = []
ZEROS = [float(z) for z in json.load(open(os.environ.get("CASCADE_ZEROS", os.path.join(HERE, "checkpoints", "zeta_zeros_2000.json"))))]
OUT = os.environ.get("CASCADE_OUT", "constrained_prolate.json")

def _grid(name, default):
    v = os.environ.get(name)
    return tuple(float(x) for x in v.split(",")) if v else default
THC = _grid("CASCADE_THC", (1.0, 1.3, 1.6, 2.0, 2.5))       # band radii T_c/T_0
THD = _grid("CASCADE_THD", (0.8, 1.0, 1.2, 1.4, 1.7, 2.0, 2.5, 3.0))   # dodging radii T_d/T_0
THC_MAX = max(THC)                                            # sets the Legendre basis size

def gl(n):
    """Gauss-Legendre nodes and weights on [-1, 1] as arb balls at working precision
    (numpy's double-precision nodes cap a band Gram's accuracy at ~1e-16, which is
    fatal for concentration eigenvalues 1 - lambda ~ e^{-2c})."""
    out = [arb.legendre_p_root(n, k, weight=True) for k in range(n)]
    return [r for r, w in out], [w for r, w in out]

def setup(delta, nz, prec):
    """Legendre-basis Fourier tables (even sector): Gz (m x nz) at the zeros, the
    tail nodes, and a band-integral quadrature builder."""
    a = arb(delta)/2
    zs = [arb(z) for z in ZEROS[:nz]]
    T0 = 2*arb.pi()*arb(delta).exp()
    nmax = 2*(int(float((2*a*THC_MAX*T0/arb.pi()).mid())) + 35)
    ns = list(range(0, nmax, 2)); m = len(ns)
    fac = [(arb(2*n + 1)/(2*a)).sqrt()*a*2 for n in ns]
    sgn = [1 if n % 4 == 0 else -1 for n in ns]
    def jn(n, x):
        x = a*x
        return (arb.pi()/(2*x)).sqrt()*x.bessel_j(arb(n) + arb(1)/2)
    def G_at(points, weights=None):
        M = arb_mat(m, len(points))
        for i, n in enumerate(ns):
            for k, r in enumerate(points):
                v = sgn[i]*fac[i]*jn(n, r)
                M[i, k] = v*weights[k] if weights is not None else v
        return M
    Gz = G_at(zs)
    gmax = zs[-1]
    edges = [gmax*(arb(200)**(arb(i)/50)) for i in range(51)]
    xg, wg = gl(16)
    rs = []; ws = []
    for lo, hi in zip(edges[:-1], edges[1:]):
        for xx, ww in zip(xg, wg):
            rs.append((hi - lo)/2*xx + (hi + lo)/2); ws.append((hi - lo)/2*ww)
    dens = [(r/(2*arb.pi())).log()/(2*arb.pi()) for r in rs]
    Gt = G_at(rs, [(ws[k]*dens[k]).sqrt() for k in range(len(rs))])
    Zmat = 2*(Gz*Gz.transpose() + Gt*Gt.transpose())
    def band(T):
        """K_T in the basis: (1/2pi) int_{-T}^{T} ghat_j ghat_k = (1/pi) int_0^T."""
        xg2, wg2 = gl(64)
        ncell = max(8, int(float((a*arb(T)).mid())/2) + 8)
        pts = []; wts = []
        for ci in range(ncell):
            lo = arb(T)*ci/ncell; hi = arb(T)*(ci + 1)/ncell
            for xx, ww in zip(xg2, wg2):
                pts.append((hi - lo)/2*xx + (hi + lo)/2); wts.append((hi - lo)/2*ww)
        Gb = G_at(pts, [(w/arb.pi()).sqrt() for w in wts])
        return Gb*Gb.transpose()
    return a, zs, ns, m, Gz, Zmat, band

def to_mp(A, m, n, dps):
    M = matrix(m, n)
    for i in range(m):
        for j in range(n):
            M[i, j] = mpf(A[i, j].mid().str(dps + 10, radius=False))
    return M

def run(delta, prec, dps, nz=2000):
    with ctx.workprec(prec):
        mp.dps = dps
        a, zs, ns, m, Gz, Zmat, band = setup(delta, nz, prec)
        Zm = to_mp(Zmat, m, m, dps)
        E, Q = eigsy(Zm)
        k0 = min(range(m), key=lambda i: E[i]); lam1 = E[k0]
        T0 = 2*math.pi*math.exp(delta)
        Gzm = to_mp(Gz, m, len(zs), dps)
        print(f"delta {delta}: lambda_1 = {mp.nstr(lam1, 6)}  ln = {float(log(lam1)):.3f}  T0 = {T0:.2f}  m = {m}", flush=True)
        best = None
        for thc in THC:
            Tc = thc*T0
            Km = to_mp(band(Tc), m, m, dps)
            # unconstrained prolate leakage
            Ek, Qk = eigsy(Km); kk = max(range(m), key=lambda i: Ek[i]); L0 = 1 - Ek[kk]
            for thd in THD:
                Td = thd*T0
                idx = [k for k, z in enumerate(ZEROS[:nz]) if z < Td]
                K = len(idx)
                if K >= m - 2: continue
                if K:
                    V = matrix(m, K)
                    for j, k in enumerate(idx):
                        for i in range(m): V[i, j] = Gzm[i, k]
                    # projector onto the complement of span V (Gram-Schmidt)
                    Qv, R = mp.qr(V)              # mpmath returns the FULL m x m Q: keep the K columns spanning V
                    Qv = Qv[:, :K]
                    P = mp.eye(m) - Qv*Qv.T
                    A_ = P*Km*P
                else:
                    A_ = Km
                Ea, Qa = eigsy(A_); ka = max(range(m), key=lambda i: Ea[i])
                L = 1 - Ea[ka]
                g = Qa[:, ka]
                # the trial's exact zero-side value (rigorous upper bound on lambda_1)
                Qg = (g.T*Zm*g)[0, 0]/(g.T*g)[0, 0]
                rec = (float(log(Qg)), thc, thd, K, float(-log(L)) if L > 0 else float('inf'), float(-log(L0)) if L0 > 0 else float('inf'))
                if best is None or rec[0] < best[0]: best = rec
                RECS.append(dict(delta=delta, thc=thc, thd=thd, K=K, mlnL=rec[4], mlnL0=rec[5], lnQ=rec[0], lnlam1=float(log(lam1)), aTc=float(a.mid())*Tc))
                json.dump(RECS, open(OUT, 'w'), indent=0)
                print(f"   theta_c {thc:5.2f} theta_d {thd:4.2f} K {K:3d} | -ln L {rec[4]:8.2f}  (2aTc = {float(a.mid())*2*Tc:7.2f}, prolate -ln L0 {rec[5]:7.2f}) | ln Q(trial) {rec[0]:9.3f}", flush=True)
        lnQ, thc, thd, K, mlnL, mlnL0 = best
        print(f"  BEST trial: theta_c {thc} theta_d {thd} K {K}: ln Q = {lnQ:.3f} vs ln lambda_1 = {float(log(lam1)):.3f} (gap {lnQ - float(log(lam1)):.2f}); "
              f"-ln L = {mlnL:.2f} = {mlnL/(2*float(a.mid())*thc*T0):.3f} x 2aTc; dodging cost {mlnL0 - mlnL:.2f}", flush=True)

if __name__ == "__main__":
    prec = int(sys.argv[1]); dps = int(sys.argv[2])
    for d in [float(s) for s in sys.argv[3:]]:
        t0 = time.time(); run(d, prec, dps); print(f"  ({time.time()-t0:.0f}s)", flush=True)
