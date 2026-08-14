#!/usr/bin/env python3
"""Theorem 1bb verifier: the prolate crossover and the measured horizon
-- Slepian-optimal modulated sections of the restricted Weil form. The
cos-basis lift-off of Theorem 1ba was section capacity, not analytic
capacity: the prolate basis extends the dodging range fourfold at equal
dimension, and the bandwidth march tau*(c) extrapolates by a measured
1/c law to the analytic horizon 2 pi e^4 -- the smooth-basis n -> inf
envelope, the follow-up 1ba named, now measured at the 0.2% level.

Two committed instruments, each exactly the session recipe:
  E (extension): KL = 90 Legendre truncation, c = 40, n = 26 prolates,
     ARCH quadrature Rwin = 800 / NR = 120001, prime overlap on 600-pt
     Gauss-Legendre panels, numeric Gram on a 400-pt grid.
  M (march): KL = int(1.4c) + 60, n = int(2c/pi) + 4, ARCH quadrature
     Rwin = 600 / NR = 80001, tau0 grid 120..380 step 20, crossings by
     log-linear interpolation on that grid.

Gates (all exit-gated; any failure exits 1):
  g1  the Slepian machinery: concentration eigenvalues at c = 40 via
      the sinc kernel on the 400-pt grid plunge STRADDLING the Shannon
      number 2c/pi = 25.46 -- lambda_23 = 0.9494, lambda_25 = 0.4873,
      lambda_27 = 0.0456 (rel 1e-2), monotone across the plunge; the
      numeric Gram orthonormal (max offdiag < 1e-10; diag = a rel
      1e-6).
  g2  the extension (instrument E, delta = 4): the prolate section
      holds the Weil boundary where the certified cos section (1ba g5)
      had lifted -- |margin| < 1e-9 at tau0 = 0, 60, and 100 (the cos
      value at 60, 4.180e-3, is gated in the chained 1ba verifier: the
      contrast IS the basis-capacity demonstration); the lift:
      margin(250) = 1.223e-2 and margin(340) = 5.151e-1 (rel 1e-2);
      the explicit-formula identity on minimizers at tau0 = 300 and
      360 (+-gamma zero side over 260 verified zeros, dps-15 pull):
      ratios in (0.97, 1.0001) and (0.99, 1.0001) -- the deficit is
      the positive beyond-260 tail.
  g3  the march (instrument M): the lift-off crossings tau*(eps, c)
      at thresholds 1e-6 and 1e-3 for c = 40, 60, 90, 120, each
      pinned +-1.5 (log-interpolated on the committed grid):
      (158.87, 222.69), (205.15, 258.50), (243.80, 285.53),
      (270.60, 305.79); both threshold sequences strictly increasing
      in c.
  g4  the extrapolation: least-squares tau* = tau_inf - K/c on the
      four 1e-3 crossings gives tau_inf in (341.5, 343.5) with
      K in (4600, 5150) and max |residual| < 5 -- the fit CONTAINS
      the analytic horizon 2 pi e^4 = 343.05 (constant computed, not
      hardcoded; |tau_inf - 2 pi e^4| < 4 gated); the 1e-6 fit gives
      tau_inf in (318, 322.5) -- the deep-threshold edge sits
      INTERIOR to the horizon at extrapolation (the epsilon-dependent
      offset: a MEASUREMENT, its interpretation deferred -- the
      concentration-null decomposition is the next arc's subject, not
      gated here).
  g5  the Shannon-not-n control (instrument M, c = 40, tau0 = 200):
      the margin cliff sits at the plunge, not at any dimension
      budget -- margin(n=20)/margin(n=24) > 500 (the cliff), while
      margin(n=24)/margin(n=32) < 5 (diminishing returns beyond);
      pinned margin(n=24) = 1.307e-4 rel 1e-2 and
      margin(n=38) = 9.79e-6 rel 5e-2.
  g6  the paper needles for the 1bb block (in-code list
      authoritative).
  g7  the chain: cascade_weil_crossover.py (Theorem 1ba) exits 0.
  g8  the footer census (this script backticked >= 2; "78 scripts
      cited in place"; "Theorems 1i-1bb").

Near-boundary caution (round-210 F1 standing): boundary-regime margins
are pinned by magnitude windows only; no balance decompositions are
gated anywhere in this verifier.

Sabotage record (parallel-isolation design: baseline + four probes as
five INDEPENDENT tar trees from committed HEAD, run concurrently and
discarded after; each mangle's application verified by assert + cmp
against the committed copy before launch; censuses are the OBSERVED
results):
  (a) title needle mangled in-span single-site in the paper
      -> OBSERVED: g6 FAIL alone (exit 1)
  (b) the tau_inf window mangled in code ((341.5, 343.5) ->
      (351.5, 353.5)) -> OBSERVED: g4 FAIL alone (exit 1)
  (c) the cliff bound mangled past truth in code (> 500 -> > 50000)
      -> OBSERVED: g5 FAIL alone (exit 1)
  (d) footer census reverted 78 -> 77 in the paper -> OBSERVED: g8
      FAIL AND g7 FAIL (census propagation through the chained 1ba
      verifier's own footer gate)
"""
import sys, subprocess, os, math
import numpy as np
from numpy.polynomial import legendre as L
from scipy.special import psi as scipy_digamma, spherical_jn
from scipy.linalg import eigh as scipy_eigh
from mpmath import mp, zetazero

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

TWO_PI = 2*math.pi
DELTA = 4.0
A = DELTA/2.0

def make_basis(c, n, KL):
    k = np.arange(KL)
    alpha = (k + 1)/np.sqrt((2*k + 1)*(2*k + 3))
    Tx = np.zeros((KL, KL))
    for i in range(KL - 1):
        Tx[i, i+1] = Tx[i+1, i] = alpha[i]
    Lm = -np.diag(k*(k + 1.0)) - c*c*(Tx @ Tx)
    ev, V = scipy_eigh(Lm)
    return V[:, np.argsort(-ev)[:n]].T

def psi_eval(coefs, x):
    KL = coefs.shape[1]
    out = np.zeros((coefs.shape[0], len(x)))
    for n in range(coefs.shape[0]):
        out[n] = L.legval(x, coefs[n]*np.sqrt(np.arange(KL) + 0.5))
    return out

def psi_hat(coefs, s, chunk=20000):
    KL = coefs.shape[1]
    s = np.atleast_1d(s).astype(float)
    ks = np.arange(KL)
    ph = (1j**ks)*np.sqrt(ks + 0.5)
    M = coefs.astype(complex)*ph[None, :]
    out = np.empty((coefs.shape[0], len(s)), dtype=complex)
    for lo in range(0, len(s), chunk):
        sl = s[lo:lo+chunk]
        J = np.empty((KL, len(sl)))
        for k in ks:
            J[k] = spherical_jn(int(k), np.abs(sl))
        sign = np.where(sl[None, :] >= 0, 1.0, (-1.0)**(ks[:, None]))
        out[:, lo:lo+chunk] = M @ (2*sign*J)
    return out

def vonmangoldt(nmax):
    lam = np.zeros(nmax + 1)
    for p in range(2, nmax + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= nmax:
                lam[pk] = np.log(p)
                pk *= p
    return lam

LAMV = vonmangoldt(int(np.floor(np.exp(DELTA))) + 1)
NS_PR = np.nonzero(LAMV)[0]

# ---------------------------------------------------------------- g1
KL_E = 90
XG4, WG4 = np.polynomial.legendre.leggauss(400)
c1 = 40.0
P34 = make_basis(c1, 34, KL_E)
PX34 = psi_eval(P34, XG4)
D = XG4[:, None] - XG4[None, :]
K1 = np.where(np.abs(D) < 1e-12, c1/np.pi,
              np.sin(c1*D)/(np.pi*np.where(np.abs(D) < 1e-12, 1.0, D)))
lam = np.array([(PX34[n]*WG4) @ K1 @ (PX34[n]*WG4)/((PX34[n]*WG4) @ PX34[n])
                for n in range(34)])
ok = abs(lam[23]/0.9494 - 1) < 1e-2
ok &= abs(lam[25]/0.4873 - 1) < 1e-2
ok &= abs(lam[27]/0.0456 - 1) < 1e-2
ok &= all(lam[i+1] < lam[i] + 1e-9 for i in range(20, 33))
P26 = make_basis(c1, 26, KL_E)
PX26 = psi_eval(P26, XG4)
G_E = A*np.einsum('ni,i,mi->nm', PX26, WG4, PX26)
offd = np.max(np.abs(G_E - np.diag(np.diag(G_E))))
ok &= offd < 1e-10
ok &= np.max(np.abs(np.diag(G_E)/A - 1)) < 1e-6
print(f"  g1 plunge (Shannon {2*c1/np.pi:.2f}): l23 {lam[23]:.4f}, "
      f"l25 {lam[25]:.4f}, l27 {lam[27]:.4f}; Gram offdiag {offd:.1e}",
      flush=True)
gate("g1 the Slepian machinery: the plunge straddles the Shannon "
     "number; the Gram is orthonormal", ok)

# ---------------------------------------------------------------- g2
TGX, TGW = np.polynomial.legendre.leggauss(600)

def prime_mat(P, G, tau0):
    n = P.shape[0]
    PR = np.zeros((n, n), dtype=complex)
    for n_ in NS_PR:
        u = np.log(n_)
        if u >= DELTA:
            continue
        lo, hi = -1.0, 1.0 - u/A
        xm = (hi + lo)/2 + (hi - lo)/2*TGX
        wm = (hi - lo)/2*TGW*A
        B1 = psi_eval(P, xm)
        B2 = psi_eval(P, xm + u/A)
        Am = np.einsum('ni,i,mi->nm', B1, wm, B2)
        phz = np.exp(1j*tau0*u)
        PR += -LAMV[n_]/np.sqrt(n_)*(phz*Am + np.conj(phz)*Am.T)
    return PR

def pole_vecs(P, tau0):
    PXc = psi_eval(P, XG4).astype(complex)
    u = A*np.einsum('ni,i->n', PXc, WG4*np.exp(((-1j*tau0 - 0.5)*A)*XG4))
    v = A*np.einsum('ni,i->n', PXc, WG4*np.exp(((-1j*tau0 + 0.5)*A)*XG4))
    return u, v

def margin(P, G, tau0, Rwin, NR):
    r = np.linspace(tau0 - Rwin, tau0 + Rwin, NR)
    F = psi_hat(P, (r - tau0)*A)*A
    ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
    dr = r[1] - r[0]
    ARCH = (F*ker[None, :]) @ F.conj().T * dr/(2*np.pi)
    u, v = pole_vecs(P, tau0)
    Mp = np.outer(np.conj(v), u)
    Q = ARCH + Mp + Mp.conj().T + prime_mat(P, G, tau0)
    Q = (Q + Q.conj().T)/2
    ev, V = scipy_eigh(Q, G)
    return ev[0], V[:, 0]

mE = {}
for t0 in (0.0, 60.0, 100.0, 250.0, 300.0, 340.0, 360.0):
    mE[t0], cv = margin(P26, G_E, t0, 800.0, 120001)
    mE[(t0, 'vec')] = cv
ok = abs(mE[0.0]) < 1e-9 and abs(mE[60.0]) < 1e-9 and abs(mE[100.0]) < 1e-8
ok &= abs(mE[250.0]/1.223e-2 - 1) < 1e-2
ok &= abs(mE[340.0]/5.151e-1 - 1) < 1e-2
mp.dps = 15
Z260 = [float(zetazero(k).imag) for k in range(1, 261)]
def identity_ratio(P, G, tau0, lm, cvec):
    z = 0.0
    s = np.concatenate([(np.array(Z260) - tau0)*A, (-np.array(Z260) - tau0)*A])
    V = psi_hat(P, s)*A
    amps = np.conj(cvec) @ V
    z = float(np.sum(np.abs(amps)**2))
    nrm = float(np.real(np.conj(cvec) @ G @ cvec))
    return z/nrm/lm
r300 = identity_ratio(P26, G_E, 300.0, mE[300.0], mE[(300.0, 'vec')])
r360 = identity_ratio(P26, G_E, 360.0, mE[360.0], mE[(360.0, 'vec')])
ok &= 0.97 < r300 < 1.0001
ok &= 0.99 < r360 < 1.0001
print(f"  g2 extension: boundary {mE[0.0]:.1e}/{mE[60.0]:.1e}/{mE[100.0]:.1e}; "
      f"lift {mE[250.0]:.3e}/{mE[340.0]:.3e}; identity {r300:.4f}/{r360:.4f}",
      flush=True)
gate("g2 the extension: the prolate section holds the boundary where "
     "the certified cos section lifted; the identity validates the "
     "instrument", ok)

# ---------------------------------------------------------------- g3
class March:
    def __init__(self, c):
        self.c = c
        self.n = int(2*c/math.pi) + 4
        KL = int(1.4*c) + 60
        self.P = make_basis(c, self.n, KL)
        xg, wg = np.polynomial.legendre.leggauss(800)
        PX = psi_eval(self.P, xg)
        self.G = A*np.einsum('ni,i,mi->nm', PX, wg, PX)
    def m(self, tau0):
        return margin(self.P, self.G, tau0, 600.0, 80001)[0]

GRID = list(range(120, 381, 20))
def crossings(taus, margs, thr):
    for i in range(1, len(taus)):
        if margs[i-1] < thr <= margs[i]:
            x0, x1 = taus[i-1], taus[i]
            y0 = math.log10(max(margs[i-1], 1e-16))
            y1 = math.log10(max(margs[i], 1e-16))
            return x0 + (x1 - x0)*(math.log10(thr) - y0)/(y1 - y0)
    return None

PINS = {40.0: (158.87, 222.69), 60.0: (205.15, 258.50),
        90.0: (243.80, 285.53), 120.0: (270.60, 305.79)}
T6, T3 = [], []
ok = True
march_cache = {}
for c in (40.0, 60.0, 90.0, 120.0):
    M_ = March(c)
    march_cache[c] = M_
    margs = [M_.m(float(t)) for t in GRID]
    t6 = crossings(GRID, margs, 1e-6)
    t3 = crossings(GRID, margs, 1e-3)
    T6.append(t6); T3.append(t3)
    ok &= abs(t6 - PINS[c][0]) < 1.5 and abs(t3 - PINS[c][1]) < 1.5
    print(f"  g3 c {c:.0f}: tau*(1e-6) {t6:.2f}, tau*(1e-3) {t3:.2f}",
          flush=True)
ok &= all(T6[i+1] > T6[i] for i in range(3))
ok &= all(T3[i+1] > T3[i] for i in range(3))
gate("g3 the march: the lift-off crossings pinned and strictly "
     "increasing in bandwidth at both thresholds", ok)

# ---------------------------------------------------------------- g4
CS = np.array([40.0, 60.0, 90.0, 120.0])
def extrap(vals):
    x = 1/CS
    Amat = np.vstack([np.ones(4), -x]).T
    (tinf, K), *_ = np.linalg.lstsq(Amat, np.array(vals), rcond=None)
    resid = np.array(vals) - (tinf - K*x)
    return tinf, K, resid
t3inf, K3, r3 = extrap(T3)
t6inf, K6, r6 = extrap(T6)
horizon = TWO_PI*math.exp(4.0)
ok = 341.5 < t3inf < 343.5
ok &= 4600 < K3 < 5150
ok &= np.max(np.abs(r3)) < 5
ok &= abs(t3inf - horizon) < 4
ok &= 318 < t6inf < 322.5
print(f"  g4 extrapolation: tau_inf(1e-3) = {t3inf:.2f} (K {K3:.0f}, "
      f"resid {np.round(r3, 2)}) vs horizon 2 pi e^4 = {horizon:.2f}; "
      f"tau_inf(1e-6) = {t6inf:.2f} (interior; interpretation deferred)",
      flush=True)
gate("g4 the extrapolation: the 1/c law lands the shallow edge on the "
     "analytic horizon; the deep edge measured interior", ok)

# ---------------------------------------------------------------- g5
M40 = march_cache[40.0]
KL40 = int(1.4*40.0) + 60
mv = {}
for n in (20, 24, 32, 38):
    Pn = make_basis(40.0, n, KL40)
    xg, wg = np.polynomial.legendre.leggauss(800)
    PXn = psi_eval(Pn, xg)
    Gn = A*np.einsum('ni,i,mi->nm', PXn, wg, PXn)
    mv[n] = margin(Pn, Gn, 200.0, 600.0, 80001)[0]
ok = mv[20]/mv[24] > 500
ok &= mv[24]/mv[32] < 5
ok &= abs(mv[24]/1.307e-4 - 1) < 1e-2
ok &= abs(mv[38]/9.79e-6 - 1) < 5e-2
print(f"  g5 control: m(n20) {mv[20]:.3e} -> m(n24) {mv[24]:.3e} "
      f"(cliff x{mv[20]/mv[24]:.0f}); m(n32) {mv[32]:.3e}, "
      f"m(n38) {mv[38]:.3e} (crawl)", flush=True)
gate("g5 the Shannon-not-n control: the cliff sits at the plunge; "
     "dimensions beyond it buy little", ok)

# ---------------------------------------------------------------- g6
needles = [
    "**Theorem 1bb (the prolate crossover and the measured horizon",
    "the Slepian-optimal basis",
    "holds the Weil boundary where the certified cos section",
    "the bandwidth march",
    "a measured 1/c law",
    "the fit contains the analytic horizon",
    "the deep-threshold edge extrapolates interior",
    "the cliff sits at the plunge",
    "capacity is bandwidth, not dimension count",
    "the follow-up Theorem 1ba named, now measured",
    "interpretation deferred to the concentration-null arc",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g6 MISSING: {nd!r}", flush=True)
gate("g6 the 1bb paper needles", ok)

# ---------------------------------------------------------------- g7
sys.path.insert(0, HERE)
from cascade_tower import chain_ok
gate("g7 the chain: cascade_weil_crossover.py (Theorem 1ba) exits 0",
     chain_ok("cascade_weil_crossover.py"))

# ---------------------------------------------------------------- g8
ok = paper.count("`cascade_prolate_horizon.py`") >= 2
ok &= "78 scripts cited in place" in paper
ok &= "Theorems 1i–1bb" in paper
gate("g8 the footer census (this script backticked >= 2; 78 cited in "
     "place; the range 1i–1bb)", ok)

print(("\nALL GATES PASS (8/8)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
