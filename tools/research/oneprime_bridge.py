#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE A -- the Connes-Consani bridge.

Commission: "lets set the foundations with stage A" (the staged plan
in oneprime_notes.py). Deliverable: the exact, gated map between
Connes-Consani's semi-local Weil quadratic form (the numerical
object of "Spectral triples and zeta-cycles", arXiv:2106.01715,
sec 2) and this program's certified 1az section instruments
(cascade_weil_margin.py), in one normalization -- plus the
reproduction of CC's numerical anchors and the margin curve
epsilon(n, delta) across the one-prime window that Stage B1 must
lower-bound.

THE FORM (CC eq. 2.11, verbatim in our notation): for f supported
in [lambda^-1, lambda], with L = 2 log lambda,

  QW_lambda(f,f) = int |fhat(t)|^2 2 theta'(t)/(2pi) dt
                   + 2 Re( fhat(i/2) conj(fhat(-i/2)) )
                   - sum_{1<n<=lambda^2} Lambda(n) <f|V(n)f>,
  <f|V(n)g> = n^{-1/2} ( (f* star g)(n) + (f* star g)(n^-1) )

on ALL of L^2([lambda^-1, lambda], d*u) -- no vanishing-condition
class (the Selecta paper's g~(0) = g~(1) = 0 conditions belong to
its trace-formula framework, not to these numerics; this file's
first version transplanted them into the anchors and the anchors
failed to reproduce -- the correction is on the record below). The
form splits by parity under u -> u^-1 into sigma+ (even) + sigma-
(odd) (their sec 2.1: "QW_lambda = QW+_lambda + QW-_lambda,
according to the parity of f and g with respect to the symmetry
operator u -> u^-1").

THE DICTIONARY.
  Variables: CC work multiplicatively (Mellin f~, sharp involution
  f#(x) = x^-1 f(x^-1), unitarity Delta^{1/2}: F(x) = x^{1/2}f(x));
  the 1az instruments work additively (F(t) = e^{t/2} f(e^t),
  Fourier Fhat(r) = f~(1/2 + ir)). Support: CC's L = 2 log lambda
  IS 1az's delta = 2a; the one-prime window is delta in
  [log 2, log 3) ~ [0.6931, 1.0986), and the certified 1az points
  delta = 0.7, 0.9 sit inside it.
  The even sector: CC's sigma+ form IS the certified 1az
  Q = ARCH + POLE + PRIME --
    arch:  kernel 2 theta'(t) = h_+(t) = -log pi
           + Re psi(1/4 + it/2) (their eq. 2.9-2.10 = the 1az
           digamma kernel; gated below as G1a);
    pole:  2 Re(fhat(i/2) conj(fhat(-i/2))): even real f has
           fhat(i/2) = fhat(-i/2) = v.c, giving 2(v.c)^2 = the 1az
           rank-one POLE = 2 v v';
    primes: <f|V(n)f> = the 1az shifted-overlap form, PRIME =
           -sum_p W_p with W_p from their eq. 2.6.
  The odd sector: sigma- is NEW to this program's instruments (the
  1az cos basis is purely even). For odd real f the pole term
  FLIPS SIGN: fhat(i/2) = -fhat(-i/2) = w.c, so the pole
  contribution is -2(w.c)^2 -- negative definite. Odd functions
  compensate with fhat(0) = 0 (spectral mass pushed away from the
  kernel's negative well around t = 0).
  The archimedean cross-check: W_R's x-integral form (their
  eq. 2.7; Selecta eq. 150) in u = log x reads
    W_R = (log 4pi + gamma) F(0)
          + int_0^{2a} [e^{u/2} F_s(u) - F(0)] du/sinh(u)
          - F(0) log coth(a)
  (F_s the even part of the cross-correlation; the last term is
  the closed-form tail of the counterterm past the support) -- a
  genuinely different computation from the digamma-kernel ARCH
  (sinh kernel on autocorrelations vs digamma kernel on
  transforms); their agreement is gate G1b.

THE ANCHORS (zeta-cycles sec 2.2-2.4, on the corrected forms):
  A1  "the contribution from the archimedean place alone ceases to
      be positive in the upper part of the interval [log 2 - 0.2,
      log 2 + 0.2]" / "ends to be positive if computed in an
      interval extending slightly beyond the value L = log 2"
      (their Figure 6): here, archimedean-alone = ARCH + POLE
      (prime terms dropped, pole kept -- the pole is the principal
      part of the explicit formula, not a place), min over both
      parities.
  A2  "the positivity is restored after that value, and precisely
      in the interval log 2 <= L < log 3, by implementing also the
      contribution of the prime p = 2": full form positive across
      the window, both parities -- and (their sec 2.4) failure
      past log 3 when p = 3's contribution is withheld.
  A3  "the positivity of the quadratic form fails if one considers
      real values of p outside an interval of size < 10^-3 around
      2" (their sec 2.3): the window in real p' of
      lambda_min(ARCH + POLE - W_{p'}) > 0, both parities, at
      several delta in the one-prime window.

FIRST-RUN RECORD (the corrected-anchor history). Version 1 of this
file computed A1/A3 on the pole-killed hyperplane v.c = 0 of the
even sector (a wrong transplant of the Selecta class conditions
into the zeta-cycles numerics). Its identity gates G0-G4 passed
unchanged (they test the dictionary, not the anchors) and its
anchor data -- kept in the checkpoint under "hyperplane" -- showed
the arch-only hyperplane margin comfortably POSITIVE through
delta = 0.75 (+0.55 at log 2) and no p' knife-edge (window wider
than [1.05, e^delta) at delta <= 0.9): on the pole-killed
hyperplane the tiny margins and the knife-edge DO NOT EXIST. That
is itself a structural finding for Stage B1: the near-null
directions of the semi-local form have v.c != 0 -- the certified
1az margins (0.0347 at 0.5, 0.00128 at 0.7) live in the
pole-cancellation directions, and any positivity proof must
control exactly those.

CHECKS. 7: everything here is classical (explicit formula, Mellin/
Fourier, digamma kernels, finite sections) -- no semiclassics.
8: no hypothesis input anywhere; pure analytic number theory.

RESULT (first two-parity run, 2026-08-21; all identity gates
asserted in code, anchor values recorded here and reproducible from
the checkpoint):
  THE DICTIONARY HOLDS, GATED. G0: the certified 1az pins
  reproduced exactly (0.034733 at delta 0.5, 0.001279 at 0.7).
  G1a: h_+ = 2 theta' at tau = 5/20/100 to full precision at dps
  30 (dev 0.0). G1b: the x-integral W_R (eq. 2.7) vs the certified
  digamma ARCH agrees at rel Frobenius 3.8e-6 - 1.3e-5 across
  delta in {0.5, 0.7, 0.9, 1.05}, BOTH parities. G2: PRIME =
  -sum_p W_p at ~1.5e-16 (identical grids; a consistency check of
  the transcription, not an independent quadrature). G3: the pole
  bridge at 4.7e-6 (even) / 9.1e-6 (odd). G4: the explicit-formula
  closure at delta 0.7 -- prime/Gamma side vs zeros side over the
  committed ledger (K = 2270, gamma <= 2796): even 0.00127857 vs
  0.00127931 (rel 5.8e-4), odd 0.07027960 vs 0.07033161 (rel
  7.4e-4) -- the odd-sector instruments, new to this program,
  validate directly against the zeros.
  THE ANCHORS REPRODUCE.
  A1 (their Figure 6): arch-alone (ARCH + POLE) margin crosses
  zero at delta in (0.74, 0.76) -- the ODD sector fails first
  (+1.15e-2 at 0.74, -1.66e-2 at 0.76); the even sector holds to
  (0.80, 0.85) (+7.5e-4 at 0.80, -1.3e-3 at 0.85). "Slightly
  beyond log 2," in the upper part of their sweep interval
  [0.493, 0.893] -- reproduced.
  A2: the full form is positive across the whole window at n = 24,
  both parities, the margin falling from 1.404e-3 (even, log 2) to
  8.616e-8 (even, 1.09); the odd margins are ~60-250x larger
  (8.008e-2 at log 2, 2.209e-5 at 1.09). THE EVEN SECTOR -- the
  certified 1az machinery -- BINDS EVERYWHERE in the window.
  A2x (their sec 2.4): with p = 3's contribution withheld the form
  stays positive at delta 1.11 (even +4.9e-8, odd +1.1e-5), the
  odd sector fails by 1.15 (-2.8e-2), the even by 1.20 (-4.6e-4)
  -- positivity fails as the support stretches past the prime
  power, reproduced.
  A3 (their sec 2.3): the real-p' positivity window around 2 (min
  over parities; the even sector is the binding one at every
  delta): width 1.10e-1 at delta 0.75, 4.23e-3 at 0.90, 1.88e-4 at
  1.02, 8.12e-5 at 1.05, 3.26e-5 at 1.09 -- the "< 10^-3
  knife-edge" reproduced for delta >~ 0.95, sharpening as the
  window top approaches; and it is strongly ASYMMETRIC: at delta
  1.09 the window is [2 - 8e-7, 2 + 3.2e-5] -- the arithmetic of 2
  is consumed ~40x more exactly from below.
  THE STAGE-B1 TARGET. The margin curve epsilon(n, delta) at
  n = 8/16/24 shows section saturation at every delta (n = 16 ->
  24 moves the margin by < 7%); the object B1 must lower-bound is
  the even-sector curve: 1.28e-3 at the certified delta = 0.7,
  1.84e-5 at 0.9, 3.05e-7 at 1.05, 8.62e-8 at 1.09. A certificate
  with explicit constants must beat THESE numbers -- near the
  window top that is a ~1e-7 target in L2-normalized units, so a
  first B1 attempt should certify a sub-window [log 2, delta_max]
  where the margin is workable (e.g. delta_max = 0.9 at 1.8e-5).
  THE HYPERPLANE OBSERVATION (version-1 data, re-recorded): on the
  pole-killed hyperplane v.c = 0 the even-sector margins are LARGE
  (arch+prime +0.554 at log 2, +4.0e-3 at 1.05, vs full
  unrestricted +1.4e-3 / +3.0e-7): the semi-local form's near-null
  directions all have v.c != 0, i.e. the tiny margins live in the
  pole-cancellation directions -- 1bf/1bg's near-exact PRIME/ARCH
  cancellation seen from the CC side. A Stage-B1 proof must
  control exactly those directions; on the pole-killed complement
  the positivity is soft.

Provenance: the even-sector constructors (fhat_matrix64,
fhat_at_imag64, vonmangoldt, build_Q64) are verbatim from
cascade_weil_margin.py (Theorem 1az, certified) with NBASE 24,
generalized by a parity switch (even: f_k = cos((k+1/2) pi t/a);
odd: f_k = sin(k pi t/a) -- both L^2-orthogonal with ||f_k||^2 =
a); gate G0 re-pins the certified g2 margins (0.034733 at delta
0.5; 0.001279 at delta 0.7) to prove the copy faithful. The zeros
ledger for the closure gate is the committed zeros380 +
ext_zeros_to chunks (gamma <= 2796). Keying law: every producing
file in every key.
"""
import hashlib, math, os, sys

import numpy as np
from scipy.special import psi as scipy_digamma
from scipy.linalg import eigh as scipy_eigh

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from fold_D import zeros380
from height_uniformity import ext_zeros_to

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSB = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "oneprime_bridge.py")}
KEYFILE = os.path.join(HERE, "oneprime_bridge.py")

LOG2, LOG3 = math.log(2.0), math.log(3.0)
EULER = 0.5772156649015329
NBASE = 24

def freqs(a, parity):
    ks = np.arange(NBASE)
    return ((ks + 0.5)*np.pi/a if parity == "even"
            else (ks + 1.0)*np.pi/a)

def basis_eval(a, parity, t):
    w = freqs(a, parity)
    return (np.cos(w[:, None]*t[None, :]) if parity == "even"
            else np.sin(w[:, None]*t[None, :]))

# ====== the certified-side constructors (1az verbatim for parity
# ====== "even"; the odd sector is their sin-basis companion)
def fhat_matrix64(a, r, parity="even"):
    """Even: fhat_k(r) (real, even in r). Odd: fhat_k(r) = i q_k(r)
    with q_k real odd; returns q_k (so that products q_i q_j =
    fhat_i conj(fhat_j) enter the forms identically)."""
    w = freqs(a, parity)[:, None]
    rr = r[None, :]
    def s(x):
        return np.sinc(x/np.pi)
    sgn = 1.0 if parity == "even" else -1.0
    return a*(s((rr - w)*a) + sgn*s((rr + w)*a))

def fhat_at_imag64(a, y, parity="even"):
    """Even: fhat_k(iy) = fhat_k(-iy). Odd: |fhat_k(+-iy)| =
    2 int_0^a sin(w t) sinh(y t) dt with fhat(iy) = -fhat(-iy);
    the returned vector is sign-definite under squaring."""
    w = freqs(a, parity)
    y = abs(y)
    if parity == "even":
        num = w*np.sin(w*a)*np.cosh(y*a) + y*np.cos(w*a)*np.sinh(y*a)
        return 2*(num/(w*w + y*y))
    num = y*np.sin(w*a)*np.cosh(y*a) - w*np.cos(w*a)*np.sinh(y*a)
    return 2*(num/(w*w + y*y))

def vonmangoldt(nmax):
    lam = np.zeros(nmax + 1)
    for p in range(2, nmax + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= nmax:
                lam[pk] = np.log(p)
                pk *= p
    return lam

def overlap_matrix(a, u, parity):
    """sym_ij int f_i(t) f_j(t+u) dt on the certified 4001-point
    t-grid convention (the 1az PRIME building block)."""
    if u >= 2*a:
        return np.zeros((NBASE, NBASE))
    tg = np.linspace(-a, a, 4001)
    dt = tg[1] - tg[0]
    mask = (tg + u <= a) & (tg + u >= -a)
    t1 = tg[mask]
    B1 = basis_eval(a, parity, t1)
    B2 = basis_eval(a, parity, t1 + u)
    gij = B1 @ B2.T * dt
    return (gij + gij.T)/2

def build_Q64(delta, Rmax=600.0, NR=120001, parity="even"):
    a = delta/2.0
    G = np.eye(NBASE)*a
    r = np.linspace(-Rmax, Rmax, NR)
    F = fhat_matrix64(a, r, parity)
    ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
    dr = r[1] - r[0]
    ARCH = (F*ker[None, :]) @ F.T * dr/(2*np.pi)
    v = fhat_at_imag64(a, 0.5, parity)
    # CC eq. 2.11 pole term 2 Re(fhat(i/2) conj(fhat(-i/2))): even
    # fhat(i/2) = fhat(-i/2) -> +2 v v'; odd fhat(i/2) = -fhat(-i/2)
    # -> -2 w w' (negative definite)
    POLE = (2.0 if parity == "even" else -2.0)*np.outer(v, v)
    nmax = int(np.floor(np.exp(delta))) + 1
    lam = vonmangoldt(nmax)
    ns = np.nonzero(lam)[0]
    PRIME = np.zeros((NBASE, NBASE))
    for n_ in ns:
        u = np.log(n_)
        if u >= delta:
            continue
        PRIME += -2*lam[n_]/np.sqrt(n_)*overlap_matrix(a, u, parity)
    Q = ARCH + POLE + PRIME
    return (Q + Q.T)/2, G, ARCH, POLE, PRIME

# ==================== the CC side (independent implementation)
def gauss_legendre(lo, hi, npts=96):
    x, w = np.polynomial.legendre.leggauss(npts)
    return 0.5*(hi - lo)*x + 0.5*(hi + lo), 0.5*(hi - lo)*w

def WR_matrix(delta, parity="even", npts=96):
    """CC eq. 2.7 / Selecta eq. 150 in the u = log x variable: the
    x-integral route (independent of the digamma-kernel ARCH)."""
    a = delta/2.0
    F0 = overlap_matrix(a, 0.0, parity)
    us, ws = gauss_legendre(0.0, 2*a, npts)
    WR = (math.log(4*math.pi) + EULER)*F0
    for u, w in zip(us, ws):
        WR = WR + w*(math.exp(u/2)*overlap_matrix(a, u, parity)
                     - F0)/math.sinh(u)
    WR = WR - F0*math.log(1.0/math.tanh(a))
    return (WR + WR.T)/2

def Wp_matrix(delta, p, parity="even"):
    """CC eq. 2.6 for one (real) p: W_p = log p sum_m p^{-m/2}
    (F(m log p) + F(-m log p)) as a quadratic form."""
    a = delta/2.0
    W = np.zeros((NBASE, NBASE))
    m = 1
    while m*math.log(p) < 2*a:
        W += 2*math.log(p)*p**(-m/2.0)*overlap_matrix(
            a, m*math.log(p), parity)
        m += 1
    return W

def Wp_all(delta, parity="even"):
    W = np.zeros((NBASE, NBASE))
    for p in range(2, int(math.exp(delta)) + 2):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            W += Wp_matrix(delta, p, parity)
    return W

def pole_matrix_cc(delta, parity="even", npts=96):
    """fhat(i/2) fhat(-i/2)-symmetrized as the u-quadrature
    4 int_0^{2a} F_s(u) cosh(u/2) du on cross-correlations
    (independent of fhat_at_imag64; the parity sign emerges from
    the correlations themselves)."""
    a = delta/2.0
    us, ws = gauss_legendre(0.0, 2*a, npts)
    P = np.zeros((NBASE, NBASE))
    for u, w in zip(us, ws):
        P = P + 4*w*math.cosh(u/2)*overlap_matrix(a, u, parity)
    return P

def relfro(X, Y):
    return float(np.linalg.norm(X - Y)/np.linalg.norm(Y))

def full_min(M, n, a):
    return float(scipy_eigh(M[:n, :n], a*np.eye(n),
                            eigvals_only=True)[0])

def hyper_min(M, v, n, a):
    """lambda_min restricted to the pole-killed hyperplane v.c = 0
    (the version-1 side observation, kept on the record)."""
    vn = v[:n]/np.linalg.norm(v[:n])
    B = np.linalg.svd(np.eye(n) - np.outer(vn, vn))[0][:, :n-1]
    return float(scipy_eigh(B.T @ M[:n, :n] @ B,
                            B.T @ (a*np.eye(n)) @ B,
                            eigvals_only=True)[0])


def run():
    params = {"deps": DEPSB, "nbase": NBASE}
    st = ckpt_key.load("oneprime_bridge", KEYFILE, params)
    if st is not None:
        return st
    st = {}

    # ------------------------------------------------ G0 provenance
    Q05, _, A05, P05, PR05 = build_Q64(0.5)
    l05 = full_min(Q05, NBASE, 0.25)
    Q07, G07, A07, P07, PR07 = build_Q64(0.7)
    l07 = full_min(Q07, NBASE, 0.35)
    print(f"G0 provenance: delta 0.5 margin {l05:.6f} (certified "
          f"0.034733), delta 0.7 margin {l07:.6f} (certified "
          f"0.001279)", flush=True)
    assert abs(l05 - 0.034733) < 1e-4, "G0 FAIL: delta 0.5 pin"
    assert abs(l07 - 0.001279) < 1e-5, "G0 FAIL: delta 0.7 pin"
    st["G0"] = {"l05": l05, "l07": l07}

    # ------------------------------------------- G1 the arch bridge
    # (a) h_+ = 2 theta' (CC eq. 2.9-2.10) at three heights
    from mpmath import mp, mpf, siegeltheta, diff as mpdiff, \
        digamma as mpdigamma, pi as mppi, log as mplog, mpc
    mp.dps = 30
    devs = []
    for tau in ("5", "20", "100"):
        t_ = mpf(tau)
        hp = -mplog(mppi) + mpdigamma(mpf("0.25") + mpc(0, 1)*t_/2).real
        tp = 2*mpdiff(siegeltheta, t_)
        devs.append(float(abs(hp - tp)/abs(tp)))
    print(f"G1a h_+ = 2 theta' rel devs: {['%.1e' % d for d in devs]}",
          flush=True)
    assert max(devs) < 1e-20, "G1a FAIL"
    st["G1a_max_dev"] = max(devs)

    # (b) the x-integral (2.7) vs the certified digamma ARCH, both
    # parities, converged quadrature (Rmax 3000)
    g1 = {}
    for parity in ("even", "odd"):
        for delta, npts in ((0.5, 96), (0.7, 96), (0.9, 128),
                            (1.05, 128)):
            WR = WR_matrix(delta, parity, npts)
            _, _, Ac, _, _ = build_Q64(delta, Rmax=3000.0, NR=600001,
                                       parity=parity)
            dev = relfro(-WR, Ac)
            g1[f"{parity}:{delta:g}"] = dev
            print(f"G1b {parity} delta {delta:g}: relfro(-WR, ARCH) "
                  f"{dev:.2e}", flush=True)
    assert max(g1.values()) < 1e-4, "G1b FAIL"
    st["G1b"] = g1

    # ------------------------------- G2 primes and G3 pole bridges
    g2 = {}
    for parity in ("even", "odd"):
        for delta in (0.7, 0.9, 1.05):
            _, _, _, _, PR = build_Q64(delta, parity=parity)
            dev = relfro(-Wp_all(delta, parity), PR)
            g2[f"{parity}:{delta:g}"] = dev
            print(f"G2 {parity} delta {delta:g}: "
                  f"relfro(-sum W_p, PRIME) {dev:.2e}", flush=True)
    assert np.linalg.norm(Wp_all(0.5)) == 0.0, \
        "G2 FAIL: prime leak below log 2"
    assert max(g2.values()) < 1e-12, "G2 FAIL"
    st["G2"] = g2

    g3 = {}
    for parity in ("even", "odd"):
        for delta in (0.5, 0.7, 0.9, 1.05):
            _, _, _, PO, _ = build_Q64(delta, parity=parity)
            dev = relfro(pole_matrix_cc(delta, parity), PO)
            g3[f"{parity}:{delta:g}"] = dev
            print(f"G3 {parity} delta {delta:g}: relfro(pole_CC, "
                  f"POLE) {dev:.2e}", flush=True)
    assert max(g3.values()) < 1e-4, "G3 FAIL"
    st["G3"] = g3

    # ------------------------- G4 the explicit-formula closure
    # (both parities at delta 0.7: the extremal's Q against the
    # zeros side over the committed ledger, gamma <= 2796; the
    # beyond-ledger tail is O(1e-10) relative)
    Z = np.concatenate([zeros380(), ext_zeros_to(2270)])
    g4 = {}
    for parity in ("even", "odd"):
        Q, G, _, _, _ = build_Q64(0.7, parity=parity)
        ev, V = scipy_eigh(Q, G)
        c = V[:, 0]
        qval = float(c @ Q @ c)
        Fz = fhat_matrix64(0.35, Z, parity)
        zside = float(2*np.sum((c @ Fz)**2))
        rd = abs(qval - zside)/abs(zside)
        g4[parity] = {"qside": qval, "zside": zside, "reldev": rd}
        print(f"G4 {parity} closure at delta 0.7: prime/Gamma side "
              f"{qval:.8f} vs zeros side {zside:.8f} (rel dev "
              f"{rd:.2e}; ledger K = {len(Z)})", flush=True)
    assert max(x["reldev"] for x in g4.values()) < 5e-3, "G4 FAIL"
    st["G4"] = g4

    # ------------------------------------ the anchors (2.11 forms)
    # A1: archimedean-alone (ARCH + POLE, primes dropped) margins,
    # both parities, fine grid through the CC sweep interval
    a1 = {}
    for delta in (0.5, 0.55, 0.6, 0.64, 0.66, 0.68, 0.6931, 0.70,
                  0.71, 0.72, 0.74, 0.76, 0.80, 0.85, 0.893):
        row = {}
        for parity in ("even", "odd"):
            _, _, Ac, PO, _ = build_Q64(delta, parity=parity)
            row[parity] = full_min(Ac + PO, NBASE, delta/2)
        a1[f"{delta:g}"] = row
        print(f"A1 delta {delta:g}: arch-alone even "
              f"{row['even']:+.4e} odd {row['odd']:+.4e}", flush=True)
    st["A1"] = a1

    # A2: full-form margins across the window, both parities; and
    # past log 3 with p = 3 withheld (their sec 2.4)
    a2, a2x = {}, {}
    for delta in (0.6931, 0.72, 0.75, 0.80, 0.90, 1.00, 1.05, 1.09):
        row = {}
        for parity in ("even", "odd"):
            Q, _, _, _, _ = build_Q64(delta, parity=parity)
            row[parity] = full_min(Q, NBASE, delta/2)
        a2[f"{delta:g}"] = row
        print(f"A2 delta {delta:g}: full even {row['even']:+.3e} "
              f"odd {row['odd']:+.3e}", flush=True)
    for delta in (1.11, 1.15, 1.20):
        row = {}
        for parity in ("even", "odd"):
            _, _, Ac, PO, _ = build_Q64(delta, parity=parity)
            W2 = Wp_matrix(delta, 2, parity)
            row[parity] = full_min(Ac + PO - W2, NBASE, delta/2)
        a2x[f"{delta:g}"] = row
        print(f"A2x delta {delta:g} (p = 3 withheld): even "
              f"{row['even']:+.3e} odd {row['odd']:+.3e}", flush=True)
    st["A2"], st["A2x"] = a2, a2x

    # A3: the knife-edge -- the positivity window in real p' around
    # 2 for the full form ARCH + POLE - W_{p'}, min over parities
    def kmargin(delta, APs, p_):
        return min(full_min(APs[par] - Wp_matrix(delta, p_, par),
                            NBASE, delta/2)
                   for par in ("even", "odd"))

    def bisect_edge(f, p_in, p_out, iters=48):
        for _ in range(iters):
            mid = (p_in + p_out)/2
            if f(mid) > 0:
                p_in = mid
            else:
                p_out = mid
            if abs(p_in - p_out) < 1e-9:
                break
        return (p_in + p_out)/2

    a3 = {}
    for delta in (0.75, 0.90, 1.02, 1.05, 1.09):
        APs = {}
        for parity in ("even", "odd"):
            _, _, Ac, PO, _ = build_Q64(delta, parity=parity)
            APs[parity] = Ac + PO
        f = lambda p_: kmargin(delta, APs, p_)
        m2 = f(2.0)
        lo = hi = float("nan")
        if m2 > 0:
            pfloor, pceil = 1.05, math.exp(delta) - 1e-9
            step = 1e-7
            while 2.0 - step > pfloor and f(2.0 - step) > 0:
                step *= 2
            lo = (float("nan") if 2.0 - step <= pfloor and
                  f(max(2.0 - step, pfloor)) > 0
                  else bisect_edge(f, 2.0 - step/2, 2.0 - step))
            step = 1e-7
            while 2.0 + step < pceil and f(2.0 + step) > 0:
                step *= 2
            hi = (float("nan") if 2.0 + step >= pceil and
                  f(min(2.0 + step, pceil)) > 0
                  else bisect_edge(f, 2.0 + step/2, 2.0 + step))
        a3[f"{delta:g}"] = {"m2": m2, "plo": lo, "phi": hi,
                            "width": hi - lo}
        print(f"A3 delta {delta:g}: margin at p = 2 {m2:+.3e}; "
              f"window [{lo:.7f}, {hi:.7f}] width {hi - lo:.2e}",
              flush=True)
    st["A3"] = a3

    # ---------------- the margin curve epsilon(n, delta) -- the
    # Stage-B1 target, in L2-normalized units, both parities
    curve = {}
    for delta in (0.5, 0.6, 0.6931, 0.7, 0.75, 0.8, 0.9, 1.0,
                  1.05, 1.09):
        row = {}
        for parity in ("even", "odd"):
            Q, _, _, _, _ = build_Q64(delta, parity=parity)
            for n in (8, 16, 24):
                row[f"{parity}_n{n}"] = full_min(Q, n, delta/2)
        curve[f"{delta:g}"] = row
        print(f"curve delta {delta:g}: even "
              f"{row['even_n8']:+.3e}/{row['even_n16']:+.3e}/"
              f"{row['even_n24']:+.3e}  odd "
              f"{row['odd_n8']:+.3e}/{row['odd_n16']:+.3e}/"
              f"{row['odd_n24']:+.3e}  (n 8/16/24)", flush=True)
    st["curve"] = curve

    # ---------------- the version-1 side observation, re-recorded:
    # pole-killed hyperplane margins (even sector) are LARGE -- the
    # near-null directions have v.c != 0
    hyp = {}
    for delta in (0.6931, 0.75, 0.9, 1.05):
        Q, _, Ac, _, PR = build_Q64(delta)
        v = fhat_at_imag64(delta/2, 0.5)
        hyp[f"{delta:g}"] = {
            "arch_only": hyper_min(Ac, v, NBASE, delta/2),
            "arch_prime": hyper_min(Ac + PR, v, NBASE, delta/2),
            "full_unrestricted": full_min(Q, NBASE, delta/2)}
        h = hyp[f"{delta:g}"]
        print(f"hyperplane delta {delta:g}: arch-only "
              f"{h['arch_only']:+.3e}, arch+prime "
              f"{h['arch_prime']:+.3e} vs full unrestricted "
              f"{h['full_unrestricted']:+.3e}", flush=True)
    st["hyperplane"] = hyp

    ckpt_key.save("oneprime_bridge", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("one-prime bridge (Stage A) complete", flush=True)
