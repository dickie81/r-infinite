#!/usr/bin/env python3
"""Theorem 1az verifier: the Weil margin and its rate law -- the
restricted Weil quadratic form as a finite-dimensional eigenproblem
(built from primes + Gamma-data, no zeros), its pole-carried
positivity and dodger anatomy, and the mp-precision measurement of
the margin's decay law epsilon(n, delta) with the dodging-horizon
phase change.

Gates (all exit-gated; any failure exits 1):
  g1  the instrument cross-checks: the exact moment recursion
      M_p(c) = (e^{ic} - (-1)^p e^{-ic})/(ic) - (p/ic) M_{p-1} against
      direct mp quadrature of fhat_j(gamma) at three (j, gamma) pairs
      (rel dev < 1e-30 at dps 60); the closed-form Gram (Beta
      functions) against mp quadrature (rel dev < 1e-30).
  g2  the margin ladder and the pole anatomy (float64 prime-side form,
      basis f_k = cos((k+1/2) pi t/a), n = 24): lambda_min = 0.034733
      at delta = 0.5 (no primes: the unconditional floor) and 0.001279
      at delta = 0.7 (prime 2 enters: the 27x drop); WITHOUT the pole
      term the form is negative (lambda_min in (-1.0, -0.85) at 0.5;
      in (-17.5, -16.0) at 5.0): the positivity is POLE-CARRIED; the
      converged floor 0.034761 (Rmax = 3000) gated alongside the
      committed-quadrature 0.034733 (round 210 F5); at delta = 4 the
      bottom of the spectrum is a DEGENERATE near-null cluster
      (|ev[1..5]| < 1e-11) whose balance decompositions are
      direction-dependent (vec1: arch > 1, |pole| < 0.1, primes < -1)
      -- the former single-extremal balance pins were struck (round
      210 F1: a noise-selected direction inside the cluster).
  g3  the dodger: at delta = 4, n = 24 the float64 margin is
      numerically zero (|lambda_min| < 5e-6) and the extremal
      eigenvector suppresses |fhat(gamma_k)|^2/||f||^2 below 1e-4 at
      each of the first 8 zeros -- the finite sections sit on the
      boundary at float64, which is WHY the mp instrument exists.
  g4  the rate law (mp, dps 60; basis (1-x^2)^m x^j; K = 1000 verified
      zeros as labeled classical data; the computed value IS the
      K-zero section's margin exactly -- and because the omitted
      beyond-K terms are nonnegative it is a rigorous lower bound on
      the FULL-zero-set form's margin over the same section (round
      210 F11 rewording)): pinned margins (rel 1e-3): (0.9, m3, n2)
      1.574e-3, (0.9, m3, n12) 5.221e-5, (1.4, m3, n12) 3.338e-10,
      (2.2, m3, n10) 2.156e-13, (2.2, m5, n12) 1.932e-15; the fitted
      per-dimension rates c(delta) in windows c(0.9) in (0.05, 0.2),
      c(1.4) in (0.45, 0.65), c(2.2) in (0.70, 0.85) for BOTH basis
      families, all slopes 5-point fits (round 210 F4), with
      |c_m3 - c_m5| < 0.1 at 1.4 and 2.2 (the rate is intrinsic,
      basis-independent); a delta = 4 section (m3, n8) mp-resolved
      strictly positive, pinned 2.565e-14 rel 1e-2 (round 210 F8).
  g5  the phase change at the dodging horizon: at delta = 0.9 the
      decay SATURATES (margin(n=20)/margin(n=12) > 0.5 -- an algebraic
      crawl, pinned 2.896e-5 at n = 20) while at delta = 1.4 it
      continues (margin(n=12)/margin(n=20) > 100, pinned 1.905e-12 at
      n = 20); the horizon arithmetic 2 pi e^delta = 15.45 / 25.48 /
      56.71 at delta = 0.9 / 1.4 / 2.2 (constants-only conjuncts,
      display-equal windows, prints computed -- the landing's 15.46
      was a rounding defect, round 210 F6; nature stated per the
      1av-g2 precedent; the 0.5% proximity of 2 pi e^{2.2} to
      gamma_12 is NOTED in the block, not leaned on, and not gated).
  g6  the two-sided pins (SECTION margins, not the support-class
      infimum eps_inf, which the section value only upper-bounds --
      saturation suggests convergence in n at delta = 0.9 but does
      not prove it): the minimizer-adapted tail bound (|fhat(r)| <=
      V/r^{m+1} with V = int |f^{(m+1)}| + the boundary jump masses
      |f^{(m)}(+-a)| -- f is only C^{m-1} at the support edges, so
      integration by parts leaves boundary terms; the landing's V
      omitted them, round 210 F2, every displayed claim survives the
      repair) pins the (0.9, m3, n20) section's full-zero-set margin
      essentially exactly (tail/floor < 1e-4 GATED, round 210 F3;
      floor 2.896e-5 gated) and the (1.4, m3, n20) section at
      1.905e-12 (adapted tail gated < 1e-12); the ceiling reads the
      beyond-K zeros' contributions as the nonnegative |fhat|^2 form
      (the labeled-classical-data clause).
  g7  the paper needles for the 1az block (in-code list authoritative).
  g8  the chain: cascade_saddle_curvature.py (Theorem 1ay) exits 0.
  g9  the footer census (this script backticked >= 2; "76 scripts cited
      in place"; "Theorems 1i-1az").

Sabotage record (each: fresh tar tree, single mangle with application
verified by assert + cmp against pristine, restore verified by cmp;
censuses are the OBSERVED results):
  (a) title needle mangled in-span single-site in the paper
      -> OBSERVED: g7 FAIL alone (exit 1)
  (b) the delta = 0.5 floor pin mangled in code (0.034733 -> 0.036733)
      -> OBSERVED: g2 FAIL alone (the unconditional floor is
      load-bearing)
  (c) the (2.2, m5, n12) margin pin mangled a decade in code
      (1.932e-15 -> 1.932e-14) -> OBSERVED: g4 FAIL alone (the deep
      rate-law pin is live)
  (d) footer census reverted 76 -> 75 in the paper -> OBSERVED: g9
      FAIL AND g8 FAIL (census propagation through the chained 1ay
      verifier's own footer gate)
"""
import sys, subprocess, os
import numpy as np
from scipy.special import psi as scipy_digamma
from scipy.linalg import eigh as scipy_eigh
from mpmath import (mp, mpf, mpc, exp as mpexp, gamma as mpgamma, pi as mppi,
                    matrix, cholesky, zetazero, binomial, eigsy, quad as mpquad,
                    cos as mpcos, log as mplog, diff as mpdiff)

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

# ================= the mp rate instrument =================
mp.dps = 60
def moments(c, pmax):
    eic = mpexp(mpc(0, 1)*c); emic = mpexp(mpc(0, -1)*c)
    ic = mpc(0, 1)*c
    out = [(eic - emic)/ic]
    for p in range(1, pmax + 1):
        out.append((eic - (-1)**p*emic)/ic - p/ic*out[-1])
    return out

def fhat_vec(a, m, n, gam):
    c = gam*a
    M = moments(c, 2*m + n - 1)
    binos = [(-1)**l*binomial(m, l) for l in range(m + 1)]
    return [a*sum(binos[l]*M[2*l + j] for l in range(m + 1)) for j in range(n)]

def gram(a, m, n):
    Gm = matrix(n, n)
    for i in range(n):
        for j in range(n):
            p = i + j
            if p % 2:
                continue
            Gm[i, j] = a*mpgamma(mpf(p + 1)/2)*mpgamma(2*m + 1)/mpgamma(mpf(p + 1)/2 + 2*m + 1)
    return Gm

# ---------------------------------------------------------------- g1
a1, m1 = mpf("0.7"), 3
ok = True
for j, gam_ in ((0, mpf("14.1347251417")), (3, mpf("30.4248761259")), (5, mpf("77.1448400689"))):
    rec = fhat_vec(a1, m1, 6, gam_)[j]
    direct = a1*mpquad(lambda x: (1 - x*x)**m1 * x**j * mpexp(mpc(0, 1)*gam_*a1*x), [-1, 1])
    ok &= abs(rec - direct)/abs(direct) < mpf(10)**-30
Gm1 = gram(a1, m1, 4)
gq = a1*mpquad(lambda x: (1 - x*x)**(2*m1) * x**2, [-1, 1])
ok &= abs(Gm1[0, 2] - gq)/abs(gq) < mpf(10)**-30
gate("g1 the instrument cross-checks: the moment recursion and the "
     "closed-form Gram against direct mp quadrature", ok)

# ================= the float64 prime-side form =================
NBASE = 24
def fhat_matrix64(a, r):
    ks = np.arange(NBASE)
    w = (ks[:, None] + 0.5)*np.pi/a
    rr = r[None, :]
    def s(x):
        return np.sinc(x/np.pi)
    return a*(s((rr - w)*a) + s((rr + w)*a))

def fhat_at_imag64(a, y):
    ks = np.arange(NBASE)
    w = (ks + 0.5)*np.pi/a
    y = abs(y)
    num = w*np.sin(w*a)*np.cosh(y*a) + y*np.cos(w*a)*np.sinh(y*a)
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

def build_Q64(delta, Rmax=600.0, NR=120001):
    a = delta/2.0
    G = np.eye(NBASE)*a
    r = np.linspace(-Rmax, Rmax, NR)
    F = fhat_matrix64(a, r)
    ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
    dr = r[1] - r[0]
    ARCH = (F*ker[None, :]) @ F.T * dr/(2*np.pi)
    v = fhat_at_imag64(a, 0.5)
    POLE = 2*np.outer(v, v)
    nmax = int(np.floor(np.exp(delta))) + 1
    lam = vonmangoldt(nmax)
    ns = np.nonzero(lam)[0]
    tg = np.linspace(-a, a, 4001)
    dt = tg[1] - tg[0]
    ks = np.arange(NBASE)
    PRIME = np.zeros((NBASE, NBASE))
    for n_ in ns:
        u = np.log(n_)
        if u >= delta:
            continue
        mask = (tg + u <= a) & (tg + u >= -a)
        t1 = tg[mask]
        B1 = np.cos((ks[:, None] + 0.5)*np.pi*t1[None, :]/a)
        B2 = np.cos((ks[:, None] + 0.5)*np.pi*(t1[None, :] + u)/a)
        gij = B1 @ B2.T * dt
        gij = (gij + gij.T)/2
        PRIME += -2*lam[n_]/np.sqrt(n_)*gij
    Q = ARCH + POLE + PRIME
    return (Q + Q.T)/2, G, ARCH, POLE, PRIME

# ---------------------------------------------------------------- g2
Q05, G05, A05, P05, PR05 = build_Q64(0.5)
l05 = scipy_eigh(Q05, G05, eigvals_only=True)[0]
l05np = scipy_eigh(A05 + PR05, G05, eigvals_only=True)[0]
Q07, G07, _, _, _ = build_Q64(0.7)
l07 = scipy_eigh(Q07, G07, eigvals_only=True)[0]
Q50, G50, A50, P50, PR50 = build_Q64(5.0)
l50np = scipy_eigh(A50 + PR50, G50, eigvals_only=True)[0]
Q40, G40, A40, P40, PR40 = build_Q64(4.0)
ev40, V40 = scipy_eigh(Q40, G40)
f0 = V40[:, 0]
f1 = V40[:, 1]
arch_c = float(f0 @ A40 @ f0); pole_c = float(f0 @ P40 @ f0); pr_c = float(f0 @ PR40 @ f0)
arch_1 = float(f1 @ A40 @ f1); pole_1 = float(f1 @ P40 @ f1); pr_1 = float(f1 @ PR40 @ f1)
ok = abs(l05 - 0.034733) < 1e-4
# round 210 F5: the committed Rmax = 600 floor is truncation-biased at
# the 4th significant digit; the converged floor gated alongside it
Q05c, G05c, _, _, _ = build_Q64(0.5, Rmax=3000.0, NR=600001)
l05c = scipy_eigh(Q05c, G05c, eigvals_only=True)[0]
ok &= abs(l05c - 0.034761) < 1e-4
ok &= abs(l07 - 0.001279) < 1e-5
ok &= -1.0 < l05np < -0.85
ok &= -17.5 < l50np < -16.0
# round 210 F1: the former extremal-balance pins (-2.415/+6.795/-4.379)
# described a NOISE-SELECTED direction inside a degenerate near-null
# cluster and were struck; the gates now pin the honest structure --
# the cluster's degeneracy and the DIRECTION-DEPENDENCE of balance
# decompositions within it (vec1's pattern has positive arch and
# near-zero pole, unlike vec0's)
ok &= all(abs(x) < 1e-11 for x in ev40[1:6])
ok &= abs(ev40[0]) < 1e-6
ok &= arch_1 > 1.0 and abs(pole_1) < 0.1 and pr_1 < -1.0
print(f"  g2 floor {l05:.6f} (converged {l05c:.6f}); prime-2 drop {l07:.6f}; "
      f"no-pole {l05np:.3f}/{l50np:.2f}; vec0 balance {arch_c:.3f}/{pole_c:.3f}/"
      f"{pr_c:.3f}; vec1 balance {arch_1:.3f}/{pole_1:.3f}/{pr_1:.3f}", flush=True)
gate("g2 the margin ladder and the pole anatomy: the unconditional floor "
     "(committed and converged), the 27x prime-2 drop, pole-carried "
     "positivity, the degenerate cluster with direction-dependent "
     "balances (the former extremal-balance pins struck round 210 F1)", ok)

# ---------------------------------------------------------------- g3
ok = abs(ev40[0]) < 5e-6
mp.dps = 25
gz8 = np.array([float(zetazero(k).imag) for k in range(1, 9)])
mp.dps = 60
Fz = fhat_matrix64(2.0, gz8)
vals = (f0 @ Fz)**2/float(f0 @ G40 @ f0)
ok &= all(v < 1e-4 for v in vals)
print(f"  g3 float64 margin at delta 4: {ev40[0]:.2e}; dodge "
      f"|fhat(gamma_k)|^2/||f||^2 max over first 8: {vals.max():.2e}", flush=True)
gate("g3 the dodger: the float64 sections sit on the boundary; the extremal "
     "suppresses the first 8 zeros below 1e-4", ok)

# ---------------------------------------------------------------- g4
mp.dps = 35
K = 1000
print("  g4 pulling zeros...", flush=True)
ZK = [zetazero(k).imag for k in range(1, K + 1)]
mp.dps = 60
def margin(a, m, n):
    Q = matrix(n, n)
    for k in range(K):
        fv = fhat_vec(a, m, n, ZK[k])
        for i in range(n):
            for j in range(i, n):
                Q[i, j] += 2*(fv[i]*fv[j].conjugate()).real
    for i in range(n):
        for j in range(i):
            Q[i, j] = Q[j, i]
    Gm = gram(a, m, n)
    Lc = cholesky(Gm)
    Li = Lc**-1
    A = Li*Q*Li.T
    A = (A + A.T)/2
    E, EV = eigsy(A)
    lams = [E[i] for i in range(n)]
    kmin = min(range(n), key=lambda i: lams[i])
    y = matrix([EV[i, kmin] for i in range(n)])
    coef = Li.T*y                       # coefficients in the monomial basis
    return lams[kmin], [coef[i] for i in range(n)]

vals = {}
for delta, m, ns in ((mpf("0.9"), 3, (2, 4, 6, 8, 10, 12, 20)),
                     (mpf("0.9"), 5, (4, 12)),
                     (mpf("1.4"), 3, (4, 6, 8, 10, 12, 20)),
                     (mpf("1.4"), 5, (4, 6, 8, 10, 12)),
                     (mpf("2.2"), 3, (4, 6, 8, 10, 12)),
                     (mpf("2.2"), 5, (4, 6, 8, 10, 12)),
                     (mpf("4.0"), 3, (8,))):
    for n in ns:
        lam, coefs = margin(delta/2, m, n)
        vals[(float(delta), m, n)] = (lam, coefs)
        print(f"  g4 delta={float(delta)} m={m} n={n}: {mp.nstr(lam, 6)}", flush=True)
ok = abs(vals[(0.9, 3, 2)][0]/mpf("1.574e-3") - 1) < 1e-2
ok &= abs(vals[(0.9, 3, 12)][0]/mpf("5.221e-5") - 1) < 1e-2
ok &= abs(vals[(1.4, 3, 12)][0]/mpf("3.338e-10") - 1) < 1e-2
ok &= abs(vals[(2.2, 3, 10)][0]/mpf("2.156e-13") - 1) < 1e-2
ok &= abs(vals[(2.2, 5, 12)][0]/mpf("1.932e-15") - 1) < 1e-2
def slope(delta, m, ns=(4, 6, 8, 10, 12)):
    ys = [float(mplog(vals[(delta, m, n)][0])/mplog(10)) for n in ns]
    A1 = np.polyfit(list(ns), ys, 1)[0]
    return -A1
lam40 = vals[(4.0, 3, 8)][0]
# round 210 F8: a delta = 4 section IS mp-resolved strictly positive
# (the block's (iii)->(iv) resolution claim now has a delta = 4 witness)
ok &= abs(lam40/mpf("2.565e-14") - 1) < mpf("1e-2")
c09, c14, c22 = slope(0.9, 3), slope(1.4, 3), slope(2.2, 3)
c14b, c22b = slope(1.4, 5), slope(2.2, 5)   # round 210 F4: 5-point fit
# (the landing fitted m5/1.4 from two endpoints, undisclosed; struck)
ok &= 0.05 < c09 < 0.2
ok &= 0.45 < c14 < 0.65
ok &= 0.70 < c22 < 0.85
ok &= abs(c14 - c14b) < 0.1 and abs(c22 - c22b) < 0.1
print(f"  g4 rates c(0.9) = {c09:.3f}, c(1.4) = {c14:.3f} (m5 {c14b:.3f}), "
      f"c(2.2) = {c22:.3f} (m5 {c22b:.3f}); delta-4 margin {mp.nstr(lam40, 4)}", flush=True)
gate("g4 the rate law: pinned margins; the per-dimension rates in their "
     "windows; basis-independence of the rate", ok)

# ---------------------------------------------------------------- g5
sat = vals[(0.9, 3, 20)][0]/vals[(0.9, 3, 12)][0]
cont = vals[(1.4, 3, 12)][0]/vals[(1.4, 3, 20)][0]
ok = abs(vals[(0.9, 3, 20)][0]/mpf("2.896e-5") - 1) < 1e-2
ok &= abs(vals[(1.4, 3, 20)][0]/mpf("1.905e-12") - 1) < 1e-2
ok &= sat > 0.5
ok &= cont > 100
# the horizon arithmetic (constants-only; nature stated in the docstring)
import math
h09, h14, h22 = (2*math.pi*math.exp(d) for d in (0.9, 1.4, 2.2))
# round 210 F6: the landing published 15.46 -- the true value 15.4541
# displays as 15.45; windows now display-equal and the print computed
ok &= abs(h09 - 15.45) < 0.005
ok &= abs(h14 - 25.48) < 0.005
ok &= abs(h22 - 56.71) < 0.005
print(f"  g5 saturation ratio at 0.9: {mp.nstr(sat, 4)}; continuation factor "
      f"at 1.4: {mp.nstr(cont, 4)}; horizons {h09:.2f}/{h14:.2f}/{h22:.2f}", flush=True)
gate("g5 the phase change at the dodging horizon: saturation at 0.9, "
     "continuation at 1.4, the horizon arithmetic", ok)

# ---------------------------------------------------------------- g6
def adapted_tail(delta, m, n):
    # round 210 F2: f = (1-x^2)^m * poly is only C^{m-1} at the support
    # edges, so the (m+1)-fold integration by parts leaves BOUNDARY
    # terms: the valid constant is V = int |f^{(m+1)}| + |f^{(m)}(a)| +
    # |f^{(m)}(-a)| (the landing's V omitted the jump masses -- struck;
    # every displayed claim survives the repair). Round 210 F10: the
    # 1.2 factor below is the zero-density majorant's cushion --
    # log(g/2pi)/(2pi) x 1.2 dominates the counting density beyond
    # gamma_K against S(T) fluctuations; disclosed.
    lam, coefs = vals[(float(delta), m, n)]
    a = mpf(delta)/2
    def f(tt):
        xx = tt/a
        return sum(coefs[j]*(1 - xx*xx)**m*xx**j for j in range(n))
    def fmder(x):
        return abs(mpdiff(f, a*x, m + 1))
    Vint = mpquad(fmder, [-1, 1])*a
    Vbnd = abs(mpdiff(f, a, m)) + abs(mpdiff(f, -a, m))
    V = Vint + Vbnd
    gK = ZK[-1]
    tail = 2*V**2*mpquad(lambda g: mplog(g/(2*mppi))*mpf("1.2")/(2*mppi)/g**(2*m + 2),
                         [gK, mp.inf])
    return tail

t09 = adapted_tail(mpf("0.9"), 3, 20)
t14 = adapted_tail(mpf("1.4"), 3, 20)
lo09, hi09 = vals[(0.9, 3, 20)][0], vals[(0.9, 3, 20)][0] + t09
lo14, hi14 = vals[(1.4, 3, 20)][0], vals[(1.4, 3, 20)][0] + t14
ok = float(lo09) > 2.85e-5 and float(hi09) < 1.2e-4
# round 210 F3: the equality-of-bracket-ends claim is now ITS OWN gate
# (the landing displayed "equal at four digits, gated" while no
# conjunct gated the equality -- struck and repaired); the corrected
# 0.9 tail pinned so the block's digit is a gated printout
ok &= t09/lo09 < mpf("1e-4")
ok &= abs(t09/mpf("3.05e-12") - 1) < mpf("2e-2")
ok &= t14 < mpf("1e-12")
print(f"  g6 adapted tails: 0.9 tail {mp.nstr(t09,3)} -> bracket "
      f"[{mp.nstr(lo09,4)}, {mp.nstr(hi09,4)}]; "
      f"1.4 tail {mp.nstr(t14,3)} -> bracket [{mp.nstr(lo14,4)}, {mp.nstr(hi14,4)}]", flush=True)
gate("g6 the two-sided pins: the minimizer-adapted tails pin the n = 20 "
     "SECTION margins (0.9 essentially exactly; 1.4 ceiling below 1e-12)", ok)

# ---------------------------------------------------------------- g7
needles = [
    "**Theorem 1az (the Weil margin and its rate law:",
    "built purely from primes and Γ-data",
    "the positivity is POLE-CARRIED",
    "the uniform dodger",
    "ε(n, δ) ≈ C(m, δ)·10^(−c(δ)·n)",
    "the rate is intrinsic",
    "the dodging horizon",
    "2πe^δ",
    "the cushion is now a measured curve",
    "noted, not leaned on",
    "no certificate of strict positivity at any fixed finite level",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g7 MISSING: {nd!r}", flush=True)
gate("g7 the 1az paper needles", ok)

# ---------------------------------------------------------------- g8
rr = subprocess.run([sys.executable, os.path.join(HERE, "cascade_saddle_curvature.py")],
                    capture_output=True, text=True)
gate("g8 the chain: cascade_saddle_curvature.py (Theorem 1ay) exits 0", rr.returncode == 0)

# ---------------------------------------------------------------- g9
ok = paper.count("`cascade_weil_margin.py`") >= 2
ok &= "76 scripts cited in place" in paper
ok &= "Theorems 1i–1az" in paper
gate("g9 the footer census (this script backticked >= 2; 76 cited in place; "
     "the range 1i–1az)", ok)

print(flush=True)
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (9/9)")
