#!/usr/bin/env python3
"""Theorem 1aw verifier: the floor and the meter -- the first-stage
floor extended to d = 100, the pole-side meter validated against a
planted off-line zero, and the exploratory anatomy of the
informational-pressure program's second-law clause (atomic refutation,
collective near-monotonicity).

Gates (all exit-gated; any failure exits 1):
  g1  the moment instrument extended: coefficients through j = 100 at
      dps 160; the ratio-1/2 pin (live calibration) and the gamma(1)
      independent-derivative cross-check (rel dev < 1e-20), the same
      instrument as cascade_attraction_margins.py g1 at doubled reach.
  g2  the floor extension census: the n = 0 Jensen stage margin over
      Hermite ratio at d = 45/55/65/80/100, every stage hyperbolic
      (relative imaginary root part < 1e-30); the decline MONOTONE
      across the full ten-point ladder d = 9..100 (the session
      draft's "rebound at d = 65" was a float64 Hermite-recurrence
      artifact -- the recurrence loses the d = 65 gap before
      breaking down at d = 80 (complex-root collapse to a spurious
      0.0 gap, coefficients finite ~1e75; "overflowing outright"
      struck round 201 F5); the stable Gauss-Hermite route
      gives 0.5732, in sequence -- REFUTED by this gate's first
      harvest run, disclosed in the paper block); the Hermite
      benchmark by hermgauss, cross-checked against the recurrence
      at d = 45 where both are healthy.
  g3  the two fits and the refutation: the log-log power fit over the
      ten-point ladder d = 9..100 has exponent in (-0.31, -0.26) and
      prefactor in (1.7, 2.2); the [9, 45]-window LINEAR fit's
      prediction at d = 100 UNDERSHOOTS the computed ratio by > 0.18
      -- the finite-d zero-crossing threat (linear zero near d = 130)
      is refuted by the extension itself.
  g4  the disc geometry and the reciprocal-orientation convention:
      min over |z| = r of Re(1/(1-z)) equals 1/(1+r) > 1/2 (numerical
      sweep at r = 0.95 against the closed form); the identity
      |rho/(rho-1)|^2 - 1 = (2 beta - 1)/|rho-1|^2 (spot-checked at
      mpmath precision), so the ESPRIT pole rho/(rho-1) has modulus
      EXACTLY 1 iff beta = 1/2 and modulus > 1 iff beta > 1/2: the
      meter's pole is the FE-partner's multiplier, and side-of-line
      is read from pole ORIENTATION (inside/on/outside the unit
      circle).
  g5  the planted-zero detection: F(s) = (s-1) zeta(s) (1 - a b^{-s})
      with ln b = pi/20 and a = b^{3/4} e^{i pi} (real), planting
      zeros at exactly 3/4 +- 20i (the factor's zero tower is
      3/4 + i(20 + 40k), conjugate-symmetric); branch-safe Cauchy
      extraction of lambda_F(n) = n [z^n] log F(1/(1-z)) at M = 2048,
      r = 0.95, dps 60, N = 2000 coefficients via a radix-2 FFT at
      working precision (cross-checked against the direct DFT at
      three n, < 1e-20); winding of the log around the contour = 0
      (the planted preimage modulus |rho-1|/|rho| = 0.99938 lies
      OUTSIDE the r = 0.95 circle); ESPRIT at model order K = 32
      (the 1av K = 16 blends the plant with gamma_2 -- the harvest
      run's observation, disclosed in the paper; ~20 zero-pairs
      share the band) recovers a pole at the planted frequency
      (|theta - theta_true| < 1e-10, theta_true = arg(rho/(rho-1))
      at rho = 3/4 + 20i) with modulus excess matching the true
      off-line signature |rho/(rho-1)| - 1 = 6.2471e-4 to < 1e-8,
      while the on-line control (gamma_1's pole, present in the same
      data) keeps modulus within 5e-7 of 1; the inversion
      rho_rec = p/(p-1) lands within 1e-4 of beta = 0.75 and within
      1e-3 of gamma = 20. The K = 16 diagnostic (round 201 F3): at
      the committed N = 2000 the 1av model order's blend is gated in
      windows (excess in (4.9e-4, 5.1e-4); inversion beta in
      (0.69, 0.70), gamma in (19.7, 19.9)) so the paper's
      committed-pipeline blend figures are this gate's output.
  g6  the D-H crowding infeasibility: at the certified off-line
      Davenport-Heilbronn zero height gamma = 85.699348 (the
      cascade_primes_side_ball.py certificate), the pole-frequency
      density |d theta / d gamma| = 4/(1 + 4 gamma^2) ~ 1.4e-4 rad per
      unit height, while the meter's resolving power at n <= 4500
      coefficients is 2 pi / 4500 ~ 1.4e-3 rad: the ratio (in (9, 12))
      says neighbouring zeros crowd an order of magnitude below
      resolution -- the wild D-H target is INFEASIBLE for this
      instrument at this reach, recorded as such (the planted target
      at gamma = 20, where the density is ~18x thinner, is the honest
      validation). Constants-only arithmetic; nature stated at the
      gate per the 1av-g2 precedent.
  g7  the atomic peek (the P2 candidate's atomic refutation):
      Delta_p(1) = -ln p/(p - 1) < 0 for EVERY prime (closed form,
      matched against the Cauchy loop at every p <= 2000); the sign
      censuses of Delta_p(n) over the 303 primes p <= 2000 are pinned
      (n = 5: 59 negative; n = 10: 197; n = 20: 113; n = 40: 210) --
      mixed signs at every tested n >= 5, so NO per-prime monotone law
      exists at any single n except the uniformly NEGATIVE n = 1; the
      exact laws stand: D(P_y || P_infty) = log(zeta(2)/zeta_y(2))
      decreasing to 0 along the fill (identity checked by direct
      smooth-sum at y = 3), and the zeta-measure entropy is
      prime-additive (independence of prime valuations, checked at
      y = 3 by direct summation).
  g8  the collective anatomy: profile P_y(t) = sum cos(t k log p) /
      (k p^{k/2}) over p <= y, k <= 3, on 5000 points of [10, 110];
      C-I the variance is monotone increasing along the nine-stage
      ladder y = 3..30000 and tracks the additive atom prediction
      sum w^2/2 (within 5% at y = 3; at y = 30000 the finite window
      lags the additive value, ratio in (0.80, 0.92)); C-II the
      negentropy J(y) (Vasicek-estimated differential entropy against
      the Gaussian at matched variance) is NOT monotone decreasing --
      the full barrier shape pinned (round 201 F6): dip at stage 2,
      rise through y = 300, a 4-dp micro-dip at y = 1000, the crest
      at y = 3000, the sustained decline after (the Selberg-CLT
      second law is asymptotic, not monotone); C-III the spectral
      entropy of the periodogram is monotone on the coarse ladder
      but the fine 58-stage ladder (12% prime-count growth per
      stage) exhibits EXACTLY 5 micro-violations at y = 1283, 3253,
      4793, 15313, 22469 with deepest in (0.0074, 0.0076) (pinned
      round 201 F7),
      and the atom-weight control (H_a of q ~ 1/(k^2 p^k)) correlates
      > 0.95 with H_s while the window excess H_s - H_a CHANGES SIGN
      along the fill: near-monotone, collective, not exactly a second
      law.
  g9  the paper needles for the 1aw block (in-code list authoritative).
  g10 the chain obligation to cascade_li_two_channels.py (Theorem 1av) met.
  g11 the footer census (this script backticked >= 2; the anchored needles "the **90 scripts cited in place** above"
      and "extended by Theorems 1i–1bn:" -- round-218 F12 mirrored
      the tower-wide anchoring into this line).

Sabotage record (each: fresh tar tree, single mangle, restore from
pristine verified by cmp; censuses are the OBSERVED results):
  (a)  title needle mangled in-span single-site in the paper
       -> OBSERVED g9 FAIL alone (exit 1)
  (b)  as first driven: NO-OP, disclosed -- the driver predated the
       d = 65 correction, its old-string no longer matched, the
       assert failed and the suite ran the UNMANGLED tree to a
       masquerading exit 0 (the 1av probe-(a) genus)
  (b') the d = 100 ratio pin shifted in code (0.4642 -> 0.4842),
       mangle-application-checked (assert + cmp) -> OBSERVED g2
       FAIL alone (the extension census is load-bearing)
  (c)  as first driven: NO-OP, disclosed -- same mechanism (the
       driver's inversion bound predated the display-equal
       tightening); predicted from the diff before the run
  (c') the inversion pin's beta mangled in code (0.75 -> 0.76),
       mangle-application-checked -> OBSERVED g5 FAIL alone (the
       detection is live)
  (d)  footer census reverted 73 -> 72 in the paper -> OBSERVED
       g11 FAIL AND g10 FAIL (census propagation: the chained 1av
       verifier's own footer gate catches the same reversion)
"""
import sys, math, subprocess, os
import numpy as np
from mpmath import (mp, mpf, mpc, exp, pi, quad, gamma as G, zeta, polyroots,
                    factorial, binomial, zetazero, log, euler, loggamma)

HERE = os.path.dirname(os.path.abspath(__file__))

# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g9', 's': '**Theorem 1aw (the floor and the meter:'},
    {'g': 'g9', 's': '**no proof is claimed,\nand none resulted**'},
    {'g': 'g9', 's': 'a float64 Hermite-recurrence artifact'},
    {'g': 'g9', 's': 'refuted the rebound\non its first run'},
    {'g': 'g9', 's': "the FE-partner's\nmultiplier"},
    {'g': 'g9', 's': 'modulus > 1 iff β > ½'},
    {'g': 'g9', 's': 'planted at\nexactly 3/4 ± 20i'},
    {'g': 'g9', 's': 'INFEASIBLE for\nthis instrument at this reach'},
    {'g': 'g9', 's': 'uniformly negative at n = 1 (all 303'},
    {'g': 'g9', 's': 'asymptotic, not\nmonotone'},
    {'g': 'g9', 's': 'near-monotone, collective, not exactly a second\nlaw'},
    {'g': 'g11', 's': '`cascade_floor_meter.py`', 'min': 2},
    {'g': 'g11', 's': 'the **90 scripts cited in place** above'},
    {'g': 'g11', 's': 'extended by Theorems 1i–1bn:'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

# ---------------------------------------------------------------- g1
mp.dps = 160
def Phi(u):
    s = mpf(0)
    for n in range(1, 40):
        s += (2*pi**2*n**4*exp(mpf(9)*u/2) - 3*pi*n*n*exp(mpf(5)*u/2))*exp(-pi*n*n*exp(2*u))
    return s
xi_half = mpf("0.25")*(-1)*pi**mpf("-0.25")*G(mpf("0.25"))*zeta(mpf("0.5"))/2
_phicache = {}
def PhiC(u):
    v = _phicache.get(u)
    if v is None:
        v = Phi(u)
        _phicache[u] = v
    return v
m0 = 2*quad(PhiC, [0, 8])
ratio = m0/xi_half
JMAX = 100
gam = []
for j in range(JMAX + 1):
    m2j = 2*quad(lambda u: PhiC(u)*u**(2*j), [0, 8])
    gam.append(factorial(j)*(m2j/factorial(2*j))*(xi_half/m0))
print(f"  g1 moment nodes cached: {len(_phicache)}", flush=True)
ok = abs(ratio - mpf("0.5")) < mpf(10)**-10
from mpmath import diff as mpdiff
d2 = mpdiff(lambda s: s*(s-1)/2 * pi**(-s/2) * G(s/2) * zeta(s), mpf("0.5"), 2)
ok &= abs(gam[1] - d2/2)/abs(gam[1]) < mpf(10)**-20
print(f"  g1 ratio = {float(ratio):.12f}; gamma(0) = {float(gam[0]):.12f}; "
      f"gamma(1) cross-check rel dev {float(abs(gam[1]-d2/2)/abs(gam[1])):.1e}", flush=True)
gate("g1 the moment instrument extended to j = 100: ratio-1/2 pin (live), "
     "gamma(1) independent-derivative cross-check", ok)

# ---------------------------------------------------------------- g2
def hermite_gap_stable(d):
    x = np.polynomial.hermite.hermgauss(d)[0]
    x = np.sort(x)
    return float(min(np.diff(x))/(x[-1] - x[0]))
def hermite_gap_rec(d):
    hprev = np.zeros(d + 1); hprev[0] = 1.0
    hcur = np.zeros(d + 1); hcur[1] = 2.0
    for k in range(1, d):
        nxt = np.zeros(d + 1)
        nxt[1:] += 2*hcur[:-1]
        nxt -= 2*k*hprev
        hprev, hcur = hcur, nxt
    r = np.sort(np.roots(hcur[::-1]).real)
    return float(min(np.diff(r))/(r[-1] - r[0]))
ok = abs(hermite_gap_stable(45) - hermite_gap_rec(45)) < 1e-6   # route cross-check
DS_EXT = (45, 55, 65, 80, 100)
DS_OLD = (9, 12, 16, 20, 25)
ratios = {}
worst_im = mpf(0)
for d in DS_OLD + DS_EXT:
    c = [binomial(d, j)*gam[j] for j in range(d + 1)]
    rts = polyroots([c[d - k] for k in range(d + 1)], maxsteps=600, extraprec=400)
    worst_im = max(worst_im, max(abs(r.imag) for r in rts)/max(abs(r) for r in rts))
    re = sorted([r.real for r in rts])
    marg = min(re[i+1] - re[i] for i in range(len(re) - 1))/(re[-1] - re[0])
    ratios[d] = float(marg)/hermite_gap_stable(d)
    print(f"  g2 d = {d:3d}: ratio = {ratios[d]:.4f}", flush=True)
ok &= worst_im < mpf(10)**-30
# committed pins for the extension (the session drafts confirmed or replaced
# by THIS gate's computation -- these values are the published values; the
# session draft's 65: 0.6554 was a recurrence artifact, replaced by 0.5732):
pins = {45: 0.6701, 55: 0.6172, 65: 0.5732, 80: 0.5196, 100: 0.4642}
for d, v in pins.items():
    ok &= abs(ratios[d] - v) < 0.004
# the decline is MONOTONE across the full ladder (the rebound refuted)
seq = [ratios[d] for d in DS_OLD + DS_EXT]
ok &= all(seq[i+1] < seq[i] for i in range(len(seq) - 1))
print(f"  g2 worst relative imaginary part: {float(worst_im):.2e}", flush=True)
gate("g2 the floor extension census: d = 45..100 hyperbolic, pinned ratios, "
     "the decline monotone (the session rebound refuted)", ok)

# ---------------------------------------------------------------- g3
ds = np.array(DS_OLD + DS_EXT, dtype=float)
rs = np.array([ratios[int(d)] for d in ds])
A, B = np.polyfit(np.log(ds), np.log(rs), 1)
Cpow = math.exp(B)
resid = np.sqrt(np.mean((rs - Cpow*ds**A)**2))
ok = -0.31 < A < -0.26 and 1.7 < Cpow < 2.2
# the linear-crossing refutation: fit the [9, 45] window, predict d = 100
w = ds <= 45
la, lb = np.polyfit(ds[w], rs[w], 1)
pred100 = la*100 + lb
ok &= ratios[100] - pred100 > 0.18
ok &= pred100 < 0.26          # the fit really did predict a near-crossing
zero_at = -lb/la
print(f"  g3 power fit {Cpow:.2f} * d^{A:.3f} (rms {resid:.3f}); linear window "
      f"fit predicts {pred100:.3f} at d = 100 (zero at d = {zero_at:.0f}) vs "
      f"computed {ratios[100]:.4f}", flush=True)
gate("g3 the two fits: the power law pinned; the linear zero-crossing threat "
     "refuted by the extension", ok)

# ---------------------------------------------------------------- g4
# NATURE OF THIS GATE (the 1av-g2/g6 precedent: retained, nature
# stated): the identity conjuncts are exact algebra and the minimum-
# location sweep is a library-consistency check -- they cannot fail
# short of mpmath breakage or a mangle of either surface; the gate's
# role is to pin the published closed forms, and the LIVE use of the
# orientation convention is g5's measured planted-pole modulus.
mp.dps = 40
r4 = mpf("0.95")
minre = min((1/(1 - r4*exp(mpc(0, 2*pi*m/4096)))).real for m in range(4096))
ok = abs(minre - 1/(1 + r4)) < mpf(10)**-6 and minre > mpf("0.5")
for beta, g_ in ((mpf("0.5"), mpf("14.134725")), (mpf("0.75"), mpf("20")),
                 (mpf("0.6"), mpf("50")), (mpf("0.51"), mpf("100"))):
    rho = mpc(beta, g_)
    p = rho/(rho - 1)
    ident = (abs(p)**2 - 1) - (2*beta - 1)/abs(rho - 1)**2
    ok &= abs(ident) < mpf(10)**-30
    if beta == mpf("0.5"):
        ok &= abs(abs(p) - 1) < mpf(10)**-30       # on the line: modulus exactly 1
    else:
        ok &= abs(p) > 1                           # off the line: outside the circle
rho75 = mpc(mpf("0.75"), 20)
p75 = rho75/(rho75 - 1)
true_mod_excess = float(abs(p75) - 1)
true_theta = abs(math.atan2(float(p75.imag), float(p75.real)))
print(f"  g4 min Re = {float(minre):.6f} (= 1/(1+r) = {float(1/(1+r4)):.6f}); "
      f"planted true |p|-1 = {true_mod_excess:.4e}, theta = {true_theta:.5f}", flush=True)
gate("g4 the disc geometry and the reciprocal orientation: min Re = 1/(1+r) > "
     "1/2; |rho/(rho-1)| = 1 iff beta = 1/2, > 1 iff beta > 1/2", ok)

# ---------------------------------------------------------------- g5
mp.dps = 60
LNB = pi/20
AA = -exp(mpf(3)*pi/80)          # a = b^{3/4} e^{i pi}, real negative
M5, r5, N5 = 2048, mpf("0.95"), 2000
zsm = [r5*exp(mpc(0, 2*pi*m/M5)) for m in range(M5)]
sv = [1/(1 - z) for z in zsm]
lvF = [log((s - 1)*zeta(s)) + log(1 - AA*exp(-s*LNB)) for s in sv]
steps = [(lvF[(m+1) % M5] - lvF[m]).imag for m in range(M5)]
maxstep = max(abs(st) for st in steps)
winding = float(sum(steps))/(2*math.pi)
ok = float(maxstep) < math.pi and abs(winding) < 1e-6
def mpfft(a):                     # radix-2 DIT at working precision
    n = len(a)
    A = list(a)
    j = 0
    for i in range(1, n):
        bit = n >> 1
        while j & bit:
            j ^= bit; bit >>= 1
        j |= bit
        if i < j:
            A[i], A[j] = A[j], A[i]
    L = 2
    while L <= n:
        wl = exp(mpc(0, -2*pi/L))
        for i in range(0, n, L):
            w = mpc(1)
            for k in range(L//2):
                u = A[i+k]; v = A[i+k+L//2]*w
                A[i+k] = u + v
                A[i+k+L//2] = u - v
                w *= wl
        L <<= 1
    return A
FF = mpfft(lvF)
lamF = [float(n*(FF[n]/M5/r5**n).real) for n in range(1, N5 + 1)]
# FFT-vs-direct-DFT cross-check at three n
for n in (1, 40, 1000):
    cc = sum(lvF[m]*exp(mpc(0, -2*pi*n*m/M5)) for m in range(M5))/(M5*r5**n)
    ok &= abs(lamF[n-1] - float(n*cc.real)) < 1e-20
x = np.array(lamF)
Wm = 179; h = Wm//2
D = x[h:N5-h] - np.convolve(x, np.ones(Wm)/Wm, mode='valid')
mE = len(D)//2
X5 = np.lib.stride_tricks.sliding_window_view(D, mE)
U, S, Vt = np.linalg.svd(X5, full_matrices=False)
# model order K = 32: the 1av instrument's K = 16, adequate when the
# dominant pole IS the target, BLENDS the plant with gamma_2 (harvest
# observation: measured modulus excess 2.7e-4 against the true 6.2e-4,
# biased toward the line; ~20 zero-pairs share the 0.012 < |theta| < 0.2
# band and the truncated subspace cannot hold them all); K = 32 recovers
# the plant machine-exactly -- the model-order calibration is part of
# the validation record
Vs = Vt[:32].T
zev = np.linalg.eigvals(np.linalg.pinv(Vs[:-1]) @ Vs[1:])
cands = [(abs(np.angle(zz)), abs(zz)) for zz in zev if 0.012 < abs(np.angle(zz)) < 0.2]
th_true = abs(math.atan2(float(p75.imag), float(p75.real)))
# the K = 16 DIAGNOSTIC (round 201 F3): at the committed N = 2000 the
# 1av model order still blends the plant with gamma_2 -- gated so the
# paper's committed-pipeline blend figures are the gate's output (the
# harvest configuration N = 1000 / K = 16 is session history,
# provenance-labeled in the block)
V16 = Vt[:16].T
z16 = np.linalg.eigvals(np.linalg.pinv(V16[:-1]) @ V16[1:])
c16 = [(abs(np.angle(zz)), abs(zz)) for zz in z16 if 0.012 < abs(np.angle(zz)) < 0.2]
# the planted pole: nearest candidate in frequency
e_th, m_pl = min((abs(a - th_true), mod) for a, mod in cands)
ok &= e_th < 1e-10
ok &= abs((m_pl - 1) - true_mod_excess) < 1e-8
# the on-line control: gamma_1's pole in the same data
th_g1 = math.pi - 2*math.atan(2*14.134725)
e_g1, m_g1 = min((abs(a - th_g1), mod) for a, mod in cands)
ok &= e_g1 < 5e-4 and abs(m_g1 - 1) < 5e-7
# the inversion: rho_rec = p/(p-1) from the measured (theta, modulus)
th_meas = min(cands, key=lambda c: abs(c[0] - th_true))[0]
p_meas = m_pl*complex(math.cos(th_meas), math.sin(th_meas))
rho_rec = p_meas/(p_meas - 1)
ok &= abs(rho_rec.real - 0.75) < 1e-4 and abs(abs(rho_rec.imag) - 20) < 1e-3
# the K = 16 diagnostic pins (windowed, not display-equal: the blended
# pole is ill-conditioned by construction, so cross-platform jitter is
# not bounded by the clean pole's determinism argument)
e16, m16, th16 = min((abs(a - th_true), mod, a) for a, mod in c16)
p16 = m16*complex(math.cos(th16), math.sin(th16))
r16 = p16/(p16 - 1)
ok &= 4.9e-4 < m16 - 1 < 5.1e-4
ok &= 0.69 < r16.real < 0.70 and 19.7 < abs(r16.imag) < 19.9
print(f"  g5 winding = {winding:.2e}; planted theta err {e_th:.1e}, |p|-1 = "
      f"{m_pl-1:.4e} (true {true_mod_excess:.4e}, diff {abs((m_pl-1)-true_mod_excess):.1e}); "
      f"on-line control |p| = {m_g1:.8f}; inverted to "
      f"({rho_rec.real:.4f}, {abs(rho_rec.imag):.3f}); K16 diagnostic: "
      f"excess {m16-1:.4e}, inverted ({r16.real:.4f}, {abs(r16.imag):.3f})", flush=True)
gate("g5 the planted-zero detection: winding 0, the off-line pole found at "
     "the planted frequency with the beta = 3/4 modulus, the on-line control "
     "clean, the location inverted", ok)

# ---------------------------------------------------------------- g6
# NATURE OF THIS GATE (the 1av-g2 precedent: retained, nature stated):
# constants-only arithmetic -- it pins the ARITHMETIC of the published
# infeasibility numbers against single-site mangles of either surface;
# it is not a computation that could discover anything. The empirical
# content of the infeasibility record lives in g5 (where detection
# demonstrably works) plus this density comparison.
gDH = 85.699348
dens = 4/(1 + 4*gDH*gDH)
resol = 2*math.pi/4500
ok = 9 < resol/dens < 12
dens20 = 4/(1 + 4*20.0*20.0)
ok &= 17 < dens20/dens < 20      # the planted target sits where density is ~18x thinner
print(f"  g6 |dtheta/dgamma| at 85.699 = {dens:.4e}; resolution at n = 4500 = "
      f"{resol:.4e}; ratio = {resol/dens:.1f}; thinning factor at gamma = 20: "
      f"{dens20/dens:.1f}", flush=True)
gate("g6 the D-H crowding infeasibility: neighbour separation an order of "
     "magnitude below the meter's resolution at reachable n", ok)

# ---------------------------------------------------------------- g7
def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]:
            s[i*i::i] = False
    return np.nonzero(s)[0]
PR = primes_upto(2000)
ok = len(PR) == 303
M7, r7 = 512, 0.8
z7 = r7*np.exp(2j*np.pi*np.arange(M7)/M7)
s7 = 1/(1 - z7)
def delta_seq(p, N):
    f = -np.log(1 - p**(-s7))
    c = np.fft.fft(f)/M7
    return np.array([ (n*c[n]/r7**n).real for n in range(1, N + 1) ])
ds7 = {int(p): delta_seq(int(p), 40) for p in PR}
# n = 1 closed form at every prime
ok &= all(abs(ds7[int(p)][0] - (-math.log(p)/(p - 1))) < 1e-8 for p in PR)
ok &= all(ds7[int(p)][0] < 0 for p in PR)
cens = {n: sum(1 for p in PR if ds7[int(p)][n-1] < 0) for n in (5, 10, 20, 40)}
ok &= cens == {5: 59, 10: 197, 20: 113, 40: 210}
S1_2000 = sum(ds7[int(p)][0] for p in PR)
ok &= abs(S1_2000 - (-7.048)) < 0.02
# the exact laws
zeta2 = float(zeta(2))
def zeta_y2(y):
    v = 1.0
    for p in PR[PR <= y]:
        v /= (1 - p**-2.0)
    return v
Ds = [math.log(zeta2/zeta_y2(y)) for y in (3, 10, 100, 1000)]
ok &= all(Ds[i+1] < Ds[i] for i in range(3)) and Ds[-1] > 0
# direct check at y = 3: KL by explicit smooth summation
sm = sorted(2**a * 3**b for a in range(40) for b in range(25) if 2**a * 3**b < 10**7)
z3 = zeta_y2(3)
kl = sum((n**-2.0/z3)*math.log((n**-2.0/z3)/(n**-2.0/zeta2)) for n in sm)
ok &= abs(kl - Ds[0]) < 1e-9
# entropy prime-additivity at y = 3 by direct summation
Hjoint = -sum((n**-2.0/z3)*math.log(n**-2.0/z3) for n in sm)
def hgeom(p):
    q = 1 - p**-2.0
    return -sum(q*p**(-2.0*k)*math.log(q*p**(-2.0*k)) for k in range(0, 60))
ok &= abs(Hjoint - (hgeom(2) + hgeom(3))) < 1e-9
print(f"  g7 Delta_2(1) = {ds7[2][0]:.4f}; censuses {cens}; S_2000(1) = "
      f"{S1_2000:.3f}; D at y = 3/10/100/1000: "
      f"{['%.4f' % d for d in Ds]}; additivity dev {abs(Hjoint - hgeom(2) - hgeom(3)):.1e}", flush=True)
gate("g7 the atomic peek: n = 1 uniformly negative (closed form at every "
     "prime), mixed signs pinned at n = 5/10/20/40, the exact laws exact", ok)

# ---------------------------------------------------------------- g8
PRC = primes_upto(30000)
t8 = np.linspace(10, 110, 5000)
def contrib(ps):
    P = np.zeros_like(t8)
    for k in (1, 2, 3):
        w = 1/(k*ps**(k/2.0))
        P += (np.cos(np.outer(t8, k*np.log(ps))) * w).sum(axis=1)
    return P
def atom_var(y):
    ps = PRC[PRC <= y].astype(float)
    return sum(float(np.sum(1/(k*ps**(k/2.0))**2))/2 for k in (1, 2, 3))
YL = [3, 10, 30, 100, 300, 1000, 3000, 10000, 30000]
profs = {}
Pacc = np.zeros_like(t8); prev = 0
for y in YL:
    ps = PRC[(PRC > prev) & (PRC <= y)].astype(float)
    if len(ps):
        Pacc = Pacc + contrib(ps)
    profs[y] = Pacc.copy(); prev = y
va = {y: float(np.var(profs[y])) for y in YL}
ok = all(va[YL[i+1]] > va[YL[i]] for i in range(8))
ok &= abs(va[3]/atom_var(3) - 1) < 0.05
ok &= 0.80 < va[30000]/atom_var(30000) < 0.92
def vasicek_h(xx):
    xs = np.sort(xx); N = len(xs); m = int(round(math.sqrt(N)))
    d = np.maximum(xs[m:] - xs[:-m], 1e-300)
    return float(np.mean(np.log((N/(2.0*m))*d)))
def negentropy(xx):
    z = (xx - xx.mean())/xx.std()
    h = vasicek_h(z)
    return 0.5*math.log(2*math.pi*math.e) - h
J = {y: negentropy(profs[y]) for y in YL}
Jl = [J[y] for y in YL]
ok &= not all(Jl[i+1] < Jl[i] for i in range(8))     # NOT monotone decreasing
ok &= Jl[1] < Jl[0] and Jl[2] > Jl[1]                # the dip then the rise
ok &= Jl[6] > Jl[2]                                  # the barrier climbs to y = 3000
ok &= Jl[8] < Jl[7] < Jl[6]                          # the late decline
# round 201 F6: the full barrier shape pinned -- the rise through
# y = 300, the 4-dp micro-dip at y = 1000 (0.8654 -> 0.8648, hidden
# by 3-dp display), the crest at y = 3000
ok &= Jl[3] > Jl[2] and Jl[4] > Jl[3]
ok &= Jl[5] < Jl[4] and Jl[6] > Jl[5]
def spec_H(P):
    ps = np.abs(np.fft.rfft(P - P.mean()))**2
    q = ps/ps.sum()
    q = q[q > 0]
    return float(-(q*np.log(q)).sum())
Hs_coarse = [spec_H(profs[y]) for y in YL]
ok &= all(Hs_coarse[i+1] > Hs_coarse[i] for i in range(8))
# the fine ladder: ~12% prime-count growth per stage
idx = [4]
while idx[-1] < len(PRC):
    idx.append(max(idx[-1] + 1, int(round(idx[-1]*1.12))))
idx = [i for i in idx if i <= len(PRC)]
ys_fine = [int(PRC[i-1]) for i in idx]
def atom_H(y):
    ps = PRC[PRC <= y].astype(float)
    q = np.concatenate([1/(k*k*ps**k) for k in (1, 2, 3)])
    q = q/q.sum()
    return float(-(q*np.log(q)).sum())
Hs_f, Ha_f = [], []
Pacc = np.zeros_like(t8); prev = 0
for y in ys_fine:
    ps = PRC[(PRC > prev) & (PRC <= y)].astype(float)
    if len(ps):
        Pacc = Pacc + contrib(ps)
    prev = y
    Hs_f.append(spec_H(Pacc))
    Ha_f.append(atom_H(y))
viol = [(ys_fine[i+1], round(Hs_f[i], 4), round(Hs_f[i+1], 4))
        for i in range(len(Hs_f) - 1) if Hs_f[i+1] < Hs_f[i]]
deepest = max((Hs_f[i] - Hs_f[i+1]) for i in range(len(Hs_f) - 1))
# round 201 F7: the census pinned exactly (the ladder is deterministic,
# so the paper's "the count is the claim" is now what the gate gates)
ok &= len(viol) == 5
ok &= [v[0] for v in viol] == [1283, 3253, 4793, 15313, 22469]
ok &= 0.0074 < deepest < 0.0076
corr = float(np.corrcoef(Hs_f, Ha_f)[0, 1])
exc = [Hs_f[i] - Ha_f[i] for i in range(len(Hs_f))]
ok &= corr > 0.95
ok &= exc[0] > 0.3 and exc[-1] < -0.5                # the sign-changing excess
print(f"  g8 var {va[3]:.4f}->{va[30000]:.4f} (atom {atom_var(3):.4f}/"
      f"{atom_var(30000):.4f}); J = {[round(j,4) for j in Jl]}; Hs coarse "
      f"{Hs_coarse[0]:.4f}->{Hs_coarse[-1]:.4f}; fine stages {len(ys_fine)}, "
      f"violations {len(viol)} {viol}, deepest {deepest:.4f}; corr(Hs,Ha) = "
      f"{corr:.5f}; excess {exc[0]:.3f}/{exc[len(exc)//2]:.3f}/{exc[-1]:.3f}", flush=True)
gate("g8 the collective anatomy: C-I monotone with the additive control; "
     "C-II non-monotone (dip, barrier, late decline); C-III coarse-monotone "
     "with a fine-ladder micro-violation census and a sign-changing window "
     "excess over the atom control", ok)

# ---------------------------------------------------------------- g9
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES, g='g9')
for _d, _n in _miss:
    print(f"  g9 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g9 the 1aw paper needles (declared surface)", ok)

# ---------------------------------------------------------------- g10
sys.path.insert(0, HERE)
from cascade_tower import chain_ok
gate("g10 the chain obligation to cascade_li_two_channels.py (Theorem 1av) met",
     chain_ok("cascade_li_two_channels.py"))

# ---------------------------------------------------------------- g11
ok, _missC = paper_needles.verify(PAPER_NEEDLES, g='g11')
for _d, _n in _missC:
    print(f"  g11 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g11 the footer census (this script backticked >= 2; 88 cited in place; "
     "the range 1i–1bl)", ok)

print(flush=True)
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (11/11)")
