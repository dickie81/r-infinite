#!/usr/bin/env python3
"""Theorem 1ba verifier: the crossover -- where pole-carried positivity
ends. Frequency-modulated sections f = g(t) e^{-i tau0 t} of the
reach-delta restricted Weil class (the committed 1az cos basis,
modulated): the Hermitian form ARCH(tau0) + POLE(tau0) - PRIME(tau0)
built from primes + Gamma-data only, its margin swept in the center
frequency tau0 from the certified baseband floors up into the
zero-carried regime. The measured carrier curve: the pole hands off to
an arch--prime draw, the draw hands off to the zeros; the margin curve
reads individual zero gaps; and the session's stated lift-off-at-the-
horizon prediction is REFUTED and replaced by the section-capacity
mechanism.

Gates (all exit-gated; any failure exits 1):
  g1  baseband cross-checks against the committed 1az instrument
      (tau0 = 0, the committed Rmax = 600 / NR = 120001 quadrature):
      margins display-equal to the certified floors 0.034733
      (delta 0.5) and 0.001279 (delta 0.7), and the delta = 4
      boundary value in (-2.6e-7, -2.3e-7) -- the modulated builder
      IS the committed builder at tau0 = 0 (pole 2 Re(u u^T) with u
      real, prime phases exp(i tau0 log n) = 1).
  g2  the explicit-formula identity on minimizers: the zero-free form
      value equals the +-gamma zero-side sum over the first 260
      verified zeros (dps-15 pull) at four spots spanning both delta
      and both regimes -- (1.4, tau0 5) boundary, (1.4, 17) gap-dip,
      (4, 60) just-lifted, (4, 300) zero-carried -- ratios pinned in
      (0.995, 1.0001); the deficit is the positive beyond-260 tail,
      so ratio <= 1 up to float64 wiggle. Margins pinned rel 1e-2:
      4.707e-7, 0.2060, 4.180e-3, 1.1556.
  g3  the handoff (delta = 0.5, no primes; sweep quadrature
      Rwin = 800 / NR = 160001, disclosed -- between the committed 600
      and the converged 3000 of the 1az record): margin monotone
      across the 41-point grid tau0 = 0..40 (every consecutive
      difference positive; 0.034749 at 0, 1.2854 at 40, both rel
      1e-3); the carrier flips pole -> arch: pole share > 0.85 at
      tau0 = 0, arch share crossing sign inside (8, 9) (arch(8) < 0 <
      arch(9); margins there ~0.3, well off boundary, so the balance
      is direction-stable per the round-210 F1 lesson).
  g4  the gap-meter (delta = 1.4): |margin(0)| < 1e-6 and
      0 < margin(5) < 1e-5 (the pole-carried boundary); the
      six-decade lift as gamma_1 = 14.13 enters the footprint
      (margin(13)/margin(5) > 1e5; margin(13) = 0.18384 rel 1e-2);
      the margin then reads the zero gaps: local minima at tau0 = 17
      and 23 -- the (gamma_1, gamma_2) and (gamma_2, gamma_3) gap
      centers -- gated as local minima against both neighbors, pinned
      0.2060 and 0.3545 rel 1e-2, with the dip-filling order
      margin(17) < margin(23).
  g5  the three regimes and the refutation (delta = 4): pole-carried
      boundary (margin(0) in (-2.55e-7, -2.35e-7) on the sweep
      quadrature; -2e-7 < margin(20) < 0); the arch--prime draw at
      tau0 = 40 (|pole| < 1e-3, |margin| < 1e-7,
      margin/arch < 1e-6 -- nine decades of arch-prime cancellation
      with the pole numerically gone); the lift-off bracketed in
      (40, 60) (margin(60) = 4.180e-3 rel 1e-2 > 1e-3), REFUTING the
      session's stated prediction of lift-off at the horizon
      2 pi e^4 = 343.05: the 5-step grid tau0 = 300..400 straddling
      the horizon never dips below 0.5 (gated) -- the fixed-n
      cos-basis section exhausts its own tail-cancellation capacity
      (~n zeros; the tails are 1/r^2 -- the cos modes vanish exactly
      at the support edges and their 1/r sinc leading terms cancel in
      pairs; round-213 F1 corrected the landing's "edge discontinuity
      gives 1/r tails", false on both counts) long before the
      analytic type capacity;
      the horizon remains the smooth-basis n -> infinity envelope,
      untested here. The zero-carried regime: cancellation depth
      margin/arch = 1.873e-3 at 60 and 0.2991 at 300 (windowed);
      the arch share tracks the density identity,
      |arch - log(tau0/2pi)| < 0.05 at tau0 = 300 and 520 (under the
      c^H G c = 1 normalisation, int |fhat|^2 = 2 pi, so
      arch ~ 2 pi mu(tau0) = log(tau0/2pi)); the conservation check
      |arch + pole + prime - margin| < 1e-8 at the five spots of the
      depth/draw/density loop (tau0 = 0, 40, 60, 300, 520; round-213
      F5 corrected the landing's "at every gated spot", which
      overreached the committed loop).
  g6  the paper needles for the 1ba block (in-code list
      authoritative).
  g7  the chain obligation to cascade_weil_margin.py (Theorem 1az) met.
  g8  the footer census (this script backticked >= 2; the anchored needles "the **79 scripts cited in place** above"
      and "extended by Theorems 1i–1bc:" -- round-218 F12 mirrored
      the tower-wide anchoring into this line).

Balance-decomposition caution (round-210 F1 / round-211 F5 standing):
balances at near-boundary margins are direction-sensitive and
instrument-dependent; every balance gate above is either at a lifted
margin (direction-stable) or a coarse magnitude/sign bound.

Sabotage record (parallel-isolation design: baseline + four probes as
five INDEPENDENT tar trees from committed HEAD, run concurrently and
discarded after -- no restore step exists; each mangle's application
verified by assert + cmp against the committed copy before launch;
the first attempt was killed mid-chain by a container restart after
all five trees had recorded g1-g6, and the record below is the full
uninterrupted relaunch; censuses are the OBSERVED results):
  (a) title needle mangled in-span single-site in the paper
      -> OBSERVED: g6 FAIL alone (exit 1)
  (b) the gap-dip pin 0.2060 mangled a decade in code (-> 2.060)
      -> OBSERVED: g4 FAIL alone (exit 1)
  (c) the draw bound margin/arch < 1e-6 tightened past truth in code
      (-> < 1e-12) -> OBSERVED: g5 FAIL alone (exit 1)
  (d) footer census reverted 77 -> 76 in the paper -> OBSERVED: g8
      FAIL AND g7 FAIL (census propagation through the chained 1az
      verifier's own footer gate)
"""
import sys, subprocess, os, math
import numpy as np
from scipy.special import psi as scipy_digamma
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

NBASE = 24

def gvec_real(a, r):
    ks = np.arange(NBASE)
    w = (ks[:, None] + 0.5)*np.pi/a
    rr = np.atleast_1d(r)[None, :]
    def s(x):
        return np.sinc(x/np.pi)
    return a*(s((rr - w)*a) + s((rr + w)*a))

def gvec_complex(a, z):
    ks = np.arange(NBASE)
    w = (ks + 0.5)*np.pi/a
    def s(x):
        out = np.ones_like(x, dtype=complex)
        nz = np.abs(x) > 1e-12
        out[nz] = np.sin(x[nz])/x[nz]
        return out
    return a*(s((z - w)*a) + s((z + w)*a))

def vonmangoldt(nmax):
    lam = np.zeros(nmax + 1)
    for p in range(2, nmax + 1):
        if all(p % q for q in range(2, int(p**0.5) + 1)):
            pk = p
            while pk <= nmax:
                lam[pk] = np.log(p)
                pk *= p
    return lam

def build_form(delta, tau0, Rwin=800.0, NR=160001):
    a = delta/2.0
    r = np.linspace(tau0 - Rwin, tau0 + Rwin, NR)
    F = gvec_real(a, r - tau0)
    ker = np.real(scipy_digamma(0.25 + 0.5j*r)) - np.log(np.pi)
    dr = r[1] - r[0]
    ARCH = ((F*ker[None, :]) @ F.T * dr/(2*np.pi)).astype(complex)
    u = gvec_complex(a, np.full(NBASE, -tau0) + 0.5j)
    POLE = np.outer(u, u); POLE = POLE + np.conj(POLE)
    nmax = int(np.floor(np.exp(delta))) + 1
    lam = vonmangoldt(nmax)
    ns = np.nonzero(lam)[0]
    tg = np.linspace(-a, a, 4001)
    dt = tg[1] - tg[0]
    ks = np.arange(NBASE)
    PRIME = np.zeros((NBASE, NBASE), dtype=complex)
    for n_ in ns:
        uu = np.log(n_)
        if uu >= delta:
            continue
        mask = (tg + uu <= a) & (tg + uu >= -a)
        t1 = tg[mask]
        B1 = np.cos((ks[:, None] + 0.5)*np.pi*t1[None, :]/a)
        B2 = np.cos((ks[:, None] + 0.5)*np.pi*(t1[None, :] + uu)/a)
        A = B1 @ B2.T * dt
        ph = np.exp(1j*tau0*uu)
        PRIME += -lam[n_]/np.sqrt(n_)*(ph*A + np.conj(ph)*A.T)
    Q = ARCH + POLE + PRIME
    Q = (Q + Q.conj().T)/2
    return Q, ARCH, POLE, PRIME, a

def margin_at(delta, tau0, **kw):
    Q, ARCH, POLE, PRIME, a = build_form(delta, tau0, **kw)
    G = np.eye(NBASE)*a
    ev, V = scipy_eigh(Q, G)
    c = V[:, 0]
    bal = (float(np.real(c.conj() @ ARCH @ c)),
           float(np.real(c.conj() @ POLE @ c)),
           float(np.real(c.conj() @ PRIME @ c)))
    return ev[0], bal, c

# ---------------------------------------------------------------- g1
l05 = margin_at(0.5, 0.0, Rwin=600.0, NR=120001)[0]
l07 = margin_at(0.7, 0.0, Rwin=600.0, NR=120001)[0]
l40b = margin_at(4.0, 0.0, Rwin=600.0, NR=120001)[0]
ok = abs(l05 - 0.034733) < 1e-4
ok &= abs(l07 - 0.001279) < 1e-5
ok &= -2.6e-7 < l40b < -2.3e-7
print(f"  g1 baseband cross-checks: {l05:.6f} / {l07:.6f} / {l40b:.4e}", flush=True)
gate("g1 baseband cross-checks: the modulated builder reproduces the "
     "committed 1az floors and the delta-4 boundary at tau0 = 0", ok)

# ---------------------------------------------------------------- g2
mp.dps = 15
NZ = 260
print("  g2 pulling zeros...", flush=True)
Z = [float(zetazero(k).imag) for k in range(1, NZ + 1)]
spots = ((1.4, 5.0, 4.707e-7), (1.4, 17.0, 0.2060),
         (4.0, 60.0, 4.180e-3), (4.0, 300.0, 1.1556))
ok = True
spot_cache = {}
for delta, tau0, pin in spots:
    lm, bal, c = margin_at(delta, tau0)
    spot_cache[(delta, tau0)] = (lm, bal, c)
    a = delta/2.0
    zside = 0.0
    for g in Z:
        for gg in (g, -g):
            v = gvec_real(a, np.array([gg - tau0]))[:, 0]
            zside += abs(np.dot(np.conj(c), v))**2
    nrm = float(np.real(np.conj(c) @ (np.eye(NBASE)*a) @ c))
    ratio = zside/nrm/lm
    ok &= abs(lm/pin - 1) < 1e-2
    ok &= 0.995 < ratio < 1.0001
    print(f"  g2 ({delta}, {tau0}): form {lm:.4e}; zero-side ratio {ratio:.4f}",
          flush=True)
gate("g2 the explicit-formula identity: the zero-free form equals the "
     "+-gamma zero side on minimizers at four spots (both delta, both "
     "regimes)", ok)

# ---------------------------------------------------------------- g3
marg05 = []
bal05 = []
for tau0 in range(0, 41):
    lm, bal, _ = margin_at(0.5, float(tau0))
    marg05.append(lm); bal05.append(bal)
ok = abs(marg05[0]/0.034749 - 1) < 1e-3
ok &= abs(marg05[40]/1.2854 - 1) < 1e-3
ok &= all(marg05[i+1] > marg05[i] for i in range(40))
ok &= bal05[0][1] > 0.85
ok &= bal05[8][0] < 0 < bal05[9][0]
print(f"  g3 handoff: margin {marg05[0]:.6f} -> {marg05[40]:.6f} monotone; "
      f"pole share at 0: {bal05[0][1]:.4f}; arch sign flip "
      f"{bal05[8][0]:.4f} -> {bal05[9][0]:.4f} in (8, 9)", flush=True)
gate("g3 the handoff at delta = 0.5: monotone margin, pole -> arch "
     "carrier flip inside (8, 9)", ok)

# ---------------------------------------------------------------- g4
m14 = {}
for tau0 in (0.0, 5.0, 13.0, 16.0, 17.0, 18.0, 22.0, 23.0, 24.0):
    m14[tau0] = margin_at(1.4, tau0)[0]
ok = abs(m14[0.0]) < 1e-6
ok &= 0 < m14[5.0] < 1e-5
ok &= m14[13.0]/m14[5.0] > 1e5
ok &= abs(m14[13.0]/0.18384 - 1) < 1e-2
ok &= m14[17.0] < m14[16.0] and m14[17.0] < m14[18.0]
ok &= m14[23.0] < m14[22.0] and m14[23.0] < m14[24.0]
ok &= abs(m14[17.0]/0.2060 - 1) < 1e-2
ok &= abs(m14[23.0]/0.3545 - 1) < 1e-2
ok &= m14[17.0] < m14[23.0]
print(f"  g4 gap-meter: boundary {m14[5.0]:.3e}; lift ratio "
      f"{m14[13.0]/m14[5.0]:.3e}; gap dips {m14[17.0]:.4f} (tau0 17), "
      f"{m14[23.0]:.4f} (tau0 23), both local minima, filling in", flush=True)
gate("g4 the gap-meter at delta = 1.4: pole-carried boundary, the "
     "six-decade lift at gamma_1, the gap-center local minima", ok)

# ---------------------------------------------------------------- g5
m40 = {}
for tau0 in [0.0, 20.0, 40.0, 60.0, 520.0] + list(np.arange(300.0, 401.0, 5.0)):
    m40[tau0] = spot_cache.get((4.0, tau0)) or margin_at(4.0, tau0)
ok = -2.55e-7 < m40[0.0][0] < -2.35e-7
ok &= -2e-7 < m40[20.0][0] < 0
lm40, bal40, _ = m40[40.0]
ok &= abs(bal40[1]) < 1e-3
ok &= abs(lm40) < 1e-7
ok &= abs(lm40)/bal40[0] < 1e-6
ok &= abs(m40[60.0][0]/4.180e-3 - 1) < 1e-2 and m40[60.0][0] > 1e-3
hzmin = min(m40[t][0] for t in np.arange(300.0, 401.0, 5.0))
ok &= hzmin > 0.5
d60 = m40[60.0][0]/m40[60.0][1][0]
d300 = m40[300.0][0]/m40[300.0][1][0]
ok &= 1.6e-3 < d60 < 2.2e-3
ok &= 0.25 < d300 < 0.35
ok &= abs(m40[300.0][1][0] - math.log(300.0/(2*math.pi))) < 0.05
ok &= abs(m40[520.0][1][0] - math.log(520.0/(2*math.pi))) < 0.05
for t in (0.0, 40.0, 60.0, 300.0, 520.0):
    lm, bal, _ = m40[t]
    ok &= abs(bal[0] + bal[1] + bal[2] - lm) < 1e-8
print(f"  g5 three regimes: boundary {m40[0.0][0]:.4e} / {m40[20.0][0]:.4e}; "
      f"draw at 40: margin {lm40:.3e}, pole {bal40[1]:.5f}, depth "
      f"{abs(lm40)/bal40[0]:.2e}; lift-off in (40, 60): {m40[60.0][0]:.4e}; "
      f"horizon-straddle min {hzmin:.4f} (NO feature at 343.05); depths "
      f"{d60:.4e} -> {d300:.4f}; arch vs log(tau0/2pi): "
      f"{m40[300.0][1][0]:.4f}/{math.log(300.0/(2*math.pi)):.4f}, "
      f"{m40[520.0][1][0]:.4f}/{math.log(520.0/(2*math.pi)):.4f}", flush=True)
gate("g5 the three regimes at delta = 4: pole-carried boundary, the "
     "arch--prime draw, the (40, 60) lift-off refuting the naive "
     "horizon, the density identity", ok)

# ---------------------------------------------------------------- g6
needles = [
    "**Theorem 1ba (the crossover:",
    "positivity changes hands twice",
    "the arch–prime draw",
    "Montgomery's diagonal draw at section level",
    "the margin curve reads the zero gaps",
    "six-decade lift",
    "lift-off sits in (40, 60)",
    "the smooth-basis n → ∞ envelope",
    "ratio 0.9996–0.9999",
    "the first continuous object connecting",
    "dodger death at the horizon",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g6 MISSING: {nd!r}", flush=True)
gate("g6 the 1ba paper needles", ok)

# ---------------------------------------------------------------- g7
sys.path.insert(0, HERE)
from cascade_tower import chain_ok
gate("g7 the chain obligation to cascade_weil_margin.py (Theorem 1az) met",
     chain_ok("cascade_weil_margin.py"))

# ---------------------------------------------------------------- g8
ok = paper.count("`cascade_weil_crossover.py`") >= 2
ok &= "the **79 scripts cited in place** above" in paper
ok &= "extended by Theorems 1i–1bc:" in paper
gate("g8 the footer census (this script backticked >= 2; 79 cited in "
     "place; the range 1i–1bc)", ok)

print(("\nALL GATES PASS (8/8)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
