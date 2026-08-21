#!/usr/bin/env python3
"""Theorem 1au verifier: the push record -- the open-region census, the
first-stage floor's data, the Turan rate law, and the thinnest Li
direction. (The docstring title had carried the refuted monotone
draft's name -- the fourth carrier of the round-194 F2 class, caught
round 195 F2 and corrected here.)

Gates (all exit-gated; any failure exits 1):
  g1  the moment instrument: 2*int Phi over [0,8] equals xi(1/2)/2 to
      1e-10 (the ratio-1/2 pin -- the LIVE calibration); the gamma(0)
      pin is a digit-string check only (gamma(0) = xi(1/2) holds by
      construction, round-194 F7); the real instrument evidence is the
      gamma(1) cross-check against an independent derivative route
      (relative deviation < 1e-20). Coefficients through j = 56.
  g2  the open-region census (beyond GORZ's proven d <= 8): for
      d in {9, 12, 16, 20, 25} and every reachable n (n <= 56 - d),
      every Jensen stage is hyperbolic with relative imaginary root
      part < 1e-40 (observed: exactly zero).
  g3  the first-stage floor (the declared conjecture's data, with the
      refutation the gate itself delivered): the full-step monotonicity
      census finds EXACTLY ONE violation -- the micro-dip at
      (d = 12, n = 3 -> 4), depth in (2e-6, 6e-6) -- which refuted the
      lead's monotone draft on the first clean run, pre-commit; the
      floor min(seq) >= seq[0] holds for every d (the first stage is
      the worst stage); endpoints pinned (d=9: 0.1067 -> 0.1100; d=16:
      0.0520 -> 0.0556; d=25: 0.0290 -> 0.0329; each +- 0.002); every
      margin BELOW its Hermite benchmark (H_9 0.1134, H_16 0.0583,
      H_25 0.0357, each +- 0.002); the n = 0 Hermite ratios pinned and
      DECLINING (0.9414/0.9244/0.8914/0.8559/0.8119 at d =
      9/12/16/20/25) with the global tested floor 0.8119 +- 0.003.
  g4  the Turan rate law r_j ~ 1/(2j): r_j > 0 for j <= 55; the products
      j*r_j pinned at j=10: 0.2932 and j=55: 0.4687 (each +- 0.005) and
      increasing across the sampled ladder.
  g5  the Li margins (rebuilt round 194 F1; the lower-bound framing
      struck round 195 F1 and its docstring/label carriers swept round
      196 F1): the 200-pair partial sums are POSITIVE, with termwise
      nonnegativity gated at n = 40 (every paired term checked >= 0)
      and per-n positivity gated for every n <= 40; the n = 40 partial
      sum 27.1808 +- 0.02 labeled as a partial sum; the TRUE zeros-free
      ladder via Cauchy extraction of log xi(1/(1-z)): lambda_1 to
      1e-8, lambda_40 = 30.4774 +- 0.002, lambda_50 = 43.5311 +- 0.002
      (the committed gated-ladder anchor); the truncation deficit
      lambda_40 - partial(40) in (3.25, 3.35), the paired-tail scale;
      argmin of partial(n)/n at n = 1.
  g6  the thinnest direction's closed form: |(1 + gamma/2 - log(4 pi)/2)
      - 0.0230957090| < 1e-9, and the bracket: zeros-side lambda_1 <
      closed form < zeros-side + 2x the stated tail bound. (The former
      fixed-inequality conjunct was removed round 194 F8 as a gate that
      could not fail.)
  g7  the paper needles for the 1au block (title; the no-proof frame;
      the FIRST-STAGE FLOOR; the n = 0 reduction; the rate law; the
      archimedean inequality; the closed-form digits; beyond-GORZ;
      plus the round-194 repair needles including a unique-context
      anchor for the 1au closed-form sentence -- the in-code list is
      the authoritative census; the original docstring's "MONOTONE
      ATTRACTION" entry named a needle that never existed, round-194
      F2's docstring carrier).
  g8  the chain obligation to cascade_finite_fill.py (Theorem 1at) met.
  g9  the footer census (this script backticked >= 2; the anchored needles "the **84 scripts cited in place** above"
      and "extended by Theorems 1i–1bh:" -- round-218 F12 mirrored
      the tower-wide anchoring into this line).

Sabotage record (each: fresh tree, single mangle, restore from pristine;
clean baselines around the suite; censuses are the OBSERVED results):
  (a) title needle mangled in the paper       -> g7 FAIL alone
  (b) the global-floor pin mangled in code (0.8119 -> 0.8319)
                                              -> g3 FAIL alone (the
      floor census is load-bearing)
  (c) closed-form digits mangled in the paper (0.0230957 -> 0.0230857,
      a GLOBAL replacement hitting all three occurrences, both others
      in one earlier block, Theorem 1ao ("blocks" corrected round 195
      F4) -- disclosed round 194 F5; the probe
      demonstrated paper-vs-computation independence, not single-site
      corruption detection) -> g7 FAIL while g6 (recomputed closed
      form) STANDS
  (c') the round-194 repair: single-site mangle of the 1au block's own
      closed-form sentence (unique-context needle "0.0230957… (gated
      to nine digits") -> g7 FAIL alone -- single-site corruption of
      the 1au value is now detected (observed in the round-194 sweep's
      probe run)
  (d) footer census reverted 71 -> 70         -> g9 FAIL AND g8 FAIL
      (census propagation through the chain: the chained 1at verifier's
      own footer gate catches the same reversion)
  (e) chain target renamed in code            -> g8 FAIL alone
"""
import sys, math, subprocess, os
import numpy as np
from mpmath import (mp, mpf, mpc, exp, pi, quad, gamma as G, zeta, polyroots,
                    factorial, binomial, zetazero, log, euler)

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        fails.append(label)

# ---------------------------------------------------------------- g1
mp.dps = 80
def Phi(u):
    s = mpf(0)
    for n in range(1, 26):
        s += (2*pi**2*n**4*exp(mpf(9)*u/2) - 3*pi*n*n*exp(mpf(5)*u/2))*exp(-pi*n*n*exp(2*u))
    return s
xi_half = mpf("0.25")*(-1)*pi**mpf("-0.25")*G(mpf("0.25"))*zeta(mpf("0.5"))/2
m0 = 2*quad(Phi, [0, 8])
ratio = m0/xi_half
JMAX = 56
gam = []
for j in range(JMAX + 1):
    m2j = 2*quad(lambda u: Phi(u)*u**(2*j), [0, 8])
    gam.append(factorial(j)*(m2j/factorial(2*j))*(xi_half/m0))
ok = abs(ratio - mpf("0.5")) < mpf(10)**-10
ok &= abs(gam[0] - mpf("0.497120778188")) < mpf(10)**-9   # digit-string check only:
# gam[0] = xi_half BY CONSTRUCTION (round-194 F7) -- the live calibration is the
# ratio pin above plus this independent-derivative cross-check on gamma(1):
from mpmath import diff as mpdiff
d2 = mpdiff(lambda s: s*(s-1)/2 * pi**(-s/2) * G(s/2) * zeta(s), mpf("0.5"), 2)
ok &= abs(gam[1] - d2/2)/abs(gam[1]) < mpf(10)**-20
print(f"  g1 ratio = {float(ratio):.12f}; gamma(0) = {float(gam[0]):.12f}; "
      f"gamma(1) cross-check rel dev {float(abs(gam[1]-d2/2)/abs(gam[1])):.1e}")
gate("g1 the moment instrument: ratio-1/2 pin (live), gamma(0) digit check "
     "(by-construction), gamma(1) independent-derivative cross-check", ok)

# ---------------------------------------------------------------- g2, g3
def jensen(d, n):
    return [binomial(d, j)*gam[n + j] for j in range(d + 1)]
def stage_roots(d, n):
    c = jensen(d, n)
    return polyroots([c[d - k] for k in range(d + 1)], maxsteps=200, extraprec=120)
worst_im = mpf(0)
gapseq = {}
for d in (9, 12, 16, 20, 25):
    seq = []
    for n in range(0, JMAX - d + 1):
        rts = stage_roots(d, n)
        worst_im = max(worst_im, max(abs(r.imag) for r in rts)/max(abs(r) for r in rts))
        re = sorted([r.real for r in rts])
        seq.append(min(re[i+1] - re[i] for i in range(len(re) - 1))/(re[-1] - re[0]))
    gapseq[d] = seq
print(f"  g2 worst relative imaginary part: {float(worst_im):.2e}")
gate("g2 open-region census: every stage d in {9,12,16,20,25}, all reachable n, "
     "hyperbolic", worst_im < mpf(10)**-40)

def hermite_gap(d):
    hprev = np.zeros(d + 1); hprev[0] = 1.0
    hcur = np.zeros(d + 1); hcur[1] = 2.0
    for k in range(1, d):
        nxt = np.zeros(d + 1)
        nxt[1:] += 2*hcur[:-1]
        nxt -= 2*k*hprev
        hprev, hcur = hcur, nxt
    r = np.sort(np.roots(hcur[::-1]).real)
    return float(min(np.diff(r))/(r[-1] - r[0]))
ok = True
violations = []
for d in (9, 12, 16, 20, 25):
    seq = gapseq[d]
    for i in range(len(seq) - 1):
        if seq[i+1] < seq[i] - mpf(10)**-12:
            violations.append((d, i, float(seq[i] - seq[i+1])))
    # the first-stage floor: the n = 0 stage is the worst stage
    ok &= min(seq) >= seq[0] - mpf(10)**-12
# the exception census: exactly ONE micro-dip, located, depth pinned
ok &= len(violations) == 1
ok &= violations[0][0] == 12 and violations[0][1] == 3
ok &= 2e-6 < violations[0][2] < 6e-6
hb = {9: 0.1134, 16: 0.0583, 25: 0.0357}
pins = {9: (0.1067, 0.1100), 16: (0.0520, 0.0556), 25: (0.0290, 0.0329)}
for d, (p0, p1) in pins.items():
    seq = gapseq[d]
    ok &= abs(float(seq[0]) - p0) < 0.002 and abs(float(seq[-1]) - p1) < 0.002
    hg = hermite_gap(d)
    ok &= abs(hg - hb[d]) < 0.002
    ok &= all(float(x) < hg for x in seq)
# the d-trend of the n = 0 ratio, pinned, declining; the global floor
n0r = {d: float(gapseq[d][0])/hermite_gap(d) for d in (9, 12, 16, 20, 25)}
n0pins = {9: 0.9414, 12: 0.9244, 16: 0.8914, 20: 0.8559, 25: 0.8119}
for d in n0pins:
    ok &= abs(n0r[d] - n0pins[d]) < 0.003
ok &= n0r[9] > n0r[12] > n0r[16] > n0r[20] > n0r[25]
ok &= abs(min(min(float(x)/hermite_gap(d) for x in gapseq[d])
              for d in (9, 12, 16, 20, 25)) - 0.8119) < 0.003
print(f"  g3 violations: {violations}; endpoints d=9 "
      f"{float(gapseq[9][0]):.4f}->{float(gapseq[9][-1]):.4f} (H {hermite_gap(9):.4f}); "
      f"d=25 {float(gapseq[25][0]):.4f}->{float(gapseq[25][-1]):.4f} (H {hermite_gap(25):.4f}); "
      f"n0 ratios {[round(n0r[d],4) for d in (9,12,16,20,25)]}")
gate("g3 the first-stage floor: exactly one located micro-dip; min at n = 0 "
     "for every d; pinned endpoints; below-Hermite; declining n0 ratios with "
     "global floor 0.8119", ok)

# ---------------------------------------------------------------- g4
sample = (1, 2, 5, 10, 20, 30, 40, 50, 55)
jr = {}
ok = True
for j in range(1, 56):
    r = gam[j]**2/(gam[j-1]*gam[j+1]) - 1
    ok &= r > 0
    if j in sample:
        jr[j] = float(j*r)
ok &= abs(jr[10] - 0.2932) < 0.005 and abs(jr[55] - 0.4687) < 0.005
ok &= all(jr[sample[i+1]] > jr[sample[i]] for i in range(len(sample) - 1))
print(f"  g4 j*r_j: j=10 {jr[10]:.4f}, j=55 {jr[55]:.4f}")
gate("g4 the Turan rate law: r_j > 0 through j = 55; j*r_j pinned and increasing", ok)

# ---------------------------------------------------------------- g5
mp.dps = 30
zs = [zetazero(k) for k in range(1, 201)]
def li_terms(n):
    return [2*(1 - ((z - 1)/z)**n).real for z in zs]
lam = {n: sum(li_terms(n)) for n in range(1, 41)}
# termwise nonnegativity at n = 40: the on-line paired terms are
# 2(1 - cos) >= 0, so the PARTIAL SUMS are positive. (The former
# "so the partial sums are LOWER BOUNDS" comment reproduced the
# inference struck round 195 F1 -- tail nonnegativity is RH-strength;
# carrier caught round 196 F1.)
ok = all(t >= -mpf(10)**-25 for t in li_terms(40))
ok &= all(lam[n] > 0 for n in lam)
ok &= abs(float(lam[40]) - 27.1808) < 0.02      # the PARTIAL SUM, labeled as such
argmin = min(range(1, 41), key=lambda n: float(lam[n])/n)
ok &= argmin == 1
# the TRUE ladder, zeros-free: lambda_n = n*[z^n] log xi(1/(1-z))
mp.dps = 60
def xi60(s):
    from mpmath import gamma as G60, zeta as z60
    return s*(s-1)/2 * pi**(-s/2) * G60(s/2) * z60(s)
M5, r5 = 512, mpf("0.5")
lv = [log(xi60(1/(1 - r5*exp(mpc(0, 2*pi*m/M5))))) for m in range(M5)]
def lam_free(n):
    c = sum(lv[m]*exp(mpc(0, -2*pi*n*m/M5)) for m in range(M5))/(M5*r5**n)
    return float(n*c.real)
lf1, lf40, lf50 = lam_free(1), lam_free(40), lam_free(50)
ok &= abs(lf1 - 0.023095709) < 1e-8
ok &= abs(lf40 - 30.4774) < 0.002
ok &= abs(lf50 - 43.5311) < 0.002                # the committed gated-ladder anchor
ok &= 3.25 < lf40 - float(lam[40]) < 3.35        # the deficit at the paired-tail scale
print(f"  g5 partial(40) = {float(lam[40]):.4f}; TRUE lambda_40 = {lf40:.4f}; "
      f"lambda_50 = {lf50:.4f}; deficit {lf40 - float(lam[40]):.4f}; argmin = {argmin}")
gate("g5 Li margins: partial sums positive (termwise-gated at n = 40; the "
     "lower-bound framing struck round 195 F1, label swept round 196 F1); "
     "the TRUE zeros-free ladder (lambda_40 = 30.4774, anchored at the "
     "committed lambda_50); the deficit at the paired-tail scale", ok)

# ---------------------------------------------------------------- g6
closed = 1 + euler/2 - log(4*pi)/2
gam_last = float(zs[-1].imag)
tailb = 2*float(1*2*0.5*((log(gam_last/(2*pi)) + 1)/(2*pi*gam_last))*2)
ok = abs(closed - mpf("0.0230957090")) < mpf(10)**-9
# (the former "(2 + euler) > log(4 pi)" conjunct was removed round 194 F8 --
# a fixed true inequality between constants, a gate that could not fail)
ok &= float(lam[1]) < float(closed) < float(lam[1]) + tailb
print(f"  g6 closed form {float(closed):.10f}; bracket ({float(lam[1]):.4f}, {float(lam[1]) + tailb:.4f})")
gate("g6 the thinnest direction: lambda_1 = 1 + gamma/2 - log(4pi)/2 and "
     "the zeros-side bracket (the inequality conjunct removed round 194 F8; "
     "label re-synced rounds 195 F3, 213 F3)", ok)

# ---------------------------------------------------------------- g7
needles = [
    "**Theorem 1au (the push record: two fronts advanced past their",
    "**no proof is\nclaimed, and none resulted**",
    "the FIRST-STAGE FLOOR",
    "refuted the\nlead's monotone draft pre-commit",
    "(d = 12, n = 3 → 4) of depth 4.0×10⁻⁶",
    "margin(d, n) ≥ margin(d, 0)",
    "global tested floor 0.8119",
    "all-n hyperbolicity reduces to the n = 0 line",
    # round-194 repair needles
    "the 198 tested steps",
    "the 200-pair partial sums are\nPOSITIVE unconditionally",
    "struck round 195 F1, MAJOR",
    "unconditional and zeros-free: this paper's committed",
    "λ₄₀ = 30.4774, anchored at the",
    "an\nabsolute margin of 0.0462 — 1.8% of log 4π",
    "parts below 10⁻⁴⁰ (gated",
    "the FIRST-STAGE-FLOOR conjecture is DECLARED,",
    "0.0230957… (gated to nine digits",
    "r_j ≈ 1/(2j)",
    "2 + γ > log 4π",
    "0.0230957",
    "far beyond GORZ's proven",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g7 MISSING: {nd!r}")
gate("g7 the 1au paper needles", ok)

# ---------------------------------------------------------------- g8
sys.path.insert(0, HERE)
from cascade_tower import chain_ok
gate("g8 the chain obligation to cascade_finite_fill.py (Theorem 1at) met",
     chain_ok("cascade_finite_fill.py"))

# ---------------------------------------------------------------- g9
ok = paper.count("`cascade_attraction_margins.py`") >= 2
ok &= "the **84 scripts cited in place** above" in paper
ok &= "extended by Theorems 1i–1bh:" in paper
gate("g9 the footer census (this script backticked >= 2; 84 cited in place; "
     "the range 1i–1bh)", ok)

print()
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (9/9)")
