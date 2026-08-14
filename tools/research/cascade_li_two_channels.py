#!/usr/bin/env python3
"""Theorem 1av verifier: the two channels of the Li ladder -- the two-regime
anatomy, the thousand-direction census, the phase-coincidence mechanism,
the pole-side inversion, the dichotomy, and the informational-pressure
program's gated anchors.

Gates (all exit-gated; any failure exits 1):
  g1  the two-regime anatomy (Stieltjes/polygamma route, N = 50):
      lambda_B(1) = -0.5541 +- 0.0005 while lambda_A(1) = euler EXACTLY
      (to 1e-20) -- the first direction carried by the primes channel;
      lambda_B first positive at n = 8; first dominance (B > |A|) at
      n = 11; lambda_A > 0 for all n <= 50; the n = 24 local minimum
      present; lambda_A(50) = 1.4979 +- 0.002 (the g3 cross-check
      anchor).
  g2  the junction constant: euler == -psi(1) == stieltjes(0), both to
      1e-25 -- the one number the two channels share. (Round-198 F8
      note: this is an identity/library-consistency check -- the
      identity is classical and the conjunct cannot fail short of
      mpmath breakage; retained because the paper's "gated to 25
      digits" names it, with its nature stated here.)
  g3  the thousand-direction census (branch-safe dual Cauchy extraction,
      M = 2048, r = 0.95, dps 60; the contour's image has |Im s| <= 9.744
      (r/(1-r^2) = 9.74359..., bound rounded UP per round 199 finding 3)
      < gamma_1, so no zero location enters): branch continuity max
      steps < pi on BOTH logs; cross-checks lambda_1 to 1e-8,
      lambda_40 = 30.4774 +- 0.002, lambda_50 = 43.5311 +- 0.002,
      lambda_B(1) matching g1 to 1e-3, lambda_A(50) matching g1 to
      1e-3, lambda_B(89) = 99.8944 +- 0.005; FIRST NEGATIVE lambda_A at
      n = 156; negative-run starts exactly [156, 247, 353, 424, 516,
      603, 759, 919]; 336 negatives total; the first trough min over
      [80, 95] in (0.20, 0.22), its location gated == 88 and value
      0.208 +- 0.0015, the second trough gated == 172 in (-1.04, -1.01)
      (the trough conjuncts added round 198 F4); min lambda_n over
      [1, 1000] attained at n = 1 within 1e-3 of the pinned 0.0231 (the
      lambda_1 value itself is separately cross-checked at 1e-8; the
      original "within 1e-6" description overstated this conjunct's own
      tolerance, a round-198 cosmetic — the "F6" pointer here named a
      different canonical finding, re-synced round 200); max |lambda_A|/lambda_B over
      [11, 1000] = 0.8325 +- 0.003 attained at n = 11; lambda_B(1000)
      = 2324.30 +- 0.05 vs the RH trend 2323.54 +- 0.05.
  g4  the phase-coincidence mechanism (theta_k = pi - 2 atan(2 gamma_k),
      W_k(n) = 2(1 - cos(n theta_k)); classical zeros enter here as the
      mechanism's clock, labeled): at n = 132, W_2 < 0.01 while
      W_1 > 3.98 and lambda_A(132) > 2.2 (single-withholder
      insufficiency); at n = 156, W_1, W_3, W_4, W_5 ALL < 2
      (collective withholding), W_3(156) < 0.01, and 2 pi gamma_3 in
      (157.0, 157.3) with |156 - 2 pi gamma_3| < 1.3; at n = 178,
      W_1 < 0.01 while W_2 > 3.1 (zero 1's second trough exact).
  g5  the pole-side inversion: ESPRIT (Hankel SVD, K2 = 16) on the
      detrended g3 lambda_A recovers the line nearest gamma_1 with
      error < 5e-6 and pole modulus within 5e-7 of 1 (display-equal
      bounds per round 199 finding 1; this docstring had retained the
      pre-repair 1e-4/1e-5 figures and their struck characterization —
      synced round 200), and the line
      nearest gamma_2 with error < 0.05 and modulus within 5e-4 of 1 --
      position AND line-adherence from pole-side data alone.
  g6  the dichotomy rates: at beta = 1/2 the multiplier modulus is 1 to
      1e-25 (termwise [0, 4] on the line); off-line the envelope rate
      |log|w|| matches (2 beta - 1)/(2 gamma^2) within 3% at three
      (beta, gamma) examples -- no intermediate regime.
  g7  the entropy anchors: joint entropy h + h_hat for e^(-pi x^2)
      = 1 - ln 2 within 2e-3; the exponential exceeds it by > 0.07; the
      stretched Gaussian ties within 2e-3 (scale invariance); the
      self-dual member's single-side h = (1 - ln 2)/2 within 2e-3
      (the equal split).
  g8  the paper needles for the 1av block (title; the no-proof frame;
      the regime-I carrier sentence; the junction constant; the 156
      census; the seam maximum; the n = 1 scarcity; the recovered
      gamma_1 digits; the dichotomy sentence; the declared-program
      fence; the Lambda = 0 exhibit; the entropy constant; the unbuilt
      coupling; plus the six round-198 repair needles -- the in-code
      list is the authoritative census, enumeration extended round 199
      finding 5).
  g9  the chain: cascade_attraction_margins.py (Theorem 1au) exits 0.
  g10 the footer census (this script backticked >= 2; "78 scripts cited in place"; "Theorems 1i-1bb").

Sabotage record (each: fresh tree, single mangle, restore from pristine;
clean baselines around the suite; censuses are the OBSERVED results):
  (a) title needle "mangled" by APPENDING a character after the needle's
      end ("two-regime" -> "two-regimes") -> NO DETECTION (exit 0,
      10/10): the needle is suffix-open and substring matching still
      succeeds -- a probe-design defect of the quote-satisfiability
      class (round-184 lineage), disclosed as observed; the probe
      demonstrated nothing about the gate
  (a') the corrected probe: in-span mangle ("two channels" -> "two
      channel") -> g8 FAIL alone -- title corruption inside the needle
      span is detected
  (b) the census pin 156 -> 155 in code       -> g3 FAIL alone (the
      first-negative census is load-bearing)
  (c) the recovered-gamma_1 digits mangled in the paper (run against
      the PRE-round-198 needle "14.1348 against"; both round-198
      reviewers reproduced it, one in a fresh tree)
                                              -> g8 FAIL (value needle)
      while g5 (the live inversion) STANDS -- paper-vs-computation
      independence. Round-198 note: the sweep corrected the paper's
      digits to the committed instrument's 14.1347 and repointed the
      needle accordingly; the probe's mechanism (in-span digit mangle
      -> g8-alone) is unchanged by the repointing
  (d) footer census reverted 72 -> 71         -> g10 FAIL AND g9 FAIL
      (census propagation through the chained 1au verifier's own
      footer gate)
  (e) chain target renamed in code            -> g9 FAIL alone
"""
import sys, math, subprocess, os
import numpy as np
from mpmath import (mp, mpf, mpc, exp, pi, log, loggamma, zeta, euler,
                    stieltjes, factorial, polygamma, binomial, digamma,
                    zetazero, atan)

HERE = os.path.dirname(os.path.abspath(__file__))
PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label)
    if not ok:
        fails.append(label)

# ---------------------------------------------------------------- g1
mp.dps = 40
N1 = 50
c = [mpf(1)] + [(-1)**(k-1)*stieltjes(k-1)/factorial(k-1) for k in range(1, N1+1)]
lnA = [mpf(0)]*(N1+1)
for n in range(1, N1+1):
    t = c[n]
    for k in range(1, n):
        t -= mpf(k)/n*lnA[k]*c[n-k]
    lnA[n] = t
lnB = [log(mpf(1)/2)] + [mpf(0)]*N1
for k in range(1, N1+1):
    t = mpf(-1)**(k+1)/k
    if k == 1:
        t -= log(pi)/2
    t += polygamma(k-1, mpf(1)/2)/(2**k*factorial(k))
    lnB[k] = t
def compose(a, N):
    out = [a[0]] + [mpf(0)]*N
    for j in range(1, N+1):
        out[j] = sum(a[k]*binomial(j-1, k-1) for k in range(1, j+1))
    return out
CB, CA = compose(lnB, N1), compose(lnA, N1)
lB1 = [n*CB[n] for n in range(1, N1+1)]
lA1 = [n*CA[n] for n in range(1, N1+1)]
ok = abs(lB1[0] - mpf("-0.5541")) < mpf("0.0005")
ok &= abs(lA1[0] - euler) < mpf(10)**-20
ok &= next(n for n in range(1, N1+1) if lB1[n-1] > 0) == 8
ok &= next(n for n in range(1, N1+1) if lB1[n-1] > abs(lA1[n-1])) == 11
ok &= all(x > 0 for x in lA1)
ok &= lA1[22] > lA1[23] < lA1[24]
ok &= abs(lA1[49] - mpf("1.4979")) < mpf("0.002")
print(f"  g1 lam_B(1) = {float(lB1[0]):.4f}; lam_A(1) - euler = {float(abs(lA1[0]-euler)):.1e}; "
      f"lam_A(50) = {float(lA1[49]):.4f}")
gate("g1 the two-regime anatomy: the primes carry Regime I; crossovers at 8 "
     "and 11; lam_A positive through 50", ok)

# ---------------------------------------------------------------- g2
ok = abs(euler + digamma(1)) < mpf(10)**-25
ok &= abs(euler - stieltjes(0)) < mpf(10)**-25
gate("g2 the junction constant: euler = -psi(1) = gamma_0, the number the "
     "channels share", ok)

# ---------------------------------------------------------------- g3
mp.dps = 60
M3, r3, N3 = 2048, mpf("0.95"), 1000
zsm = [r3*exp(mpc(0, 2*pi*m/M3)) for m in range(M3)]
sv = [1/(1 - z) for z in zsm]
lvB = [log(s/2) - (s/2)*log(pi) + loggamma(s/2) for s in sv]
lvA = [log((s - 1)*zeta(s)) for s in sv]
mjB = max(abs((lvB[(m+1) % M3] - lvB[m]).imag) for m in range(M3))
mjA = max(abs((lvA[(m+1) % M3] - lvA[m]).imag) for m in range(M3))
def coeffs(lv):
    out = []
    for n in range(1, N3 + 1):
        cc = sum(lv[m]*exp(mpc(0, -2*pi*n*m/M3)) for m in range(M3))/(M3*r3**n)
        out.append(float(n*cc.real))
    return out
lamB = coeffs(lvB)
lamA = coeffs(lvA)
ok = float(mjB) < math.pi and float(mjA) < math.pi
ok &= abs(lamA[0] + lamB[0] - 0.023095709) < 1e-8
ok &= abs(lamA[39] + lamB[39] - 30.4774) < 0.002
ok &= abs(lamA[49] + lamB[49] - 43.5311) < 0.002
ok &= abs(lamB[0] - float(lB1[0])) < 1e-3
ok &= abs(lamA[49] - float(lA1[49])) < 1e-3
ok &= abs(lamB[88] - 99.8944) < 0.005
neg = [n for n in range(1, N3+1) if lamA[n-1] < 0]
runs = [neg[0]] + [neg[i] for i in range(1, len(neg)) if neg[i] != neg[i-1] + 1]
ok &= neg[0] == 156 and len(neg) == 336
ok &= runs == [156, 247, 353, 424, 516, 603, 759, 919]
tr1 = min(lamA[n-1] for n in range(80, 96))
ok &= 0.20 < tr1 < 0.22
# round-198 F4 conjuncts: the trough census fully gated
ok &= min(range(80, 96), key=lambda n: lamA[n-1]) == 88
ok &= abs(tr1 - 0.208) < 0.0015
n2t = min(range(160, 186), key=lambda n: lamA[n-1])
ok &= n2t == 172 and -1.04 < lamA[171] < -1.01
nmin = min(range(1, N3+1), key=lambda n: lamA[n-1] + lamB[n-1])
ok &= nmin == 1 and abs(lamA[0] + lamB[0] - 0.0231) < 1e-3
ratios = [(abs(lamA[n-1])/lamB[n-1], n) for n in range(11, N3+1)]
mx = max(ratios)
ok &= abs(mx[0] - 0.8325) < 0.003 and mx[1] == 11
trend = 1000/2*(math.log(1000) + float(euler) - 1 - math.log(2*math.pi))
ok &= abs(lamB[999] - 2324.30) < 0.05 and abs(trend - 2323.54) < 0.05
print(f"  g3 branch steps B {float(mjB):.3f} A {float(mjA):.3f}; first neg {neg[0]}; "
      f"runs {runs}; count {len(neg)}; trough {tr1:.4f}; seam {mx[0]:.4f}@{mx[1]}; "
      f"lam_B(1000) = {lamB[999]:.2f}")
gate("g3 the thousand-direction census: cross-checked both routes; 156; the "
     "run starts; the seam maximum at 11; scarcity at n = 1; the trend "
     "identity", ok)

# ---------------------------------------------------------------- g4
mp.dps = 25
gams = [float(zetazero(k).imag) for k in range(1, 6)]
def W(k, n):
    th = math.pi - 2*math.atan(2*gams[k-1])
    return 2*(1 - math.cos(n*th))
ok = W(2, 132) < 0.01 and W(1, 132) > 3.98 and lamA[131] > 2.2
ok &= all(W(k, 156) < 2 for k in (1, 3, 4, 5)) and W(3, 156) < 0.01
p3 = 2*math.pi*gams[2]
ok &= 157.0 < p3 < 157.3 and abs(156 - p3) < 1.3
ok &= W(1, 178) < 0.01 and W(2, 178) > 3.1
# round-198 F3 conjunct: firstness POST-TRANSIENT -- the all-four-below
# condition holds through the small-n transient (n <= 22; marginally at
# its edge, W1(22) = 1.970 -- "trivially" retired round 200) and must
# first RETURN at exactly 156
first_post = next(n for n in range(23, 1001) if all(W(k, n) < 2 for k in (1, 3, 4, 5)))
ok &= first_post == 156
# round-200 conjuncts: the gloss figures witnessed (edge clearance and break)
ok &= 1.9695 < W(1, 22) < 2 and W(1, 23) > 2
print(f"  g4 W2(132) = {W(2,132):.4f}, W1(132) = {W(1,132):.4f}, lam_A(132) = {lamA[131]:.3f}; "
      f"2 pi gamma_3 = {p3:.2f}; W1(178) = {W(1,178):.4f}")
gate("g4 the phase-coincidence mechanism: single-withholder insufficiency at "
     "132; collective withholding at 156 on the third zero's clock; 178 exact", ok)

# ---------------------------------------------------------------- g5
x = np.array(lamA)
Wm = 179; h = Wm//2
D = x[h:N3-h] - np.convolve(x, np.ones(Wm)/Wm, mode='valid')
mE = len(D)//2
X5 = np.lib.stride_tricks.sliding_window_view(D, mE)
U, S, Vt = np.linalg.svd(X5, full_matrices=False)
Vs = Vt[:16].T
zev = np.linalg.eigvals(np.linalg.pinv(Vs[:-1]) @ Vs[1:])
cands = [(abs(np.angle(zz)), abs(zz)) for zz in zev if 0.012 < abs(np.angle(zz)) < 0.2]
def best_near(gtrue):
    scored = [(abs(1/(2*math.tan(a/2)) - gtrue), 1/(2*math.tan(a/2)), mod)
              for a, mod in cands]
    return min(scored)
e1, g1v, m1v = best_near(14.134725)
e2, g2v, m2v = best_near(21.022040)
ok = e1 < 5e-6 and abs(m1v - 1) < 5e-7   # round-199 finding 1: the round-198
# tightening (1e-4/1e-5) was still 20x looser than the paper's display
# "error < 5e-6 ... 1.000000", and the comment claiming closure was false
# as written; NOW the gate bounds equal the displayed bounds exactly (the
# extraction is mpmath-deterministic at dps 60; the numpy ESPRIT stage's
# platform jitter is ~1e-12, irrelevant at this tolerance)
ok &= e2 < 0.02 and abs(m2v - 1) < 5e-5   # round-200 cosmetic 4: gamma_2
# display-equal bounds under the same determinism argument (observed
# 0.0181 / 2.8e-5 -- margins 1.1x / 1.8x, honest for a deterministic gate)
print(f"  g5 gamma_1 recovered {g1v:.4f} (err {e1:.5f}, |pole| {m1v:.6f}); "
      f"gamma_2 {g2v:.4f} (err {e2:.4f}, |pole| {m2v:.6f})")
gate("g5 the pole-side inversion: gamma_1 and gamma_2 recovered with on-line "
     "pole moduli from arithmetic-channel data alone", ok)

# ---------------------------------------------------------------- g6
mp.dps = 40
def logw(beta, gam_):
    rho = mpc(beta, gam_)
    return float(abs(log(abs((rho - 1)/rho))))
# round-199 finding 2 (the accepted g6 half of the round-198 F8 cosmetic,
# missed in that sweep): this first conjunct is the algebraic identity
# |(rho-1)/rho| = 1 at beta = 1/2 (rho - 1 = -conj(rho)) -- a
# library-consistency check that cannot fail short of mpmath breakage;
# retained because the paper's on-line clause names it, nature stated here.
ok = logw(mpf("0.5"), mpf("14.134725")) < 1e-25
for beta, gam_ in ((mpf("0.5001"), mpf("14.13")), (mpf("0.51"), mpf("25")),
                   (mpf("0.500001"), mpf("100"))):
    exact = logw(beta, gam_)
    approx = float((2*beta - 1)/(2*gam_**2))
    ok &= abs(exact - approx)/approx < 0.03
gate("g6 the dichotomy rates: modulus 1 exactly on the line; off-line "
     "envelope rate (2 beta - 1)/(2 gamma^2) within 3%", ok)

# ---------------------------------------------------------------- g7
X7 = np.linspace(-20, 20, 16001)
xi7 = np.linspace(-20, 20, 4001)
def entpair(f):
    fv = f(X7); fv = fv/np.sqrt(np.trapezoid(fv**2, X7))
    F = np.array([np.trapezoid(fv*np.exp(-2j*np.pi*u*X7), X7) for u in xi7])
    p = fv**2; q = np.abs(F)**2; q = q/np.trapezoid(q, xi7)
    pm = np.where(p > 1e-300, p, 1.0)   # round-198 F9: mask before log
    qm = np.where(q > 1e-300, q, 1.0)   # (np.where evaluates both branches)
    h1 = -np.trapezoid(p*np.log(pm), X7)
    h2 = -np.trapezoid(q*np.log(qm), xi7)
    return h1, h2
hg, hgh = entpair(lambda t: np.exp(-np.pi*t**2))
he = sum(entpair(lambda t: np.exp(-np.abs(t))))
hs = sum(entpair(lambda t: np.exp(-np.pi*(t/1.7)**2)))
tgt = 1 - math.log(2)
ok = abs(hg + hgh - tgt) < 2e-3
ok &= he - tgt > 0.07
ok &= abs(hs - tgt) < 2e-3
ok &= abs(hg - tgt/2) < 2e-3 and abs(hgh - tgt/2) < 2e-3
print(f"  g7 gaussian sum {hg+hgh:.5f} (tgt {tgt:.5f}); exp {he:.5f}; "
      f"stretched {hs:.5f}; split {hg:.5f}/{hgh:.5f}")
gate("g7 the entropy anchors: family saturation at 1 - ln 2; self-duality "
     "as the equal split", ok)

# ---------------------------------------------------------------- g8
needles = [
    "**Theorem 1av (the two channels of the Li ladder: the two-regime",
    # round-198 F1 (R2): the landing's needle here carried 1au's line-wrap
    # ("no proof is\nclaimed") and was satisfied ONLY by the 1au block --
    # the 1av frame was unpinned; repointed to the 1av wrap:
    "**no proof is claimed, and\nnone resulted**",
    "the first Li direction's positivity is carried by the",
    "γ = −ψ(1) = γ₀",
    "first negative direction is\nn = 156",
    "maximum ratio 0.8325 AT THE SEAM n = 11",
    "λ₁ = 0.0231 at n = 1",
    "γ₁ recovered to 14.1347 (error < 5×10⁻⁶)",
    "struck round 198 F2, MAJOR",
    "the first POST-TRANSIENT collective withholding",
    "Mechanism-class MEMBERSHIP",
    "no\nUNPROVEN zero location enters",
    "resolve zeros 1–2 cleanly",
    "the\ncommitted M = 2048 instrument prints 0.061",
    "**There is no\nintermediate regime**",
    "DECLARED RESEARCH PROGRAM",
    "the arithmetic sits exactly at the phase boundary",
    "1 − ln 2 = 0.30685",
    "The coupling (P1)+(P2)→(P4) exists",
]
ok = all(nd in paper for nd in needles)
for nd in needles:
    if nd not in paper:
        print(f"  g8 MISSING: {nd!r}")
gate("g8 the 1av paper needles", ok)

# ---------------------------------------------------------------- g9
rr = subprocess.run([sys.executable, os.path.join(HERE, "cascade_attraction_margins.py")],
                    capture_output=True, text=True)
gate("g9 the chain: cascade_attraction_margins.py (Theorem 1au) exits 0",
     rr.returncode == 0)

# ---------------------------------------------------------------- g10
ok = paper.count("`cascade_li_two_channels.py`") >= 2
ok &= "78 scripts cited in place" in paper
ok &= "Theorems 1i–1bb" in paper
gate("g10 the footer census (this script backticked >= 2; 78 cited in place; "
     "the range 1i–1bb)", ok)

print()
if fails:
    print(f"FAILURES ({len(fails)}):")
    for f in fails:
        print("  " + f)
    sys.exit(1)
print("ALL GATES PASS (10/10)")
