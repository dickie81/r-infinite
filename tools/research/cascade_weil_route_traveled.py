#!/usr/bin/env python3
"""Theorem 1aj verifier: the route traveled -- the profile morphism,
the reachability of the admissible-discriminating cone, and the RH
wall located.

Claim under test: 1ai's gap (vi) asked for a committed morphism
from field configurations to self-convolution test functions whose
kernels change sign off the line while staying nonnegative on it.
Theorem 1aj supplies it and travels the route to its terminus:

R1 (the profile morphism, committed form): a lattice configuration
  c = (c_d) maps to the even test function
  g_c(x) = sum_d c_d exp(-(d+1/2)|x|) -- decay rates the bridge's
  own committed half-shift z = d+1/2.  Its explicit-formula
  transform is EXACTLY the committed kernel family:
  int_0^inf 2 e^{-(d+1/2)t} cosh((beta-1/2)t) cos(gamma t) dt
  = K_{d+1}(beta+i gamma).
R2 (reachability, exact): on the pairwise slice {(c_1, c_2),
  c_2 > 0} the admissible cone {L >= 0 on the line} is exactly
  {c_1/c_2 >= -w_1/w_2} (binding at gamma = 0; w = d+1/2), and the
  edge ratio -(2d_1+1)/(2d_2+1) is forced by the lattice.  At the
  edge h* = K_{s_2} - (w_1/w_2) K_{s_1}:
  L(gamma) = 2 gamma^2 (w_2^2-w_1^2) / (w_2 (w_1^2+gamma^2)
  (w_2^2+gamma^2)) >= 0 (zero only at gamma = 0), while at the
  strip boundary F(0) = -(w_2^2-w_1^2)/(2 w_2 (w_2^2-1/4)
  (w_1^2-1/4)) < 0: the edge of admissibility IS discriminating,
  for every pair.  The discriminating band is exact, BOTH
  directions proved (the converse supplied in the round-143
  sweep, F2, as Theorem R2'): the boundary kernel factors as
  K_s(0, gamma) = (2s-1)(u+a)/((u+a)^2+u) with a = s(s-1),
  u = gamma^2, and the boundary ratio r*(u) = K_{s2}/K_{s1}(0,
  gamma) is STRICTLY INCREASING in u -- d/du log r* =
  psi(u+a_2) - psi(u+a_1), psi(v) = 1/v - (2v+1)/(v^2+u), and
  psi'(v)'s numerator v^4+2v^3-4uv^2-u^2 >= v^2(v^2-2v+79) > 0
  for v >= u+20, guaranteed by the lattice floor a >= 20 at
  s = 5.  r* runs from the band endpoint
  r*(0) = (w_2/w_1)(w_1^2-1/4)/(w_2^2-1/4) (exact identity) up to
  the limit w_2/w_1: at-or-beyond-endpoint ratios keep the
  boundary nonnegative (blind, minimum principle); in-band ratios
  cross it (discriminating).  The same monotonicity proves the
  cone's OTHER edge blind for every pair (F_other >= 0 iff
  r* <= w_2/w_1, strict below the limit) -- round 143 F8 upgraded
  the coarse grid to theorem, the grid retained as a check.
  Band widths with the normalizer disclosed (round 143 F5): raw
  width (w_2^2-w_1^2)/(4 w_1 w_2 (w_2^2-1/4)); quoted as a
  fraction OF THE EDGE RATIO w_1/w_2 it is
  (w_2^2-w_1^2)/(4 w_1^2 (w_2^2-1/4)).  Observer pair (4, 5):
  edge ratio -9/11, magnitude 9/11 (1ai's window endpoint,
  transposed into admissibility); raw width exactly 1/297;
  band-to-edge fraction exactly 1/243.
R3 (genuine self-convolution): with f(x) = (w_2 e^{-w_2 x}
  - w_1 e^{-w_1 x})/(w_2-w_1) on x > 0, the autocorrelation
  f * f~ = [w_2 e^{-w_2|x|} - w_1 e^{-w_1|x|}] / (2 (w_1+w_2)
  (w_2-w_1)) -- exactly proportional to the edge profile -- and
  |f^(gamma)|^2 = gamma^2/((w_1^2+gamma^2)(w_2^2+gamma^2))
  reproduces L up to the positive scale 2(w_2^2-w_1^2)/w_2.  The
  reached instance is a genuine self-convolution of an explicit
  L1-cap-L2 function; membership in the classical dense class
  (smooth compactly supported f) is NOT claimed and nothing leans
  on it -- the zeros-side value is the bridge's unconditional
  identity at real s (graded round 143 F6).
R4 (the wall, located): (a) {h* < 0} is confined to |gamma| < 1/2
  for EVERY committed pair: h* is harmonic in rho on the strip
  (real parts of functions analytic there; poles at rho = s, 1-s
  lie outside), decays like 1/gamma^2, so by the minimum principle
  on {0 < beta < 1, |gamma| > 1/2} negativity would reach the
  region's boundary -- and the strip-boundary function F is
  nonnegative beyond its single crossing gamma_b < 1/2 (exhaustive
  scan over all 22791 pairs, counter-gated -- the landing
  docstring said 22578, an off-by-one census struck round 143 F1:
  sup gamma_b = 0.49999 at (216, 217); the bound approached is
  the half-shift itself), the gamma = 1/2 segment is positive
  (grid-gated per pair), and the tail coefficient
  2(w_2^2-w_1^2)/w_2 > 0.  Band-interior instances by domination
  (round 143 F3): h_r = h* + (w_1/w_2 - r) K_{s_1} with K_{s_1}
  > 0 on the whole strip, so {h_r < 0} is a subset of {h* < 0} --
  the confinement covers every PAIRWISE-SLICE discriminating
  instance (scope regraded, self-caught: the earlier "every
  discriminating instance" was false for the whole family -- see
  the REGRADE paragraph below the honest-scope block).  (b) By the bridge's
  paired-form identity (RH-free) the zeros side is computable with
  no zeros consumed: W(h*) = Z(6) - (9/11) Z(5) = 0.0780686 > 0,
  Z(s) = p(d) + 1/(d+1) + 1/d - sum Lambda(n) n^{-s}; the direct
  sum over the first 100 true zeros converges from below with
  every term positive.  (c) The sign's true forcer (A66): W < 0
  would require a zeta zero inside {h* < 0}, i.e. below height
  1/2; the first zero lies at gamma_1 = 14.134725 and zeta has no
  real zeros in (0, 1) (both classical) -- Weil positivity on
  every reached instance is forced by the CLASSICAL ZERO COUNT,
  not by cascade structure.  Action-positivity plays no role: the
  action is positive on ALL configurations; the admissible cone is
  cut by the transform, not the action.  Extending forced
  positivity to the dense class IS RH (Weil's criterion, classical
  input) -- unclaimable by the program's rule.  The route is
  traveled to the wall; the wall is located at exact coordinates
  ("reached instance" throughout (c) = the pairwise instances this
  theorem constructs; the REGRADE below widens the family's
  reach).

REGRADE (the wall widened -- self-caught post-certification,
triggered by the owner's asymptotics question; gates g19-g20):
the 1/2 has a mechanism -- the strip-boundary read is the line
read analytically continued by +/- i/2 and averaged (exact; g20).
A pair's admissible tangency is pinned to gamma = 0 (the two-term
numerator is degree 1 in gamma^2; a degree-1 polynomial
nonnegative on [0, inf) cannot vanish at an interior point -- the
failed 2-term aim gated in g19), so the pairwise ceiling = pinned
tangency + continuation distance 1/2.  With THREE committed
kernels the tangency relocates to any height: the aimed instance
on (4, 5, 6) with tangency at gamma_1 = 14.134725 is admissible
(L proportional to (u - gamma_1^2)^2 over positive denominators)
and its boundary window [13.5514, 14.5669] (inward-rounded 4 dp;
offsets -0.5834/+0.4322; precision made self-consistent round 147
F2 -- the round-146 join of independently rounded values
disagreed in its displayed digits and its endpoints fell outward
at half-ulp) CONTAINS the first zero (g19; endpoints first
corrected round 146 F2 -- the original draft quoted
outward-rounded endpoints under an "exactly").  The tangency
relocates to any chosen height (exact linear algebra, identical
in the aim), with window-nonemptiness-and-aim-containment
multi-aim gated (0.5, 3, 100 -- round 146 F3; the window contains
its aim ABOVE the continuation threshold aim* ~ 1/4 -- the
mechanism's 1/16 - aim^2 sign flip, observed 0.2436; below it the
window persists but DETACHES from the tangency, e.g. aim 0.1 ->
window [0.2108, 1.1229] (inward-rounded round 148 F2); the
below-threshold opposite sign gated -- round 147 F1 -- the reach
envelope pinned (upper reach ~ 0.91 at the threshold, down
through 1/2 at aim ~ 2.04, minimum ~ 0.412 near aim ~ 6.74, then
approaching 1/2 FROM BELOW, rising through the zero-height
regime -- shape corrected round 149 F1, the round-148 "decaying
to ~ 1/2" having been backwards there; asymmetric -- round 148
F1), and the window is
not exactly centred on its
aim); "classically
vacant" dies for relocated windows -- their positivity is
enforced by the verified on-line zeros (the grazed zero
contributing ~ 0), so the sign statement stays RH-content-free
while the instance becomes a per-zero sensitivity probe.  The
wall stands: nothing cascade-side forces positivity on any
discriminating instance; the dense-class extension is RH, claimed
in neither direction.

Gates (twenty-two: twenty as swept round 143, plus the regrade's
g19-g20):
  V1 (R1) -- g1 transform identity (quad vs K, 1e-8, six points);
       g2 the bridge's half-shift sentence anchored at source.
  V2 (R2) -- g3 L closed form (1e-12) + grid nonneg, zero only at
       gamma = 0; g4 the cone edge exact (ratio l2/l1 minimized at
       gamma = 0, value w_1/w_2, grid-monotone); g5 F(0) closed
       form < 0, matches direct (two pairs); g6 the band widths
       exact with the normalizer disclosed (raw 1/297,
       band-to-edge 1/243, consistency); g6b Theorem R2': the
       factorization TIED to the live kernel (round 144 F1 -- two
       decoupling sabotages passed 20/0 before the tie existed,
       both now tripping 19/1; 1e-14 over an (s, u) grid) + the
       endpoint identity exact (four pairs, rationals) + r*
       strictly increasing and strictly below the limit w_2/w_1
       on the grid (three pairs incl. extremes); g6c the R2'
       positivity certificate at the lattice-floor worst case
       a = 20, u-grid to 1e7, including the algebraic lower bound
       v^2(v^2-2v+79); g7 the other edge blind (F >= 0; observer
       fine grid + all-pairs coarse -- retained as a check under
       R2').
  V3 (R3) -- g8 autocorrelation quad vs closed form (1e-8);
       g9 the autocorrelation's profile coefficients EXTRACTED
       from quadrature at two x and their ratio gated against the
       live edge ratio (rebuilt round 143 F4 -- the first draft
       was a Fraction tautology that could not fail); g10 |f^|^2
       * 2(w_2^2-w_1^2)/w_2 = L (1e-10).
  V4 (R4) -- g11 observer negative set: gamma_b in (0.48, 0.481),
       min_beta h < 0 at gamma = 0.45, > 0 at 0.5, and > 0 on the
       gamma grid [0.5, 200]; g12 exhaustive pair scan,
       COUNTER-GATED at C(214,2) = 22791 (round 143 F1): gamma_b
       < 1/2 for every pair, single positive crossing (cubic root
       count), the gamma = 1/2 segment positive per pair, sup in
       (0.4999, 0.5) at (216, 217); g13 W = Z(6) -
       (9/11) Z(5) = 0.0780686 (5e-7), > 0, bridge identity only;
       g14 direct-zeros partial sum (100 zeros): every term
       positive, total < W; g15 the classical wall: gamma_1 =
       14.134725 (recomputed) > 1/2; zeta < 0 on real (0, 1)
       (grid).
  V4b (REGRADE) -- g19 the aimed three-term instances (entry
       updated round 148 F4): tangency at gamma_1 on committed
       (4, 5, 6), L >= 0 with the interior double zero, the
       boundary window contains the RECOMPUTED first zero, the
       2-term aim fails (the pinning), the multi-aim loop (0.5,
       3, 100 -- round 146 F3), the below-threshold opposite
       sign at aim 0.1 with aim/probe coupled (rounds 147
       F1/148 F3), the reach envelope (round 148 F1), and the
       reach SHAPE -- crossing, minimum, from-below ordering
       (round 149 F1);
       g20 the mechanism identity: boundary = line continued by
       +/- i/2, averaged, machine-exact.
  V5 -- g16 the two 1ai net-state markers anchored in the paper;
       g17 1aj's key sentences anchored AS REGRADED (entry updated
       round 146 F5): the edge theorem; the wall with the PAIRWISE
       scope; the relocatable windows ("including the heights of
       actual zeros"); the continuation-threshold sentence (added
       round 147, listed round 148 F4); the per-zero probe; the
       wall-stands sentence; R2''s monotonicity; the
       no-role-of-the-action;
       g18 the footer census (the script backticked; "82 scripts cited in place"; "Theorems 1i--1bf" -- the census
       advances with each landing; the gate carries the live
       values).

Grading: R1-R3 exact algebra with machine-precision gates (the
t-integral identities are classical Fourier bookkeeping); R4(a)
exhaustive over the committed lattice, minimum principle
(classical potential theory in the rho-plane) + grid-gated
segment checks, disclosed; R4(b) the bridge's own identity;
R4(c) classical inputs cited.  No data, no closures, no RH/GRH
in either direction.  Check 7 clean (Fourier bookkeeping, the
explicit formula, potential theory -- classical; no semiclassics).
Check 8 clean (every number traces to the lattice w = d+1/2).

Sabotage record (full-tree scratchpad copy, at the landing
commit; mid-anchor perturbations).  At the landing: (a) the
paper's "the edge of admissibility IS discriminating" perturbed
mid-anchor -> V5 g17 trips, 17/1, exit 1; (b) the live edge
coefficient flipped to -w_2/w_1 in the SCRATCHPAD COPY of this
verifier -> g3, g5, g10 print FAIL and the run then ABORTS at
g11's sign bracket (brentq finds no crossing; no RESULT line) --
the abort is part of the trip, exit 1, disclosed; (c) the 1ai
gap-(vi) net-state marker perturbed mid-anchor -> V5 g16 trips,
17/1, exit 1.  Redone at the round-143 sweep on the swept tree
(now 20 gates): (a) 19/1 exit 1; (b) 3 FAIL lines then the g11
abort, exit 1; (c) 19/1 exit 1; NEW (d) the pair loop's lower
bound shifted in the copy -> the F1 counter gate g12 FAILS at
"22578 pairs", 19/1, exit 1 -- the counter catches exactly the
F1 defect class; NEW (e) f_one's coefficients swapped in the
copy -> g8 AND the rebuilt g9 both FAIL, 18/2, exit 1 -- the F4
rebuild's bite demonstrated.  At the round-144 sweep (the
factorization-tie repair; entries appended round 145 F2): (f)
Nbound's a = s(s-1) -> s*s in the copy -> g6b FAIL (tie
9.0e-02), 19/1, exit 1; (g) Nbound's denominator v^2+u ->
v^2+3u -> g6b FAIL (tie 2.7e-03), 19/1, exit 1 -- both had
passed 20/0 before the tie existed.  Round 145 F1 added s = 217
to the tie grid, closing the s-conditional decoupling escape.
At the regrade (the relocatable-windows repair; the letter (h)
was skipped when these were added -- sequence gap noted round 146
F6): (i) GAMMA_AIM
shifted to 10.134725 in the copy -> g19 FAILS (the window no
longer contains the RECOMPUTED first zero), 21/1, exit 1; (j)
the paper's per-zero-probe sentence perturbed mid-anchor -> g17
trips, 21/1, exit 1.  At the round-146 sweep: (i') GAMMA_AIM
shift re-run against the extended gate -> g19, 21/1, exit 1;
(k) the multi-aim solve target decoupled from the aim
(ua = aim^2 + 5) -> g19, 21/1, exit 1.  At the round-147 sweep:
(l) the below-threshold probe moved above the threshold -> g19,
21/1, exit 1; (m) the threshold anchor perturbed mid-anchor
(above -> below) -> g17, 21/1, exit 1.  At the round-148 sweep:
(n) the coupled below-threshold aim shifted to 0.5 (above the
threshold, where the sign flips) -> g19, 21/1, exit 1 -- the
F148-3 coupling's bite (the record section brought current,
round 148 F5).  At the round-149 sweep (the reach-shape repair):
(o) the from-below bracket's aim shifted 50 -> 5 (reach ~0.42
leaves (0.47, 0.49)) -> g19, 21/1, exit 1; (p) the paper's shape
sentence perturbed mid-anchor (BELOW -> ABOVE) -- DISCLOSED
PRE-COMMIT CATCH: the first attempt did NOT trip (22/0) because
the shape sentence was not yet g17-anchored; the anchor was
added and the redone sabotage trips g17, 21/1, exit 1.  Clean
baselines (18/0 at landing, 20/0
after round 144, 22/0 thereafter) exit 0 before and after
each.  Twenty-two gates (count checked against the gate()
census; the count defect's history noted).
"""
import os
import sys

import numpy as np
from scipy.integrate import quad
from scipy.optimize import brentq

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
BRIDGE = os.path.join(ROOT, "tools", "research",
                      "cascade_explicit_formula_bridge.py")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


def K(s, b, g):
    return (s - b) / ((s - b) ** 2 + g ** 2) + (s - 1 + b) / ((s - 1 + b) ** 2 + g ** 2)


W1, W2 = 4.5, 5.5          # observer pair d = 4, 5
S1, S2 = 5, 6
R_EDGE = W1 / W2           # 9/11, forced


def hstar(b, g, w1=W1, w2=W2):
    return K(w2 + .5, b, g) - (w1 / w2) * K(w1 + .5, b, g)


print("V1 -- R1: the profile morphism (committed form)")
ok = True
worst = 0.0
for (s, b, g) in ((6, 0.2, 1.3), (5, 0.05, 0.6), (9, 0.9, 3.0),
                  (5, 0.5, 0.0), (218, 0.3, 7.0), (6, 0.01, 0.2)):
    z = s - 0.5
    # upper limit scaled to the decay rate (the s = 218 integrand
    # carries all its mass below t ~ 0.05)
    v, _ = quad(lambda t: 2 * np.exp(-z * t) * np.cosh((b - .5) * t)
                * np.cos(g * t), 0, 200.0 / (z - 0.5), limit=400)
    worst = max(worst, abs(v - K(s, b, g)))
ok = worst < 1e-8
gate("g1 the transform identity: int 2 e^{-(d+1/2)t} cosh((beta-1/2)t) "
     "cos(gamma t) dt = K_{d+1}(rho), six points", ok, f"worst {worst:.1e}")
bridge_src = norm(open(BRIDGE, encoding="utf-8").read())
gate("g2 the committed half-shift anchored at the bridge: "
     "'with s = d+1 and z = d + 1/2'",
     "with s = d+1 and z = d + 1/2" in bridge_src)

print("V2 -- R2: the admissible cone's edge is discriminating (exact)")
ok = True
for g in (0.3, 1.0, 3.7, 20.0):
    cf = 2 * g * g * (W2 ** 2 - W1 ** 2) / (W2 * (W1 ** 2 + g * g) * (W2 ** 2 + g * g))
    ok &= abs(hstar(.5, g) - cf) < 1e-12
gs = np.linspace(0.0, 200.0, 40001)
Lv = np.array([hstar(.5, g) for g in gs])
ok &= Lv[0] == 0.0 and (Lv[1:] > 0).all()
gate("g3 L closed form 2 gamma^2 (w2^2-w1^2)/(w2 (w1^2+g^2)(w2^2+g^2)), "
     "nonneg with zero only at gamma = 0", ok)
l2_over_l1 = (W2 / W1) * (W1 ** 2 + gs ** 2) / (W2 ** 2 + gs ** 2)
ok = abs(l2_over_l1[0] - W1 / W2) < 1e-15
ok &= (np.diff(l2_over_l1) > 0).all()
gate("g4 the cone edge exact: min_gamma l2/l1 at gamma = 0, value "
     "w1/w2 = 9/11, ratio grid-monotone increasing", ok)
ok = True
for (w1, w2) in ((4.5, 5.5), (100.5, 200.5)):
    F0_cf = -(w2 ** 2 - w1 ** 2) / (2 * w2 * (w2 ** 2 - .25) * (w1 ** 2 - .25))
    F0 = hstar(0, 0, w1, w2)
    ok &= F0_cf < 0 and abs(F0 - F0_cf) < 1e-14
gate("g5 the boundary value F(0) = -(w2^2-w1^2)/(2 w2 (w2^2-1/4)"
     "(w1^2-1/4)) < 0, closed form matches direct (two pairs)", ok)
from fractions import Fraction  # noqa: E402
w1f, w2f = Fraction(9, 2), Fraction(11, 2)
band = (w2f ** 2 - w1f ** 2) / (4 * w1f ** 2 * (w2f ** 2 - Fraction(1, 4)))
raw = w1f / w2f - (w2f / w1f) * (w1f ** 2 - Fraction(1, 4)) / (w2f ** 2 - Fraction(1, 4))
gate("g6 the band widths exact with the normalizer disclosed (round 143 "
     "F5): raw width 1/297; band-to-edge fraction (raw / (w1/w2)) 1/243",
     raw == Fraction(1, 297) and band == Fraction(1, 243)
     and raw / (w1f / w2f) == band, f"raw {raw}, fraction {band}")


def Nbound(s, u):
    a = s * (s - 1)
    v = u + a
    return (2 * s - 1) * v / (v * v + u)


ok = True
# round 144 F1: the factorization TIE -- Nbound must equal the live
# boundary kernel K(s, 0, gamma), else every downstream R2' gate runs
# on a decoupled function (two silent-pass sabotages demonstrated the
# hole before this gate existed).
tie = max(abs(Nbound(s, u) - K(s, 0, np.sqrt(u)))
          for s in (5, 6, 100, 217, 218)   # 217 added round 145 F1:
          # every s consumed downstream is now sampled, closing the
          # s-conditional decoupling escape the reviewer exhibited
          for u in (0.0, 0.04, 1.0, 47.0, 1e4))
ok &= tie < 1e-14
for (s1, s2) in ((5, 6), (5, 218), (100, 101), (216, 218)):
    w1r, w2r = Fraction(2 * s1 - 1, 2), Fraction(2 * s2 - 1, 2)
    r0 = Fraction((2 * s2 - 1) * s1 * (s1 - 1), (2 * s1 - 1) * s2 * (s2 - 1))
    ok &= r0 == (w2r / w1r) * (w1r ** 2 - Fraction(1, 4)) / (w2r ** 2 - Fraction(1, 4))
    ok &= r0 < w2r / w1r
us_m = np.linspace(0, 1e6, 100001)
for (s1, s2) in ((5, 6), (5, 218), (217, 218)):
    rvals = Nbound(s2, us_m) / Nbound(s1, us_m)
    ok &= (np.diff(rvals) > 0).all()
    ok &= (rvals < (2 * s2 - 1) / (2 * s1 - 1)).all()
gate("g6b Theorem R2' (round 143 F2): the factorization TIED to the "
     "live kernel (round 144 F1, 1e-14 over an (s, u) grid); boundary "
     "ratio r*(u) strictly increasing from the band endpoint (exact "
     "rational identity, four pairs) to w2/w1 (strict below the limit "
     "on the grid) -- the band's converse and the other edge's "
     "blindness", ok, f"tie {tie:.1e}")
us_c = np.linspace(0, 1e7, 100001)
cert = (us_c + 20) ** 4 + 2 * (us_c + 20) ** 3 - 4 * us_c * (us_c + 20) ** 2 - us_c ** 2
lower = (us_c + 20) ** 2 * ((us_c + 20) ** 2 - 2 * (us_c + 20) + 79)
gate("g6c the R2' positivity certificate: v^4+2v^3-4uv^2-u^2 >= "
     "v^2(v^2-2v+79) > 0 at the lattice-floor worst case a = 20 "
     "(v = u+20), u-grid to 1e7",
     (cert > 0).all() and (cert >= lower - 1e-6 * np.abs(lower)).all()
     and (lower > 0).all())
other = lambda g, w1, w2: (K(w1 + .5, 0, g)                       # noqa: E731
                           - (w1 / w2) * K(w2 + .5, 0, g))
ok = all(other(g, W1, W2) >= 0 for g in np.linspace(0, 200, 8001))
coarse_ok = True
for d1 in range(4, 217, 10):
    for d2 in range(d1 + 1, 218, 10):
        w1, w2 = d1 + .5, d2 + .5
        if any(other(g, w1, w2) < 0 for g in np.linspace(0, 60, 121)):
            coarse_ok = False
gate("g7 the other edge blind: F_other >= 0 (observer pair fine grid; "
     "all-pairs coarse sample)", ok and coarse_ok)

print("V3 -- R3: the edge instance is a genuine self-convolution")
f_one = lambda x: (W2 * np.exp(-W2 * x) - W1 * np.exp(-W1 * x)) / (W2 - W1)  # noqa: E731
ok = True
for x in (0.0, 0.3, 1.0, 2.5):
    v, _ = quad(lambda y: f_one(y) * f_one(y + x), 0, 80, limit=200)
    cf = (W2 * np.exp(-W2 * x) - W1 * np.exp(-W1 * x)) / (2 * (W1 + W2) * (W2 - W1))
    ok &= abs(v - cf) < 1e-8
gate("g8 the autocorrelation f*f~ = [w2 e^{-w2|x|} - w1 e^{-w1|x|}]"
     "/(2(w1+w2)(w2-w1)), quad vs closed form", ok)
# g9 rebuilt round 143 F4: the first draft gated a Fraction tautology
# that could not fail.  Now the autocorrelation's two exponential
# coefficients are EXTRACTED from quadrature values at two x points
# and their ratio gated against the live edge ratio.
x1, x2 = 0.4, 1.2
v1, _ = quad(lambda y: f_one(y) * f_one(y + x1), 0, 80, limit=200)
v2, _ = quad(lambda y: f_one(y) * f_one(y + x2), 0, 80, limit=200)
M = np.array([[np.exp(-W1 * x1), np.exp(-W2 * x1)],
              [np.exp(-W1 * x2), np.exp(-W2 * x2)]])
ca, cb = np.linalg.solve(M, np.array([v1, v2]))
gate("g9 the autocorrelation's extracted profile coefficients (solved "
     "from quadrature at two x) stand in the edge ratio: c_{w1}/c_{w2} "
     "= -w1/w2 (rebuilt round 143 F4 -- the first draft was a "
     "tautology)",
     abs(ca / cb + W1 / W2) < 1e-6 and abs(ca / cb + R_EDGE) < 1e-6,
     f"ratio {ca / cb:.8f}")
fh2 = lambda g: g * g / ((W1 ** 2 + g * g) * (W2 ** 2 + g * g))  # noqa: E731
scale = 2 * (W2 ** 2 - W1 ** 2) / W2
ok = all(abs(hstar(.5, g) - scale * fh2(g)) < 1e-10 for g in (0.5, 2.0, 10.0, 50.0))
gate("g10 |f^|^2 x 2(w2^2-w1^2)/w2 = L (the on-line profile IS a "
     "squared modulus)", ok)

print("V4 -- R4: the wall located")
gb = brentq(lambda g: hstar(0, g), 1e-9, 5)
bgrid = np.linspace(1e-4, 0.9999, 2001)
mn045 = min(hstar(b, 0.45) for b in bgrid)
mn05 = min(hstar(b, 0.5) for b in bgrid)
seg_ok = all(min(hstar(b, g) for b in np.linspace(0.001, 0.999, 201)) > 0
             for g in np.linspace(0.5, 200, 400))
gate("g11 the observer negative set: gamma_b in (0.48, 0.481); "
     "min_beta h < 0 at gamma = 0.45, > 0 at 0.5 and on [0.5, 200]",
     0.48 < gb < 0.481 and mn045 < 0 < mn05 and seg_ok,
     f"gamma_b = {gb:.4f}")
sup_gb, sup_pair, all_ok, seg_all, single_root = 0.0, None, True, True, True
npairs = 0
bseg = np.linspace(0.001, 0.999, 101)
for d1 in range(4, 217):
    w1 = d1 + .5
    for d2 in range(d1 + 1, 218):
        npairs += 1
        w2 = d2 + .5
        r = w1 / w2
        bs4 = np.array([d2 + 1, d2, d1 + 1, d1], dtype=float)
        a4 = np.array([1.0, 1.0, -r, -r])
        # F(gamma) numerator in u = gamma^2: sum_i a_i b_i prod_{j!=i}(b_j^2+u)
        poly = np.zeros(4)
        for i in range(4):
            pr = np.array([1.0])
            for j in range(4):
                if j != i:
                    pr = np.polymul(pr, np.array([1.0, bs4[j] ** 2]))
            poly = np.polyadd(poly, a4[i] * bs4[i] * pr)
        roots = np.roots(poly)
        pos = [np.sqrt(x.real) for x in roots
               if abs(x.imag) < 1e-9 and x.real > 0]
        if len(pos) != 1:
            single_root = False
        gb_p = pos[0] if pos else 0.0
        if gb_p >= 0.5:
            all_ok = False
        if gb_p > sup_gb:
            sup_gb, sup_pair = gb_p, (d1, d2)
        if min(K(w2 + .5, b, 0.5) - r * K(w1 + .5, b, 0.5)
               for b in bseg) <= 0:
            seg_all = False
gate("g12 exhaustive pair scan, COUNTER-GATED at C(214,2) = 22791 "
     "(round 143 F1 -- the landing said 22578, an off-by-one census): "
     "gamma_b < 1/2 for every committed pair, single boundary crossing, "
     "the gamma = 1/2 segment positive; sup at (216, 217)",
     npairs == 22791 and all_ok and single_root and seg_all
     and 0.4999 < sup_gb < 0.5 and sup_pair == (216, 217),
     f"{npairs} pairs, sup gamma_b = {sup_gb:.6f} at {sup_pair}")
from mpmath import mp, mpf, log as mplog, pi as mppi, diff, zeta, zetazero  # noqa: E402
mp.dps = 30


def Z(d):
    s = mpf(d + 1)
    primes = -diff(lambda t: mplog(zeta(t)), s)
    poles = mpf(1) / (d + 1) + mpf(1) / d
    p_d = -mplog(mppi) / 2 + mp.digamma(s / 2) / 2
    return p_d + poles - primes


# Z is d-indexed (s = d+1 inside): Z(5) is the zeros side at s = 6,
# Z(4) at s = 5 -- the gate text below is s-indexed (round 144 F2).
Wval = Z(5) - mpf(9) / 11 * Z(4)
gate("g13 the value by the bridge identity (no zeros consumed): "
     "W(h*) = Z(6) - (9/11) Z(5) = 0.0780686 > 0",
     Wval > 0 and abs(float(Wval) - 0.0780686) < 5e-7,
     f"W = {float(Wval):.7f}")
terms = []
for n in range(1, 101):
    g = zetazero(n).imag
    z2, z1 = mpf("5.5"), mpf("4.5")
    terms.append(2 * z2 / (z2 * z2 + g * g) - mpf(9) / 11 * 2 * z1 / (z1 * z1 + g * g))
partial = sum(terms)
gate("g14 the direct zeros-side partial sum (first 100 true zeros): "
     "every term positive, total below W (converging from below)",
     all(t > 0 for t in terms) and 0 < partial < Wval,
     f"partial = {float(partial):.7f}")
g1 = float(zetazero(1).imag)
sigma_ok = all(float(zeta(mpf(s))) < 0 for s in np.linspace(0.05, 0.95, 19))
gate("g15 the classical wall: gamma_1 = 14.134725 (recomputed) > 1/2; "
     "zeta < 0 on real (0, 1) -- no zeros in the PAIRWISE sensitive "
     "region (scope regraded: see g19)",
     abs(g1 - 14.134725) < 1e-5 and g1 > 0.5 and sigma_ok,
     f"gamma_1 = {g1:.6f}")

print("V4b -- the regrade: relocatable windows (self-caught)")
GAMMA_AIM = 14.134725
WS3 = np.array([4.5, 5.5, 6.5])          # committed d = 4, 5, 6
u0 = GAMMA_AIM ** 2
M3 = np.zeros((3, 3))
for i in range(3):
    oth = [WS3[j] ** 2 for j in range(3) if j != i]
    M3[0, i] = 2 * WS3[i]
    M3[1, i] = 2 * WS3[i] * (oth[0] + oth[1])
    M3[2, i] = 2 * WS3[i] * oth[0] * oth[1]
c3 = np.linalg.solve(M3, np.array([1.0, -2 * u0, u0 * u0]))
L3 = lambda g: sum(c3[i] * 2 * WS3[i] / (WS3[i] ** 2 + g * g)  # noqa: E731
                   for i in range(3))
F3 = lambda g: sum(c3[i] * K(WS3[i] + .5, 0, g) for i in range(3))  # noqa: E731
gg = np.linspace(0.0, 300.0, 300001)
L3v = np.array([L3(g) for g in gg])
F3v = np.array([F3(g) for g in gg])
neg = gg[F3v < 0]
# the failed 2-term aim: a degree-1 numerator forced through an
# interior root goes negative at u = 0 (the pinning, by construction)
M2 = np.array([[2 * 4.5, 2 * 5.5],
               [2 * 4.5 * 5.5 ** 2, 2 * 5.5 * 4.5 ** 2]])
c2 = np.linalg.solve(M2, np.array([1.0, -u0]))
L2_at_0 = c2[0] * 2 * 4.5 / 4.5 ** 2 + c2[1] * 2 * 5.5 / 5.5 ** 2
# round 146 F3: the relocation universal is multi-aim gated -- for a
# spread of aims the solved instance must be admissible (relative L
# floor) with the boundary negative AT the aim itself.  Round 147 F1:
# the containment holds only ABOVE the continuation threshold
# aim* ~ 1/4 (the mechanism's 1/16 - aim^2 sign flip; observed
# 0.2436); the below-threshold OPPOSITE sign is gated after the loop.
multi_ok = True
for aim in (0.5, 3.0, 100.0):
    ua = aim * aim
    ca = np.linalg.solve(M3, np.array([1.0, -2 * ua, ua * ua]))
    La = lambda g: sum(ca[i] * 2 * WS3[i] / (WS3[i] ** 2 + g * g)  # noqa: E731,B023
                       for i in range(3))
    Fa = lambda g: sum(ca[i] * K(WS3[i] + .5, 0, g)  # noqa: E731,B023
                       for i in range(3))
    ga = np.linspace(0.0, aim + 60.0, 200001)
    Lav = np.array([La(g) for g in ga])
    multi_ok &= Lav.min() > -1e-12 * max(1.0, Lav.max())
    multi_ok &= Fa(aim) < 0
# round 147 F1: below the threshold the sign at the aim FLIPS -- the
# window detaches from the tangency.  Gate the opposite sign at
# aim = 0.1 to pin the claim's boundary.  Round 148 F3: the instance
# aim and the probe point are now COUPLED through one variable (the
# first draft's independent literals admitted a silent decoupling
# pass, demonstrated by the reviewer).
aimb = 0.1
ub = aimb * aimb
cb = np.linalg.solve(M3, np.array([1.0, -2 * ub, ub * ub]))
Fb = lambda g: sum(cb[i] * K(WS3[i] + .5, 0, g) for i in range(3))  # noqa: E731
multi_ok &= Fb(aimb) > 0
# rounds 148 F1 / 149 F1: the reach ENVELOPE gated -- the upper
# reach runs from ~0.91 at the threshold down THROUGH 1/2 (crossing
# at aim ~2.04), bottoms ~0.412 near aim ~6.74, then approaches 1/2
# FROM BELOW (rising through the zero-height regime; the round-148
# comment said "decays toward 1/2", backwards there).  The envelope
# numbers, the crossing, the minimum, and the from-below ordering
# are pinned.
from scipy.optimize import brentq as _brentq  # noqa: E402


def _reach_hi(aim):
    ua_ = aim * aim
    ca_ = np.linalg.solve(M3, np.array([1.0, -2 * ua_, ua_ * ua_]))
    Fa_ = lambda g: sum(ca_[i] * K(WS3[i] + .5, 0, g)  # noqa: E731
                        for i in range(3))
    return _brentq(Fa_, max(aim + 0.05, 0.3), aim + 2.0) - aim


env_ok = 0.90 < _reach_hi(0.244) < 0.92
env_ok &= 0.76 < _reach_hi(0.5) < 0.78
env_ok &= 0.54 < _reach_hi(1.5) < 0.56
r_g1 = _reach_hi(GAMMA_AIM)
env_ok &= 0.42 < r_g1 < 0.44
env_ok &= 0.57 < GAMMA_AIM - neg.min() < 0.59
# round 149 F1: the SHAPE pinned -- the crossing through 1/2, the
# minimum, and the from-below rising approach.
env_ok &= _reach_hi(2.0) > 0.5 > _reach_hi(2.1)
env_ok &= 0.405 < _reach_hi(6.744) < 0.415
r_50 = _reach_hi(50.0)
env_ok &= r_g1 < r_50 < 0.5 and 0.47 < r_50 < 0.49
multi_ok &= env_ok
gate("g19 the aimed three-term instances (regrade): tangency relocated "
     "to gamma_1 = 14.134725 on committed (4, 5, 6) -- L >= 0 with the "
     "interior double zero; the boundary window contains the RECOMPUTED "
     "first zero; the 2-term aim FAILS (L(0) < 0, the pinning); AND the "
     "relocation universal multi-aim gated (aims 0.5, 3, 100: "
     "admissible, boundary negative at the aim -- round 146 F3; the "
     "below-threshold OPPOSITE sign at aim 0.1 gated, aim/probe "
     "coupled -- rounds 147 F1/148 F3; the reach ENVELOPE pinned: "
     "0.91 at the threshold, 0.77 at 0.5, 0.55 at 1.5, "
     "-0.583/+0.432 at gamma_1 -- round 148 F1; the SHAPE pinned: "
     "crossing 1/2 in (2.0, 2.1), minimum ~0.412 at 6.744, rising "
     "from below at height (r_g1 < r_50 < 1/2) -- round 149 F1)",
     L3v.min() > -1e-9 and abs(L3(GAMMA_AIM)) < 1e-9
     and len(neg) > 0 and neg.min() < g1 < neg.max()
     and (neg.min() > GAMMA_AIM - 0.7) and (neg.max() < GAMMA_AIM + 0.5)
     and L2_at_0 < 0 and multi_ok,
     f"window [{neg.min():.3f}, {neg.max():.3f}] contains {g1:.4f}; "
     f"2-term L(0) = {L2_at_0:.2e}; multi-aim {multi_ok}")
ok = True
for (s, g) in ((6, 1.0), (5, 0.3), (7, 14.0), (218, 2.0), (6, 0.0)):
    w = s - 0.5
    cont = 0.5 * (2 * w / (w * w + (g + 0.5j) ** 2)
                  + 2 * w / (w * w + (g - 0.5j) ** 2))
    ok &= abs(cont.imag) < 1e-15 and abs(cont.real - K(s, 0, g)) < 1e-14
gate("g20 the mechanism identity (regrade): the strip-boundary read = "
     "the line read continued by +/- i/2 and averaged, exact at "
     "machine precision", ok)

print("V5 -- the anchors and the footer")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = ("Net state (1aj): superseded-true — Theorem 1aj constructs an "
      "admissible-discriminating instance from the committed pair itself"
      in paper)
ok &= ("Net state (1aj): the morphism now exists" in paper)
gate("g16 the two 1ai net-state markers anchored (W3's supersession; "
     "gap (vi)'s closure)", ok)
ok = "the edge of admissibility IS discriminating" in paper
ok &= "the RH wall itself, now located at exact coordinates" in paper
# regrade anchor swap: the old universal ("every committed-family
# discriminating instance interrogates only...") is STRUCK in the
# paper -- the anchors below are the regraded live sentences.
ok &= ("every pairwise discriminating instance interrogates only the "
       "classically vacant height-½ band" in paper)
ok &= ("relocatable to any height — including the heights of actual "
       "zeros" in paper)
ok &= ("containing it for tangencies above the continuation threshold "
       "≈ ¼" in paper)
ok &= ("approaches ½ FROM BELOW — rising with height throughout the "
       "zero-height regime" in paper)
ok &= "a genuine per-zero sensitivity probe" in paper
ok &= "the wall stands where it stood" in paper
ok &= "action-positivity plays no role in the sign" in paper
ok &= ("r*(u) = K_{s₂}/K_{s₁}(0, γ) is STRICTLY INCREASING in u" in paper)
ok &= "the other edge is blind, by theorem" in paper
gate("g17 1aj's key sentences anchored as regraded (the edge theorem; "
     "the wall with the PAIRWISE scope; the relocatable windows; the "
     "per-zero probe; R2'; the no-role-of-the-action)", ok)
# 1ak landing: the footer census advanced (60 -> 61; range -> 1ak);
# 1al landing: advanced again (61 -> 62; range -> 1al); 1am landing:
# advanced again (62 -> 63; range -> 1am); 1an landing: advanced
# again (63 -> 64; range -> 1an); 1ao landing: advanced again
# (64 -> 65; range -> 1ao) -- the census-evolution class,
# disclosed each time.
ok = "`cascade_weil_route_traveled.py`" in paper
ok &= "82 scripts cited in place" in paper
ok &= "Theorems 1i–1bf" in paper
gate("g18 the footer census (advanced with each landing, "
     "disclosed): this script backticked; 82 cited in "
     "place; the range 1i–1bf (advance disclosed; label re-synced "
     "rounds 175 F2, 176 F2, and again round 213 F3 -- the census "
     "value missed in the 175 pass and in the 1ba sweep)", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (22 gates)")
print("READING: the route is traveled.  R1: the profile morphism exists")
print("in committed form -- configurations to test functions via the")
print("bridge's half-shift z = d+1/2, transforming exactly onto the")
print("committed kernel family.  R2: the pairwise admissible cone's")
print("edge ratio is forced by the lattice (-(2d1+1)/(2d2+1); observer")
print("pair 9/11, 1ai's window endpoint transposed), and the edge IS")
print("discriminating -- on-line nonnegative, off-line sign-changing --")
print("for every pair; the discriminating band is exact BOTH directions")
print("(the converse by R2''s boundary-ratio monotonicity, round 143;")
print("observer band-to-edge fraction 1/243, raw width 1/297), and the")
print("cone's other edge is blind by the same theorem.  R3: the edge")
print("instance is a genuine self-convolution of an explicit L1/L2")
print("function (dense-class membership not claimed, round 143 F6).")
print("R4 (REGRADED -- the READING resweep, round 146 F1: the first")
print("regrade left the struck universal live in this block): the")
print("PAIRWISE instances' negative sets are confined below height 1/2")
print("(minimum principle + domination on the pairwise slice;")
print("exhaustive counter-gated scan over 22791 pairs; sup gamma_b =")
print("0.49999 -- the half-shift, which is the +/- i/2 continuation")
print("distance, g20).  The pinning is a two-term artifact: three")
print("committed kernels relocate the tangency to any aim (gated at")
print("gamma_1 = 14.134725 and a spread of other aims, g19; containing")
print("its aim above the ~ 1/4 continuation threshold and detaching")
print("below it, the opposite sign gated -- round 147 F1); the aimed")
print("window CONTAINS the first zero, so 'classically vacant' holds")
print("only pairwise, and relocated windows rest on the verified")
print("on-line zeros.  W = 0.0780686 > 0 by the bridge identity; the")
print("sign is forced by classical zero-location data, NOT by cascade")
print("structure -- action-positivity plays no role.  The wall:")
print("extending forced positivity to the dense class IS RH (Weil's")
print("criterion, classical); unclaimable by the program's rule.  The")
print("route terminates at the wall -- widened, surveyed, and claimed")
print("in neither direction.")
sys.exit(0 if n_fail == 0 else 1)
