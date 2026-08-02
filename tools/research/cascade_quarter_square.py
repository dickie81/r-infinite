#!/usr/bin/env python3
"""Theorem 1ak verifier: the quarter-square -- one scale behind five
constants.

Claim under test: five constants of the traveled route -- four
already on the committed record, one exhibited here for the first
time (the vertex; the count corrected round 151 F1, the landing
having said "five separately-recorded") -- are the SAME
quarter-square (1/2)^2 = 1/4 -- the
functional equation's half-shift squared under the u = z^2 change
of variable -- by exact algebra:

Q1 (the parabola and its vertex): under v = (rho - 1/2)^2 the
  critical line maps to the negative real ray (v = -gamma^2) and
  the strip boundary beta in {0, 1} maps to the parabola
  Re v = 1/4 - (Im v)^2; the two boundary lines' real-axis points
  -- s = 1 (zeta's pole) and s = 0 (its functional-equation
  mirror; "corners" corrected round 151 F6) -- map to the vertex
  v = 1/4.  The quarter-square is the pole's image under the
  squared-shift map: +1/4 in the v-plane, equivalently -1/4 in
  the height plane u = gamma^2 used by R2' and Q2-Q3 (u = -v on
  the line), where the pole's image IS Q3's displacement constant
  (the plane-name conflation corrected round 151 F4).
Q2 (the prefactor is the anchor): the R2' factorization constant
  a = s(s-1) -- every lattice kernel's u-space anchor -- is xi's
  pole-cancelling polynomial factor UP TO THE CONSTANT 1/2 (the
  bridge's source: mpf("0.5") * s * (s - 1); "exactly xi's own
  prefactor" struck round 151 F2 -- the quoted line itself
  carries the 1/2), and equals w^2 - 1/4 at the committed half-shift
  w = d + 1/2: each lattice site's anchor is its squared
  half-shift minus the quarter-square (exact, every d in
  [1, 217]).  The boundary kernel's denominator factors EXACTLY:
  (u + a)^2 + u = (u + s^2)(u + (s-1)^2) -- each committed kernel
  anchored by the adjacent squared layers -d^2, -(d+1)^2, with
  the on-line kernel's single pole -(d+1/2)^2 interlaced.
Q3 (the displacement): in u-space the +/- i/2 continuation (the
  1aj g20 mechanism) is the displacement u -> u - 1/4 +/-
  i sqrt(u): the strip-boundary read is the line read displaced
  by a CONSTANT real quarter-square plus a height-proportional
  imaginary part.  The real displacement never varies.
Q4 (the threshold's leading order is exactly 1/4): at an aimed
  instance's tangency the displaced double-zero factor is
  (-1/4 +/- i gamma_0)^2, real part 1/16 - gamma_0^2 -- so with
  the denominators FROZEN at the tangency the detachment
  threshold is EXACTLY 1/4; the observed 0.24357 (round 147) is
  1/4 minus the denominator-variation correction 0.00643
  (root-found; family-specific while the frozen 1/4 is
  family-independent -- both gated, round 151 F7).  The round-147
  threshold is the quarter-square to leading order -- the pole's
  image reappearing.

Unification only: no new RH content in either direction; no
data; no closures.  Check 7 clean (change of variable, partial
fractions, root-finding -- classical bookkeeping; a = d(d+1) is
stated as arithmetic, the product of adjacent layer indices, and
no spectral procedure is invoked).  Check 8 clean (no hypothesis
input; every identity is classical algebra over the committed
lattice w = d + 1/2).

Gates (twelve):
  V1 (Q1) -- g1 BOTH strip-boundary edges -> the parabola
       Re v = 1/4 - (Im v)^2 (beta = 0 and 1 sampled, round 151
       F5); the boundary lines' real-axis points s = 0, 1 -> the
       vertex 1/4 (exact rationals); the line -> the negative
       ray.
  V2 (Q2) -- g2 a = s(s-1) = w^2 - 1/4 exact for every d in
       [1, 217] (rationals); g3 the bridge's xi prefactor
       anchored at source (mpf("0.5") * s * (s - 1)); g4 the
       factorization (u+a)^2 + u = (u+s^2)(u+(s-1)^2) checked
       LIVE at three exact-rational u per d (rebuilt round 151
       F3 -- the first draft's constant conjunct was a
       tautology), with the interlacing (s-1)^2 < w^2 < s^2.
  V3 (Q3) -- g5 the u-space displacement identity: the boundary
       read equals the average of the line read at
       u - 1/4 +/- i sqrt(u), machine precision at samples;
       g6 the displacement's real part is the CONSTANT -1/4:
       (gamma +/- i/2)^2 - gamma^2 = -1/4 +/- i gamma, exact at
       samples.
  V4 (Q4) -- g7 the frozen-numerator algebra COMPUTED in
       rational components (rebuilt round 151 F3 -- the first
       draft was a self-comparison), root exactly at g = 1/4;
       g8 the frozen-denominator threshold root-found = 1/4
       within 1e-9 (the aimed (4, 5, 6) family, denominators
       frozen at the tangency); g9 the full threshold in
       (0.2435, 0.2437) with deficit 1/4 - aim* in
       (0.006, 0.007) -- the denominator-variation correction,
       family-specific with a second family gated both ways
       (round 151 F7).
  V5 -- g10 the 1aj sentences 1ak leans on, anchored LOCATIONALLY
       in the pre-1ak span (the threshold sentence; the
       mechanism sentence) -- locational per the
       self-satisfying-gate lesson; g11 1ak's key sentences
       anchored as swept round 151 (the two-plane pole image;
       the up-to-half prefactor); g12 the footer census (the new script
       backticked; "61 scripts cited in place"; "Theorems
       1i–1ak").

Sabotage record (full-tree scratchpad copy, at the landing
commit; mid-anchor perturbations): (a) the paper's "the
detachment threshold is EXACTLY ¼" perturbed mid-anchor -> g11
trips, 11/1, exit 1; (b) the displacement constant -0.25 flipped
to -0.30 in the SCRATCHPAD COPY of this verifier -> g5 trips
(the identity breaks at 1.1e-3), 11/1, exit 1; (c) the frozen-
threshold construction's real displacement perturbed in the copy
-> g8 trips, 11/1, exit 1.  At the round-151 sweep (the F3
rebuilds and the F4 anchor swap): (d) the rebuilt g7's component
A_COMP flipped to -1/5 in the copy -> g7 trips, 11/1, exit 1 --
the self-comparison's replacement bites; (e) the rebuilt g4's
live factorization perturbed ((s-1)^2 -> (s-2)^2) -> g4 trips,
11/1, exit 1; (a') the F4-rewritten anchored sentence perturbed
mid-anchor (IS -> WAS) -> g11 trips, 11/1, exit 1.  At the
round-152 sweep (the g7 imaginary-component repair): (f)
im_minus's sign flipped in the copy -> g7 trips via sq_im_avg,
11/1, exit 1 -- the previously-dead conjunct now bites.  Clean
baselines 12/0 exit 0 before
and after each.  Twelve gates (count checked against the gate()
census pre-commit; the count defect's history noted).
"""
import os
import sys
from fractions import Fraction

import numpy as np
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


print("V1 -- Q1: the parabola and its vertex")
ok = True
for g in (0.0, 0.7, 3.0, 14.134725):
    for x in (-0.5, 0.5):        # both boundary edges (round 151 F5)
        v = complex(x, g) ** 2
        ok &= abs(v.real - (0.25 - v.imag ** 2)) < 1e-12
ok &= Fraction(-1, 2) ** 2 == Fraction(1, 4) == Fraction(1, 2) ** 2
ok &= complex(0, 2.5) ** 2 == -6.25 + 0j
gate("g1 BOTH strip-boundary edges map to the parabola Re v = 1/4 - "
     "(Im v)^2 (beta = 0 and 1 sampled, round 151 F5); the boundary "
     "lines' real-axis points s = 0, 1 map to the vertex 1/4; the "
     "line to the negative ray", ok)

print("V2 -- Q2: the prefactor is the anchor")
ok = all(Fraction(d + 1) * Fraction(d) ==
         Fraction(2 * d + 1, 2) ** 2 - Fraction(1, 4)
         for d in range(1, 218))
gate("g2 a = s(s-1) = w^2 - 1/4 exact for every d in [1, 217] "
     "(each anchor = the squared half-shift minus the quarter-square)",
     ok)
bridge_src = open(BRIDGE, encoding="utf-8").read()
gate("g3 the xi prefactor anchored at the bridge's source: "
     "mpf(\"0.5\") * s * (s - 1)",
     'mpf("0.5") * s * (s - 1)' in bridge_src)
ok = True
for d in range(1, 218):
    s = d + 1
    a = s * (s - 1)
    # round 151 F3: the first draft's constant-coefficient conjunct
    # was a tautology (a*a == (s(s-1))^2 given a's definition).  Now
    # the factorization is checked LIVE by evaluating both sides at
    # sample u values in exact rationals.
    for u in (Fraction(1), Fraction(7), Fraction(-3, 2)):
        ok &= (u + a) ** 2 + u == (u + s * s) * (u + (s - 1) ** 2)
    ok &= (s - 1) ** 2 < (Fraction(2 * d + 1, 2)) ** 2 < s ** 2
gate("g4 the factorization (u+a)^2 + u = (u+s^2)(u+(s-1)^2) checked "
     "LIVE at three exact-rational u per d (rebuilt round 151 F3 -- "
     "the first draft's constant conjunct was a tautology); the "
     "on-line pole -(d+1/2)^2 interlaced between the adjacent squared "
     "layers", ok)

print("V3 -- Q3: the displacement")
worst = 0.0
for (s, g) in ((6, 1.0), (5, 0.3), (7, 14.0), (218, 2.0)):
    u = g * g
    w = s - 0.5
    val = 0.5 * (2 * w / (w * w + (u - 0.25 + 1j * g))
                 + 2 * w / (w * w + (u - 0.25 - 1j * g)))
    worst = max(worst, abs(val.real - K(s, 0, g)), abs(val.imag))
gate("g5 the u-space displacement identity: the boundary read = the "
     "line read averaged at u - 1/4 +/- i sqrt(u), machine precision",
     worst < 1e-14, f"worst {worst:.1e}")
ok = True
for g in (0.1, 1.0, 14.134725):
    lhs = (g + 0.5j) ** 2 - g * g
    ok &= abs(lhs - (-0.25 + 1j * g)) < 1e-14
gate("g6 the displacement's real part is the CONSTANT -1/4 at every "
     "height: (gamma + i/2)^2 - gamma^2 = -1/4 + i gamma", ok)

print("V4 -- Q4: the threshold's leading order is exactly 1/4")
# round 151 F3: the first draft compared an expression to a copy of
# itself.  Round 152 F1: the F3 rebuild itself left a cannot-fail
# conjunct (sq_im_avg assigned a literal zero under a comment claiming
# 2ab was computed).  Now BOTH components are computed
# ((a, b) -> (a^2 - b^2, 2ab)), the conjugate pair's imaginary parts
# averaged for real -- perturbing a = -1/4 trips via sq_re, and
# flipping either imaginary component's sign trips via sq_im_avg.
ok = True
A_COMP = Fraction(-1, 4)
for g0 in (Fraction(1, 10), Fraction(1, 4), Fraction(2, 5)):
    sq_re = A_COMP * A_COMP - g0 * g0          # Re[(a + i b)^2]
    im_plus = 2 * A_COMP * g0                  # Im[(a + i b)^2]
    im_minus = 2 * A_COMP * (-g0)              # Im[(a - i b)^2]
    sq_im_avg = (im_plus + im_minus) / 2       # averaged with conjugate
    ok &= sq_re == Fraction(1, 16) - g0 ** 2 and sq_im_avg == 0
    if g0 == Fraction(1, 4):
        ok &= sq_re == 0
gate("g7 the frozen-numerator algebra COMPUTED in rational components "
     "(rebuilt round 151 F3 -- the first draft was a self-comparison): "
     "Re[(-1/4 +/- i g)^2] = 1/16 - g^2, root exactly at g = 1/4", ok)
WS3 = np.array([4.5, 5.5, 6.5])
M3 = np.zeros((3, 3))
for i in range(3):
    oth = [WS3[j] ** 2 for j in range(3) if j != i]
    M3[0, i] = 2 * WS3[i]
    M3[1, i] = 2 * WS3[i] * (oth[0] + oth[1])
    M3[2, i] = 2 * WS3[i] * oth[0] * oth[1]


def F_frozen(aim):
    u0 = aim * aim
    Dfr = np.prod([w * w + u0 for w in WS3])
    return 0.5 * (((u0 - 0.25 + 1j * aim) - u0) ** 2
                  + ((u0 - 0.25 - 1j * aim) - u0) ** 2).real / Dfr


thf = brentq(F_frozen, 0.2, 0.3)
gate("g8 the frozen-denominator threshold root-found = 1/4 within "
     "1e-9 (the aimed (4, 5, 6) family, denominators frozen at the "
     "tangency)", abs(thf - 0.25) < 1e-9, f"{thf:.10f}")


def F_at_aim(aim):
    u0 = aim * aim
    c = np.linalg.solve(M3, np.array([1.0, -2 * u0, u0 * u0]))
    return sum(c[i] * K(WS3[i] + .5, 0, aim) for i in range(3))


th = brentq(F_at_aim, 0.2, 0.3)
# round 151 F7: the frozen 1/4 is family-independent, the correction
# is not -- both directions gated with a second family (3.5, 4.5, 5.5).
WSB = np.array([3.5, 4.5, 5.5])


def F_frozen_b(aim):
    u0 = aim * aim
    Dfr = np.prod([w * w + u0 for w in WSB])
    return 0.5 * (((u0 - 0.25 + 1j * aim) - u0) ** 2
                  + ((u0 - 0.25 - 1j * aim) - u0) ** 2).real / Dfr


thf_b = brentq(F_frozen_b, 0.2, 0.3)
MB = np.zeros((3, 3))
for i in range(3):
    oth = [WSB[j] ** 2 for j in range(3) if j != i]
    MB[0, i] = 2 * WSB[i]
    MB[1, i] = 2 * WSB[i] * (oth[0] + oth[1])
    MB[2, i] = 2 * WSB[i] * oth[0] * oth[1]


def F_at_aim_b(aim):
    u0 = aim * aim
    c = np.linalg.solve(MB, np.array([1.0, -2 * u0, u0 * u0]))
    return sum(c[i] * K(WSB[i] + .5, 0, aim) for i in range(3))


th_b = brentq(F_at_aim_b, 0.2, 0.3)
gate("g9 the full threshold in (0.2435, 0.2437) with deficit in "
     "(0.006, 0.007) -- the denominator-variation correction, "
     "FAMILY-SPECIFIC (round 151 F7: the second family (3, 4, 5) "
     "gives a different threshold while its frozen root stays 1/4)",
     0.2435 < th < 0.2437 and 0.006 < 0.25 - th < 0.007
     and abs(thf_b - 0.25) < 1e-9 and abs(th_b - th) > 0.002,
     f"aim* = {th:.8f}, deficit {0.25 - th:.8f}; family B aim* = "
     f"{th_b:.8f}, frozen {thf_b:.10f}")

print("V5 -- the anchors and the footer")
paper_raw = open(PAPER, encoding="utf-8").read()
i_ak = paper_raw.find("**Theorem 1ak (")
assert i_ak > 0
pre = norm(paper_raw[:i_ak]).replace("**", "")
paper = norm(paper_raw).replace("**", "")
ok = ("containing it for tangencies above the continuation threshold "
      "≈ ¼" in pre)
ok &= ("the strip-boundary read is the line read analytically continued "
       "by ±i/2 and averaged" in pre)
gate("g10 the 1aj sentences 1ak leans on, anchored LOCATIONALLY in the "
     "pre-1ak span (the threshold; the mechanism)", ok)
# round 151 F4: the anchored punchline rewritten -- the pole's image
# is +1/4 in the v-plane and -1/4 in the height plane u = gamma^2
# (where it IS the displacement constant); anchors updated.
ok = ("The quarter-square is the pole's image under the squared-shift "
      "map" in paper)
ok &= "where the pole's image IS Q3's displacement constant" in paper
ok &= ("ξ's pole-cancelling polynomial factor UP TO THE CONSTANT ½"
       in paper)
ok &= ("each lattice site's anchor is its squared half-shift MINUS the "
       "quarter-square" in paper)
ok &= ("the strip-boundary read is the line read displaced by a "
       "CONSTANT real quarter-square" in paper)
ok &= ("with the denominators frozen at the tangency, the detachment "
       "threshold is EXACTLY ¼" in paper)
ok &= "one scale — (½)², the functional equation's half-shift squared" in paper
gate("g11 1ak's key sentences anchored AS SWEPT round 151 (the "
     "two-plane pole image -- F4; the up-to-half prefactor -- F2; the "
     "anchors; the displacement; the frozen threshold; the "
     "unification)", ok)
# 1al landing: the footer census advanced (61 -> 62; range -> 1al);
# 1am landing: advanced again (62 -> 63; range -> 1am); 1an landing:
# advanced again (63 -> 64; range -> 1an) -- the census-evolution
# class, disclosed each time.
ok = "`cascade_quarter_square.py`" in paper
ok &= "64 scripts cited in place" in paper
ok &= "Theorems 1i–1an" in paper
gate("g12 the footer census (advanced at the 1al-1an landings, "
     "disclosed): this script backticked; 64 cited in place; the "
     "range 1i–1an", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (12 gates)")
print("READING (as swept round 151): the quarter-square unification,")
print("exact.  One scale -- (1/2)^2, the half-shift squared under the")
print("squared-shift map -- organizes five constants (four previously")
print("recorded, the vertex exhibited here -- F1): the strip's vertex")
print("+1/4 in the v-plane, equivalently -1/4 in the height plane,")
print("where the pole's image IS the displacement constant (F4);")
print("xi's pole-cancelling polynomial UP TO 1/2 (F2) = each lattice")
print("kernel's anchor = the squared half-shift minus the")
print("quarter-square, with the denominator factoring exactly over")
print("the adjacent squared layers;")
print("the boundary-read displacement's constant real part -1/4; and")
print("the round-147 detachment threshold, which is EXACTLY 1/4 with")
print("the denominators frozen (the observed 0.24357 = 1/4 minus the")
print("denominator-variation correction 0.00643).  Unification only:")
print("no new RH content in either direction; classical algebra over")
print("the committed lattice; no data, no closures.")
sys.exit(0 if n_fail == 0 else 1)
