#!/usr/bin/env python3
"""
THEOREM 1ap -- the concentration regrade: the resolution wall
refuted, the contrast wall named.

THE COMMISSION AND THE INVERSION.  The owner commissioned Push A --
prove the width floor for every admissible committed instance.  The
attempt refuted it (self-caught; the 1aj-regrade precedent): the
floor fails, and fails to ZERO.

P1 (the concentration construction).  On the committed lattice take
three sites (d = 4, 5, 6) and give the numerator a
complex-conjugate zero pair ON the displaced curve at height
gamma_0: q(u) = ((u - x0)^2 + y0^2)/Q(u), x0 = gamma_0^2 - 1/4,
y0 = gamma_0.  The instance is STRICTLY admissible -- L > 0
everywhere, the cone's interior, no tangency -- yet its boundary
read is negative on a window of width ~ 5/(2 gamma_0) ending at
gamma_0.  Gated at heights gamma_1/50/100/300: widths
0.1510/0.0493/0.0249/0.0083, width*gamma_0 rising to 2.4991 ~ 5/2
(equivalently constant u-plane width ~ 5.0 -- observed, not
derived).  The infimum of window widths over the admissible cone is
ZERO: the committed family concentrates arbitrarily at height.

P2 (the contrast law).  The price is depth: the negativity depth
collapses like gamma_0^-6 for the fixed three-site denominator
(measured exponents 5.5/5.9/6.0 -- |Q| ~ gamma_0^6 along the curve;
observed, not derived) -- 3.7e-7 at gamma_1 down to 8.5e-15 at
height 300.  Resolution is purchasable; contrast pays.

P3 (stacking anti-concentrates).  Two on-curve pairs at spacing eps
give width ~ 2.075 INDEPENDENT of eps (gated at eps = 0.5..0.01) --
wider than one pair.  The concentration mechanism is height, not
numerator degree.

THE REGRADE.  The 1an W4 flat clauses ("it cannot concentrate";
"relocation without resolution"; "the RH deficit is RESOLUTION, not
reach") are struck at their carriers, false-when-written beyond the
sampled family; the sampled qualifiers the hostile rounds enforced
scope the damage exactly.  What stands: the forcing clause (nothing
cascade-side forces positivity; the dense-class extension is RH,
claimed in neither direction) and the sampled aimed family's own
phenomenology.  The deficit's honest coordinate regrades to
CONTRAST; whether a nonzero contrast-normalized floor exists is the
NEW NAMED OPEN QUESTION.  1ao's wall-sidestep carries its net-state
marker (the sidestep rests on the decay-rate exclusion, untouched).

HONEST SCOPE.  Category (a) -- pure geometry of the committed
kernels; no data, no closures, no new physics; the 5/2 and
gamma_0^-6 constants observed with gated brackets, not derived; the
three-site denominator is the gated scope; positivity unchanged.
Check 7 clean (rational-function geometry; no semiclassics);
Check 8 clean (no hypothesis input).

VERIFICATION (12 gates, exit-gated).
  V1 -- g1 strict admissibility EXACT (P = (u-x0)^2 + y0^2 >= y0^2
       > 0 identically -- exact rationals at all four heights; the
       numerical L-minimum positive); g2 the delta-ladder at
       gamma_1 (widths bracketed inward, monotone decreasing);
       g3 the limit instance (F(gamma_0) = 0 exactly by
       construction; window width and depth bracketed).
  V2 -- g4 the height ladder (four widths bracketed; width*gamma_0
       increasing with the last in (2.498, 2.500) -- the observed
       5/2); g5 the contrast ladder (three ratio-exponents
       bracketed, rising toward 6); g6 the anti-concentration (two
       pairs: four widths in (2.07, 2.14), the last three within
       0.01 -- eps-independence); g7 the infimum-zero chain
       (width(300) < 0.01 < width(100) < ... < width(gamma_1) < 1).
  V3 -- g8 the regrade strikes anchored on the paper (the 1ap
       strike-frame counts exactly 2 + 2; "honest name is
       CONTRAST"; the 1an honest-scope net-state; the 1ao sidestep
       marker); g9 1ap's key sentences anchored; g10 the
       honest-scope anchors (the gated-scope clause; "wall stands
       where it stood" count >= 2 -- the forcing clause survives on
       both carriers); g11 the sibling chain green
       (unit_ball_rh 13/0, transitively chaining windows_overlap,
       riemann_selection, type_counting, and the two Weil-arc
       siblings); g12 the footer census (this script backticked;
       "66 scripts cited in place"; "Theorems 1i-1ap").

Sabotage record (full-tree scratchpad copy, tar --exclude=.git,
serial, abort-on-mangle-failure, at the landing; actual censuses):
(a) the CONTRAST strike-frame content mangled in the paper copy
(CONTRAST -> PRECISION) -> TWO gates trip: g8 directly AND g11
through the sibling chain (windows_overlap's g10 cross-anchors the
same content), 10/2, exit 1; (b) the curve displacement flipped in
the verifier copy (-0.25 -> -0.30 in curve()) -> g2 trips ALONE,
11/1, exit 1 -- an instructive coupling census: the curve-relative
constructions (g3/g4, zeros placed ON the flipped curve) stay
self-consistent, while g2's delta-ladder builds its pair from the
explicit 1/4 literal and catches the disagreement between the two
arms; (c) the limit instance knocked off the curve in the copy
(y0 -> gamma_1 - 0.5) -> g3 trips (F(gamma_0) != 0; width 0.3047
outside the bracket), 11/1, exit 1.  Clean baselines 12/0 exit 0
before and after every entry.  Also disclosed: the first clean run
failed 11/1 at g8's own marker count (the gate expected one
net-state marker where the paper correctly carries two) --
corrected to the true census in the gate text.  Twelve gates
(count checked against the gate() census pre-commit).
"""
import os
import subprocess
import sys
from fractions import Fraction as Fr

import numpy as np
from scipy.optimize import brentq

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


W2 = [4.5 ** 2, 5.5 ** 2, 6.5 ** 2]          # committed d = 4, 5, 6


def Q(u):
    return (u + W2[0]) * (u + W2[1]) * (u + W2[2])


def curve(g):
    return g * g - 0.25 + 1j * g


G1 = 14.134725
HEIGHTS = (G1, 50.0, 100.0, 300.0)


def make_F(z):
    zc = np.conj(z)
    return lambda g: (((curve(g) - z) * (curve(g) - zc)) / Q(curve(g))).real


def window(z, glo, ghi):
    F = make_F(z)
    gg = np.linspace(glo, ghi, 500001)
    Fv = np.array([F(g) for g in gg])
    ng = gg[Fv < 0]
    lo = brentq(F, ng.min() - 0.005, ng.min() + 0.0005)
    hi = brentq(F, ng.max() - 0.0005, ng.max() + 0.005)
    depth = min(F(g) for g in np.linspace(lo, hi, 60001))
    return lo, hi, depth


print("V1 -- P1: the construction, strict admissibility, the limit instance")
ok = True
for gz in HEIGHTS:
    # exact rationals: P(u) = (u - x0)^2 + y0^2 >= y0^2 > 0 identically
    x0 = Fr(gz).limit_denominator(10 ** 9) ** 2 - Fr(1, 4)
    y0 = Fr(gz).limit_denominator(10 ** 9)
    ok &= y0 * y0 > 0
    for uf in (Fr(0), x0, 2 * x0 + 7):
        ok &= (uf - x0) ** 2 + y0 * y0 >= y0 * y0
gg = np.linspace(0, 400, 400001)
z = curve(G1)
Lv = np.array([(((g * g - z) * (g * g - np.conj(z))) / Q(g * g + 0j)).real
               for g in gg])
ok &= Lv.min() > 0
gate("g1 strict admissibility EXACT: P = (u-x0)^2 + y0^2 >= y0^2 > 0 "
     "identically (exact rationals, four heights); the numerical "
     "L-minimum strictly positive (the cone's INTERIOR -- no "
     "tangency)", ok, f"L_min {Lv.min():.2e}")

DELTAS = (1.0, 0.3, 0.1, 0.03, 0.01)
DW = [(0.4004, 0.4005), (0.2552, 0.2553), (0.1924, 0.1925),
      (0.1646, 0.1647), (0.1557, 0.1558)]
ok = True
prev = None
for delta, (blo, bhi) in zip(DELTAS, DW):
    zd = complex(G1 ** 2 - 0.25, G1 - delta)
    lo, hi, _ = window(zd, G1 - 3, G1 + 2)
    w = hi - lo
    ok &= blo < w < bhi
    if prev is not None:
        ok &= w < prev
    prev = w
gate("g2 the delta-ladder at gamma_1: five widths bracketed inward "
     "(0.4004..0.1557), strictly decreasing as the pair approaches "
     "the curve", ok)

z0 = curve(G1)
F0 = make_F(z0)
lo, hi, depth = window(z0, G1 - 3, G1 + 1)
ok = abs(F0(G1)) < 1e-15                    # exact zero by construction
ok &= 0.1510 < hi - lo < 0.1512
ok &= -3.8e-7 < depth < -3.7e-7
ok &= abs(hi - G1) < 1e-6                   # the window ends AT gamma_0
gate("g3 the limit instance (the pair ON the curve): F(gamma_0) = 0 "
     "exactly; window width in (0.1510, 0.1512) ending at gamma_0; "
     "depth in (-3.8e-7, -3.7e-7)",
     ok, f"width {hi-lo:.6f} depth {depth:.2e}")

print("V2 -- P1/P2/P3: the height ladder, the contrast law, anti-concentration")
HW = [(0.1510, 0.1512), (0.0493, 0.0494), (0.0249, 0.0250),
      (0.00832, 0.00834)]
widths, depths = [], []
ok = True
for gz, (blo, bhi) in zip(HEIGHTS, HW):
    lo, hi, depth = window(curve(gz), max(0.1, gz - 3), gz + 1)
    widths.append(hi - lo)
    depths.append(depth)
    ok &= blo < hi - lo < bhi
prods = [w * g for w, g in zip(widths, HEIGHTS)]
ok &= prods[0] < prods[1] < prods[2] < prods[3]
ok &= 2.498 < prods[3] < 2.500
gate("g4 the height ladder: four widths bracketed inward; "
     "width*gamma_0 strictly increasing with the last in "
     "(2.498, 2.500) -- the observed 5/2 law",
     ok, f"products {[f'{p:.4f}' for p in prods]}")

import math
exps = []
for i in range(3):
    r = depths[i] / depths[i + 1]
    h = HEIGHTS[i + 1] / HEIGHTS[i]
    exps.append(math.log(r) / math.log(h))
ok = 5.4 < exps[0] < 5.5 and 5.9 < exps[1] < 6.0 and 5.95 < exps[2] < 6.05
gate("g5 the contrast law: ratio-exponents along the height ladder "
     "in (5.4, 5.5)/(5.9, 6.0)/(5.95, 6.05), rising toward the "
     "gamma_0^-6 scale of |Q| along the curve",
     ok, f"exponents {[f'{e:.2f}' for e in exps]}")

EPS = (0.5, 0.2, 0.05, 0.01)
tw = []
for eps in EPS:
    z1, z2 = curve(G1), curve(G1 + eps)

    def F2(g, z1=z1, z2=z2):
        u = curve(g)
        P = (u - z1) * (u - np.conj(z1)) * (u - z2) * (u - np.conj(z2))
        W5 = W2 + [7.5 ** 2, 8.5 ** 2]
        Qv = 1.0 + 0j
        for w2 in W5:
            Qv = Qv * (u + w2)
        return (P / Qv).real
    gg = np.linspace(G1 - 4, G1 + 4, 400001)
    Fv = np.array([F2(g) for g in gg])
    ng = gg[Fv < 0]
    lo = brentq(F2, ng.min() - 0.005, ng.min() + 0.0005)
    hi = brentq(F2, ng.max() - 0.0005, ng.max() + 0.005)
    tw.append(hi - lo)
ok = all(2.07 < w < 2.14 for w in tw)
ok &= max(tw[1:]) - min(tw[1:]) < 0.01
gate("g6 anti-concentration: two on-curve pairs (five-site "
     "denominator), four widths in (2.07, 2.14) with the last three "
     "within 0.01 -- eps-INDEPENDENT; stacking widens, it does not "
     "narrow", ok, f"widths {[f'{w:.4f}' for w in tw]}")

ok = widths[3] < 0.01 < widths[2] < widths[1] < widths[0] < 1
gate("g7 the infimum-zero chain: width(300) < 0.01 < width(100) < "
     "width(50) < width(gamma_1) < 1 -- the floor fails, and fails "
     "toward zero", ok)

print("V3 -- the paper: the regrade strikes, key sentences, siblings, footer")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = paper.count("struck at the Theorem 1ap regrade") == 2
ok &= paper.count("struck at the 1ap regrade") == 2
ok &= "honest name is CONTRAST" in paper
ok &= ("beyond the sample the floor fails entirely, and to zero"
       in paper)
# two 1ap net-state markers: the 1an honest-scope marker AND the 1ao
# sidestep marker (the first gate draft expected 1 and failed its own
# clean run 11/1 -- corrected to the true census, disclosed).
ok &= paper.count("net-state, Theorem 1ap") == 2
gate("g8 the regrade strikes anchored: the 1ap strike frames exactly "
     "2 + 2; the CONTRAST regrade content; the TWO net-state markers "
     "(the 1an honest-scope; the 1ao sidestep) -- count corrected "
     "from the clean-run failure, disclosed",
     ok, f"frames {paper.count('struck at the Theorem 1ap regrade')}+"
         f"{paper.count('struck at the 1ap regrade')}")

ok = ("The infimum of window widths over the admissible cone is ZERO"
      in paper)
ok &= "Resolution is purchasable; contrast pays for it" in paper
ok &= "The concentration mechanism is height, not degree" in paper
ok &= "the NEW NAMED OPEN QUESTION, replacing the refuted conjecture" in paper
gate("g9 1ap's key sentences anchored by content (the infimum-zero "
     "claim; the contrast law; the height mechanism; the new open "
     "question)", ok)

ok = "the three-site denominator is the gated scope" in paper
ok &= paper.count("wall stands where it stood") >= 2
gate("g10 the honest-scope anchors: the gated-scope clause; the "
     "forcing clause surviving on both carriers (count >= 2)",
     ok, f"wall count {paper.count('wall stands where it stood')}")

rr = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_unit_ball_rh.py")],
                    capture_output=True, text=True)
ok = rr.returncode == 0 and "13 pass / 0 fail" in rr.stdout
gate("g11 the sibling chain green after the census advance "
     "(unit_ball_rh 13/0, transitively chaining windows_overlap, "
     "riemann_selection, type_counting, and the two Weil-arc "
     "siblings)", ok)

ok = "`cascade_concentration_regrade.py`" in paper
ok &= "66 scripts cited in place" in paper
ok &= "Theorems 1i–1ap" in paper
gate("g12 the footer census (advanced at this landing, disclosed): "
     "this script backticked; 66 cited in place; the range 1i–1ap", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (12 gates)")
print("READING: the concentration regrade.  Push A inverted: the width")
print("floor is refuted, and to ZERO -- a strictly admissible")
print("complex-pair instance (the cone's interior, no tangency)")
print("concentrates with width ~ 5/(2 gamma_0) ending at its height,")
print("the 5/2 observed not derived.  The price is CONTRAST: depth")
print("collapses like gamma_0^-6 (the fixed denominator's growth).")
print("Stacking pairs anti-concentrates (width ~ 2.075,")
print("eps-independent): the mechanism is height, not degree.  The")
print("1an W4 flat clauses are struck at their carriers,")
print("false-when-written beyond the sampled family -- the sampled")
print("qualifiers the rounds enforced scope the damage exactly -- and")
print("the forcing clause stands unchanged: nothing cascade-side")
print("forces positivity; the dense-class extension is RH, claimed in")
print("neither direction.  The deficit's honest coordinate is")
print("CONTRAST; whether a nonzero contrast-normalized floor exists")
print("is the new named open question.  No data, no closures, no new")
print("physics; no direction of explanation.")
sys.exit(0 if n_fail == 0 else 1)
