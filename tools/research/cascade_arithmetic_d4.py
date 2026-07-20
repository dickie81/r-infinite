#!/usr/bin/env python3
"""
d = 4 FROM ARITHMETIC: what the tower pins, what it cannot select.

The papers select d = 4 by Lovelock (external tensor theorem) plus
two consistency prongs (part3 sec. 3, 9; read directly).  Question:
how much of '4' exists in the arithmetic frame (T1-T9) alone?

P1 (The half-period class).  The Weil index gamma = zeta_8 (T6-P1)
   makes the twist tower Z/8-graded.  The set {k : gamma^k real} =
   {0, 4}: residue 4 is the UNIQUE nontrivial real class, and
   gamma^4 = -1 -- the generator of mu(R), the torsion unit chi's
   nontrivial element (T5-P1).  Arithmetic statement: the observer
   residue is the torsion twist of the vacuum residue -- the only
   place the metaplectic phase returns to the real axis.

P2 (Scalar-flatness -- DEMOTED to Wick/lapse-conditional cross-check
   per review 3: the identity contains no arithmetic object -- no
   Gamma_R, zeta, or Weil index enters -- and the induced (round-
   sphere) metric is NEVER scalar-flat; only the unit-lapse reading
   gives
        R^(n) * a^4 = (n-1)(n-4),
   verified numerically below by finite differences: the tower's
   own measure is scalar-flat UNIQUELY at n = 4.  Everything in the
   identity is a T1 object; the calculus is neutral; the Lorentzian
   READING of it inherits the Wick step (instantiation).

P3 (DEMOTED per review 2 -- the feature->layer map is a convention;
   kept as historical record).  The features of
   Gamma_R (T5/A32, all simple) are ordered: volume 5.2569 < area
   7.2569 < threshold 20.73 < threshold 218.6.  The FIRST feature is
   the volume critical point; the last integer twist below it is 5
   (the host, the papers' d_V); the twist on its boundary is 4.
   Arithmetic pins the pair (5, 4) as (first-feature floor, its
   boundary); that the OBSERVER sits there is the hypothesis
   (Check 8 -- not derivable, not claimed).

P4 VERDICT (amended, reviews 2-3): ONE convention-free arithmetic
   distinction (P1, whose observer-link is a labeling); P2 is a
   conditional cross-check; P3 demoted.  Selection requires Lovelock
   or C1.
"""

import cmath
import math

from scipy.optimize import brentq
from scipy.special import digamma

PI = math.pi


def P(s):
    return 0.5 * digamma(s / 2.0) - 0.5 * math.log(PI)


def p1():
    print("=" * 74)
    print("P1: residue 4 is the unique nontrivial real class of the")
    print("    metaplectic cycle, and gamma^4 = -1 = the torsion unit")
    print("=" * 74)
    g = cmath.exp(1j * PI / 4)
    real_ks = [k for k in range(8) if abs((g ** k).imag) < 1e-12]
    print(f"  {{k mod 8 : gamma^k real}} = {real_ks};"
          f"  gamma^4 = {(g**4).real:+.0f} = the generator of mu(R)")
    print("  => four twist steps carry the vacuum class onto the other")
    print("     real unit: the observer residue = chi-twist of the vacuum.")


def p2():
    print()
    print("=" * 74)
    print("P2: the tower's slicing measure is scalar-flat uniquely at n = 4")
    print("=" * 74)
    t, h = 0.3, 1e-5

    def a(tt):
        return math.sqrt(1 - tt * tt)

    ad = (a(t + h) - a(t - h)) / (2 * h)
    add = (a(t + h) - 2 * a(t) + a(t - h)) / h ** 2
    print(f"  {'n':>3} {'R*a^4 (numeric)':>17} {'(n-1)(n-4)':>12}")
    for n in range(3, 9):
        Rn = 2 * (n - 1) * add / a(t) \
            + (n - 1) * (n - 2) * (ad ** 2 + 1) / a(t) ** 2
        print(f"  {n:>3} {Rn * a(t)**4:>17.6f} {(n-1)*(n-4):>12}")
    print("  => R vanishes iff n = 4: the unit ball's own geometry solves")
    print("     the vacuum equation only there.  (Identity in T1 objects;")
    print("     Lorentzian reading inherits the Wick step.)")


def p3():
    print()
    print("=" * 74)
    print("P3: the first feature of Gamma_R and its boundary twist")
    print("=" * 74)
    sV = brentq(lambda s: -1.0 / s - P(s), 2.1, 20.0)
    s0 = brentq(P, 2.1, 20.0)
    t1 = brentq(lambda s: P(s) - 0.5 * math.log(PI), 10, 40)
    t2 = brentq(lambda s: P(s) - math.sqrt(PI), 100, 400)
    feats = sorted([sV, s0, t1, t2])
    print(f"  features (ordered): {['%.4f' % f for f in feats]}")
    print(f"  FIRST feature: volume critical point s_V = {sV:.4f}")
    print(f"  last integer twist below it: {math.floor(sV)} (the host d_V)")
    print(f"  its boundary twist: {math.floor(sV) - 1} = 4"
          f"   (S^3 = boundary of the 5-ball's slicing)")
    print("  => [DEMOTED, review 2: this comparison mixes s- and d-space;")
    print("     the threshold convention applied here gives (4, 3).  The")
    print("     feature->layer map is a convention -- residue item seven.]")


if __name__ == "__main__":
    p1()
    p2()
    p3()
    print()
    print("=" * 74)
    print("P4 VERDICT (amended per reviews 2-3): ONE convention-free")
    print("arithmetic distinction (the torsion half-period, P1 -- though its")
    print("observer-link is a labeling); the scalar-flatness identity (P2) is")
    print("a Wick/lapse-conditional calculus cross-check containing no")
    print("arithmetic; the feature-boundary pinning (P3) is DEMOTED -- the")
    print("feature->layer map is a convention (review 2).  Selection still")
    print("requires physics (Lovelock) or C1.  The address is distinguished")
    print("in the arithmetic; occupying it is the hypothesis.")
    print("=" * 74)
