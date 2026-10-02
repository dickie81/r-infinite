#!/usr/bin/env python3
"""
THE PER-PERIOD ATTACHMENT RULE FROM ARITHMETIC -- what is forced,
what is not.

A29 (amended) used exponents (E^0, E^1, E^2) at twists (21, 13, 5)
and admitted they were reverse-engineered.  This script derives what
CAN be derived from the arithmetic of the real place alone, and draws
the boundary at what cannot, in the style of Addendum 33 (T5).

P1 (The period is the order of the Weil index) [ARITHMETIC].
   The quadratic character of the real place has Weil index
   gamma = int e^(i pi x^2) dx = e^(i pi/4) = zeta_8
   (Fresnel; Weil, 'Sur certains groupes d'operateurs unitaires').
   gamma has ORDER 8: the twist tower carries a canonical Z/8
   grading -- the arithmetic avatar of Bott/Clifford periodicity,
   obtained without topology.  Verified numerically below via
   Fresnel integrals.

P2 (The threshold) [ARITHMETIC -- T5/A32].  P(s) = (log Gamma_R)'(s)
   = E_{mu_s}[log|x|] is strictly increasing (variance positivity)
   and crosses ln Gamma(1/2) exactly once, transversally, at
   s = 20.731 (twist layer d_1 = 19 = last marked-relevant layer
   below).  Subcritical region: P(d+1) < ln Gamma(1/2).

P3 (The forced counting) [ARITHMETIC, conditional on the marking].
   Given the marked coset C = {d = 5 mod 8} of the Z/8 grading
   (WHICH coset is marked is instantiation data -- see P5), the
   subcritical marked set is FORCED and FINITE:
       {d in C : P(d+1) < ln Gamma(1/2)} = {5, 13}   exactly.
   For a descent functional at twist d with source above, the member
   exponent is the count of subcritical marked twists in its window:
       n(21) = 0,  n(13) = 1,  n(5) = 2.
   Each contributes at FIRST power (a lattice point has multiplicity
   one in Z; each lies in the window at most once by total order --
   T5's attach-once).  THE EXPONENT PATTERN (0, 1, 2) IS FORCED
   COUNTING, NOT FITTING.  The A29 amendment's reverse-engineering
   charge now falls entirely on the VALUE of E, not the exponents.

P4 (Stability of the counting).  The set {5, 13} sits at finite
   margins from the threshold (membership cannot flip under any
   reinterpretation smaller than the margins); computed below.

P5 (What arithmetic does NOT supply) [the honest boundary].
   (a) WHICH Z/8 coset is marked (the Dirac coset d = 5 mod 8):
       instantiation data, exactly parallel to T5's occupancy
       assignment.  (b) WHY subcritical marked twists activate as
       member sources (the activation joint; the papers' own
       activation profile, part4a thm:generations, is the physical
       statement).  (c) THE VALUE E = N_c pi^2: imports the gauge
       count (2-adic Radon-Hurwitz, located by instantiation) and a
       Gamma(1/2)^4 whose multiplicity-4 lacks a derivation; its
       grammar twin 2 pi e sqrt(3) is 0.1% away and undiscriminated.
       The value REMAINS A FIT per the A29 amendment.
   Status: gap #2 SPLITS -- shape derived (this file), value open.
"""

import math

from scipy.special import digamma, fresnel

LNPI = math.log(math.pi)
LN_GHALF = 0.5 * LNPI                    # ln Gamma(1/2) = ln sqrt(pi)


def P(s):
    return 0.5 * digamma(s / 2.0) - 0.5 * LNPI


def p1():
    print("=" * 74)
    print("P1: the Weil index of the real quadratic character has order 8")
    print("=" * 74)
    # int_{-inf}^{inf} e^{i pi x^2} dx via Fresnel: substitute x = u/sqrt(2)
    S, C = fresnel(1e8)                   # S(inf) = C(inf) = 1/2
    re = 2 * C / math.sqrt(2)
    im = 2 * S / math.sqrt(2)
    gamma = complex(re, im)
    print(f"  gamma = int e^(i pi x^2) dx = {re:.6f} + {im:.6f} i")
    print(f"  e^(i pi/4)                  = {math.cos(math.pi/4):.6f}"
          f" + {math.sin(math.pi/4):.6f} i   |gamma| = {abs(gamma):.6f}")
    orders = [k for k in range(1, 9) if abs(gamma ** k - 1) < 1e-6]
    print(f"  smallest k with gamma^k = 1: {orders[0] if orders else '>8'}"
          f"   (gamma^4 = {gamma**4:.4f} = -1)")
    print("  => the twist tower carries a canonical Z/8 grading: the")
    print("     arithmetic Bott period, from Fresnel, no topology.")


def p2p3():
    print()
    print("=" * 74)
    print("P2+P3: threshold, subcritical marked set, forced counting")
    print("=" * 74)
    print(f"  threshold: P(s) = ln Gamma(1/2) = {LN_GHALF:.4f},"
          f" crossed once (P' = Var > 0)")
    print(f"  marked coset C = {{d = 5 mod 8}} (instantiation -- P5):")
    marked = [5, 13, 21, 29, 37, 45]
    sub = []
    for d in marked:
        val = P(d + 1)
        flag = "SUBCRITICAL" if val < LN_GHALF else "supercritical"
        if val < LN_GHALF:
            sub.append(d)
        print(f"    d = {d:>2}: P(d+1) = {val:+.4f}   {flag}"
              f"   margin {abs(val-LN_GHALF):.4f}")
    print(f"  subcritical marked set = {sub}  (forced, finite, exact)")
    print()
    print("  member exponents = count of subcritical marked twists in the")
    print("  descent window [d, 29]:")
    for d in (21, 13, 5):
        n = len([m for m in sub if d <= m <= 29])
        print(f"    twist d = {d:>2}:  n(d) = {n}")
    print("  => (E^0, E^1, E^2) at (21, 13, 5): FORCED COUNTING.")
    print("     First power each: lattice points have multiplicity one;")
    print("     window contains each at most once (T5 attach-once).")


def p4():
    print()
    print("=" * 74)
    print("P4: stability -- membership margins of the forced set")
    print("=" * 74)
    for d, side in [(13, "in"), (21, "out")]:
        m = abs(P(d + 1) - LN_GHALF)
        print(f"  d = {d:>2} ({side:>3}): margin |P - ln G(1/2)| = {m:.4f}"
              f"   ({m/LN_GHALF*100:.1f}% of the threshold value)")
    print("  => the counting cannot flip under any perturbation smaller")
    print("     than these margins; the exponent pattern is rigid.")


def p5():
    print()
    print("=" * 74)
    print("P5: the honest boundary")
    print("=" * 74)
    print("  DERIVED (arithmetic): the Z/8 grading (Weil index order);")
    print("  the unique transversal threshold; the finite forced set")
    print("  {5, 13}; the exponent pattern (0, 1, 2); first power each.")
    print("  NOT DERIVED: which coset is marked (instantiation, parallel")
    print("  to T5's occupancy); the activation joint (why subcritical")
    print("  marked twists source members); the VALUE E = N_c pi^2 --")
    print("  still a fit with an undiscriminated 0.1% grammar twin.")
    print("  Gap #2 of the formulation SPLITS: shape -> theorem T6;")
    print("  value -> remains with C1 and the A29 amendment.")


if __name__ == "__main__":
    p1()
    p2p3()
    p4()
    p5()
