#!/usr/bin/env python3
"""
Proof of the height lemma: m_H^2 = 1/(2 sqrt(pi)) in cascade units.

LEMMA (obstruction height).  On the unit S^12 at the broken Dirac layer
d = 13, the canonically normalised curvature of the obstruction
potential at the vacuum is

    V''_can(pi/2) = 1/(2 sqrt(pi)),

equivalently m_H^2 = 1/(2 sqrt(pi)), a_eff = (1/chi) 1/(2 sqrt(pi)),
and m_H/m_W = sqrt(2)/(pi^(1/4) N(13)) = 1.55759.

PROOF (at the papers' Tier-2 structural rigour; sources cited).

Step 1 [papers, part4b:3296-3320].  Bare potential V(theta) =
(1/chi) cos^2 theta: the cos^2 shape is the even-sphere obstruction
form, the 1/chi height is the chirality-basin share.  Bare curvature
V''(pi/2) = 2/chi = 1.

Step 2 [papers, part4b:1512-1521, the open/closed-leg duality].  The
Higgs fluctuation h about the vacuum is an OPEN LINE terminating on
the obstruction zero -- not a closed cycle.  The papers' universal leg
rule at a Dirac layer: open-line factor = (1/sqrt(pi)) x (1/chi)
= 1/(2 sqrt(pi)) -- 'the propagator filters through the obstruction;
per-leg factor in the denominator (selection).'  (That chi-factors
apply to non-spinor observables is the papers' own standing practice:
the alpha(d*)/chi^k family corrects Omega_m and ell_A.)

Step 3 [the one residual axiom: single crossing].  The mass term
(1/2) m^2 h^2 records ONE open-line filtering event -- the fluctuation
propagator crosses the obstruction once:

    m_H^2 = V''_bare x 1/(2 sqrt(pi)) = 1/(2 sqrt(pi)).

Anchors: (i) the per-observable single-attachment rule the b/s data
selected at 2 sigma (Addendum 13: filters attach once, at the
observable); (ii) the papers' per-layer fermion mass follows the same
pattern -- m(d) = R(d) x (1/chi), one sector factor at amplitude
level; (iii) every alternative counting is numerically excluded, nearest by ~240 sigma (table below).

Step 4 [papers, part4b:3042-3095].  m_W = g x (unit equatorial
orbit)/2 = N(13)/2, with g_2 = N(13) unmodified.  Hence

    m_H/m_W = 2 sqrt(1/(2 sqrt(pi)))/N(13) = sqrt(2)/(pi^(1/4) N(13)).
                                                                   QED
Status: Steps 1, 2, 4 are published cascade machinery cited at source;
Step 3 is the named axiom, triply anchored, alternatives dead by ~240 sigma.  Same epistemic grade as the papers' own Tier-2
structural groundings (e.g. the Adams pairing, the kinetic-prefactor
normalisation).  Bonus pattern: the papers' per-layer identity
m(d)^2 = alpha(d) ('mass^2 = the mode's structural factor') extends:
the Higgs's structural factor is the obstruction factor itself.
"""

import math

SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def N(d):
    return SQRTPI * R(d)


def main():
    obs = 125.25 / 80.377
    sig = obs * math.hypot(0.17 / 125.25, 0.012 / 80.377)
    n13 = N(13)

    print("=" * 74)
    print("Step 3 stress test: all enumerable crossing-countings")
    print("=" * 74)
    countings = [
        ("0 crossings (bare V'' = 1)", 1.0),
        ("half crossing  (1/(2 sqrt(pi)))^(1/2)", (1 / (2 * SQRTPI)) ** 0.5),
        ("chirality only (1/chi)", 0.5),
        ("quarter-turn only (1/sqrt(pi))", 1 / SQRTPI),
        ("ONE full crossing 1/(2 sqrt(pi))  [lemma]", 1 / (2 * SQRTPI)),
        ("two crossings (1/(2 sqrt(pi)))^2", 1 / (4 * math.pi)),
    ]
    for lab, vpp in countings:
        ratio = 2 * math.sqrt(vpp) / n13
        print(f"  V'' = {lab:<42} -> {ratio:.5f}"
              f"  ({(ratio-obs)/sig:+7.1f} sigma)")
    print("  => the single-full-crossing counting stands alone; nearest")
    print("     alternative dead by ~240 sigma.")

    print()
    print("=" * 74)
    print("Consistency with the papers' fermion-mass pattern")
    print("=" * 74)
    print("  per-layer fermion: m(d) = R(d)/chi -> m^2 = alpha(d): one")
    print("  sector factor (chirality) attached once at amplitude level.")
    print("  Higgs: m_H^2 = 1 x [open-line factor]: one sector factor")
    print("  (full obstruction) attached once at probability level --")
    print("  the same single-attachment rule, sector-appropriate factor.")

    print()
    print("=" * 74)
    print("The lemma's numbers")
    print("=" * 74)
    r = math.sqrt(2) / (math.pi ** 0.25 * n13)
    print(f"  m_H/m_W = sqrt(2)/(pi^(1/4) N(13)) = {r:.5f}")
    print(f"  observed {obs:.5f} +/- {sig:.5f}   -> {(r-obs)/sig:+.2f} sigma,")
    print(f"  zero corrections;  m_H = {80.377*r:.2f} GeV (obs 125.25(17))")
    lam_ratio = (r / (math.pi / 2)) ** 2
    print(f"  Higgs-quartic corollary: lambda rescales by (ratio/(pi/2))^2 ="
          f" {lam_ratio:.4f}")


if __name__ == "__main__":
    main()
