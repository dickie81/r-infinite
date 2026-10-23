#!/usr/bin/env python3
"""
The geodesic normalisation computed from the action: m_H/m_W without
the stated identification.

Sources (Check 1): part4b:3276-3320 (V(theta) = a cos^2 theta with
a = 1/chi 'automatic', V''(pi/2) = 1, geodesic map theta = (pi/2) h/v
STATED; Tier-3 caveat 'stated rather than computed from an action'),
part4b:3042-3095 (obstruction factor 1/(2 sqrt(pi)) = chirality x
quarter-turn; g_2 = N(13) unmodified).

THE CANONICAL COMPUTATION.  On the unit S^12 the canonical scalar is
arc length: L = (1/2)(d theta)^2 - a cos^2 theta.  There is no
reparameterisation freedom -- masses are invariant, and the papers'
map theta = (pi/2) h/v rescales the Higgs kinetic slope without
transforming the kinetic term: pi/2 is an artefact of a non-canonical
field redefinition, NOT an action result.  Canonically:

    m_H^2 = V''(pi/2) = 2a           (curvature at the equatorial VEV)
    m_W   = g x (orbit radius)/2 = N(13)/2   (unit equator, g = N(13))
    =>  m_H/m_W = 2 sqrt(2a)/N(13).

The ratio is controlled by the OBSTRUCTION HEIGHT a, not by any
geodesic length.  The papers' a = 1/chi gives 2.93 (dead, and
unclosable: needed shift exceeds the correction family's span).  The
obstruction-algebra candidate a = (1/chi) x 1/(2 sqrt(pi)) -- the
unresolved zero's energy carrying its own obstruction factor, i.e.
V'' = the layer obstruction 1/(2 sqrt(pi)) itself -- gives

    m_H/m_W = sqrt(2) / (pi^(1/4) N(13)) = 1.55750

against the observed 1.55829 +/- 0.00214: -0.4 sigma, ZERO corrections,
16x closer than the geodesic pi/2 (+0.80%, +5.9 sigma before its
underdetermined correction).  Audit pricing: the height was selected
from ~8 obstruction-algebra atoms (only one lands within 1 sigma;
nearest others +/-6%): worth ~3 bits at most until the lemma
'the zero's potential height carries the obstruction factor' is proved.
Falsifiable: the formula needs NO correction member, so HL-LHC-era
m_H (~25 MeV) tests it directly and discriminates it from every
pi/2-plus-correction package.
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
    print(f"observed m_H/m_W = {obs:.5f} +/- {sig:.5f};   N(13) = {n13:.6f}")
    print()
    print("canonical ratio 2 sqrt(2a)/N(13) over obstruction-algebra heights a:")
    cands = [
        ("1/chi           (papers' 'automatic')", 0.5),
        ("1/sqrt(pi)", 1 / SQRTPI),
        ("1/(2 sqrt(pi))", 1 / (2 * SQRTPI)),
        ("1/chi^3", 0.125),
        ("1/(2 pi)", 1 / (2 * math.pi)),
        ("1/pi", 1 / math.pi),
        ("1/(4 pi)", 1 / (4 * math.pi)),
        ("(1/chi) x 1/(2 sqrt(pi))  [zero carries", 1 / (4 * SQRTPI)),
    ]
    for lab, a in cands:
        r = 2 * math.sqrt(2 * a) / n13
        print(f"  a = {lab:<40} -> {r:.5f}  ({(r-obs)/sig:+6.1f} sigma)")
    print("     its own obstruction factor]")
    print()
    a = 1 / (4 * SQRTPI)
    r = math.sqrt(2) / (math.pi ** 0.25 * n13)
    print(f"closed form  m_H/m_W = sqrt(2)/(pi^(1/4) N(13)) = {r:.5f}"
          f"   ({(r-obs)/sig:+.2f} sigma, zero corrections)")
    print(f"equivalently m_H^2 = V'' = 1/(2 sqrt(pi)): the Higgs mass^2 IS")
    print(f"the layer obstruction factor, in cascade units.")
    print(f"prediction:  m_H = {80.377*r:.2f} GeV  (obs 125.25 +/- 0.17)")
    print()
    print(f"papers' geodesic lead pi/2 = {math.pi/2:.5f}"
          f"  ({(math.pi/2-obs)/sig:+.1f} sigma before corrections)")
    print(f"papers' a = 1/chi canonical = {2*math.sqrt(1.0)/n13:.5f} -- dead,")
    print(f"and its needed shift ln({obs:.4f}/{2/n13:.4f}) ="
          f" {math.log(obs*n13/2):+.4f} exceeds the correction family's")
    print(f"span [0.0016, 0.0453]: unclosable, so the height CANNOT be 1/chi")
    print(f"if the family is complete -- an internal forcing argument.")


if __name__ == "__main__":
    main()
