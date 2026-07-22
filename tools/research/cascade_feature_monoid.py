#!/usr/bin/env python3
"""
FINDING 6: REOPENED.  This script's original verdict (that the
feature list is complete because Q has one archimedean place) FAILED
hostile re-review, and this file now records the failure honestly.

WHAT HOLDS (verified below, ~4e-16):
  (i)  s Gamma_R(s) = 2 pi Gamma_R(s+2)   (even-shift recursion)
  (ii) Gamma_R(s) Gamma_R(s+1) = Gamma_C(s) = 2 (2pi)^(-s) Gamma(s)
       (Legendre) -- the pure odd shift requires the L-factor of a
       complex place, and Q has r_2 = 0.

WHAT FAILED (re-review Findings 1-2):
  1. CONVENTION INCONSISTENCY.  The paper's twist convention is
     s = d + 1 (local factor Gamma_R(d+1)); threshold addresses use
     it correctly (s* = 20.73 -> d_1 = 19).  But the framework's
     volume feature lives in d-space: V(d) = pi^(d/2)/Gamma(d/2+1)
     has its maximum at d = 5.2569 (host layer 5) -- and
     V(d) = 1/(pi Gamma_R(d+2)) = 1/(pi Gamma_R(s+1)): in the twist
     variable the volume feature sits at s = 6.2569 WITH FACTOR
     Gamma_R(s+1), exactly the object the original verdict excluded.
     The s = 5.2569 object this script originally kept (crit of
     Gamma_R(s+2)) pins (host, boundary) = (4, 3) under the
     threshold convention -- breaking the observer pinning instead
     of saving it.  There is no single stated feature->layer rule
     producing {5, 7, 19, 217}; part0 itself concedes 'No rounding
     convention selects a canonical integer uniformly across the
     three boundaries' (part0.tex:1178-1180).
  2. COMPLETENESS FALSE ON ITS OWN TERMS.  The monoid
     <s, s-1, Gamma_R, zeta> also contains (s-1) Gamma_R(s), whose
     critical points (s = 2.373, 4.505 -- computed below) appear in
     no feature list; and the pole-free grouping (1/2)s(s-1)Gamma_R
     has NO critical point for s > 1.  The 'critical pair' requires
     using two different regroupings simultaneously, with no rule.

STATUS: the r_2 = 0 identity is a genuine partial obstruction (the
pure +1 shift is not in the monoid), but it does not answer review
Finding 6.  The feature->integer-layer selection convention is a
NON-ARITHMETIC RESIDUE ITEM (the seventh); after review 3 the
observer's address retains ONE convention-free distinction
(gamma^4 = -1); the scalar-flatness cross-check was also demoted.

NET-STATE (Theorem 1k, cascade_lattice_selection.py, round 60):
the part0 concession quoted in FAILED-1 is verbatim-true, but its
next sentence in the source defines the variational selection
(thm:variational: sup over the eight labelings, unique at
(7,19,217), in part0 since 2026-05), and part0's regime partition
is the lattice-band statement.  Given the site-E anchored pairing
the feature->layer assignment is lattice-entailed -- the 5.2569
double-reading in FAILED-1 is one equation psi(x/2) = ln pi read
at two argument offsets, not two conflicting conventions.  The
residue member is re-motivated, not deleted; Finding 6's
completeness question stays REOPENED and this file's failure
record stands unrevised.
"""

import math

from scipy.optimize import brentq
from scipy.special import digamma

PI = math.pi
LNPI = math.log(PI)


def gamma_R(s):
    return PI ** (-s / 2) * math.gamma(s / 2)


def P(s):
    return 0.5 * digamma(s / 2.0) - 0.5 * LNPI


def main():
    print("=" * 74)
    print("What holds: the two identities")
    print("=" * 74)
    w1 = max(abs(s * gamma_R(s) / (2 * PI * gamma_R(s + 2)) - 1)
             for s in (1.5, 4.0, 6.2569, 13.0))
    w2 = max(abs(gamma_R(s) * gamma_R(s + 1)
                 / (2 * (2 * PI) ** (-s) * math.gamma(s)) - 1)
             for s in (1.5, 4.0, 6.2569, 13.0))
    print(f"  s G_R(s) = 2pi G_R(s+2): {w1:.2e};   G_R(s)G_R(s+1) ="
          f" Gamma_C(s): {w2:.2e}")

    print()
    print("=" * 74)
    print("What failed 1: the convention inconsistency")
    print("=" * 74)
    dV = brentq(lambda d: 0.5 * LNPI - 0.5 * digamma(d / 2 + 1), 2, 12)
    print(f"  V(d) max at d = {dV:.4f} -> integer host 5 (d-space)")
    print(f"  in twist variable s = d+1: s = {dV+1:.4f}, and V(d) ="
          f" 1/(pi Gamma_R(s+1))")
    s_odd = brentq(lambda s: P(s + 1), 2.1, 20.0)
    print(f"  crit Gamma_R(s+1) = {s_odd:.4f}: the framework's own volume")
    print(f"  feature IS the excluded object.  Threshold convention check:")
    print(f"  s* = 20.73 -> d_1 = 19 = last d with d+1 < s*;  applying the")
    print(f"  same rule to s* = 5.2569 gives host 4, boundary 3.")

    print()
    print("=" * 74)
    print("What failed 2: unlisted monoid features")
    print("=" * 74)
    f = lambda s: 1.0 / (s - 1) + P(s)
    r1 = brentq(f, 1.01, 3.0)
    r2 = brentq(f, 3.0, 12.0) if f(3.0) * f(12.0) < 0 else None
    print(f"  (s-1)Gamma_R(s) critical points: s = {r1:.3f}"
          f"{', ' + format(r2, '.3f') if r2 else ''} -- in no feature list")
    g = lambda s: 1.0 / s + 1.0 / (s - 1) + P(s)
    print(f"  pole-free grouping s(s-1)Gamma_R/2: min of derivative on")
    print(f"  (1.05, 300) = {min(g(1.05+i*0.5) for i in range(598)):.4f}"
          f" > 0: NO critical point")

    print()
    print("=" * 74)
    print("VERDICT: Finding 6 REOPENED.  The r_2 = 0 obstruction is real")
    print("but partial; the feature->layer selection is a convention and")
    print("joins the residue (item seven); the observer address keeps ONE")
    print("convention-free distinction (torsion half-period; review 3")
    print("demoted the scalar-flatness cross-check).")
    print("(net-state, Theorem 1k: given the site-E pairing the selection")
    print("is lattice-entailed -- member re-motivated, count unchanged;")
    print("Finding 6's completeness question stays open)")
    print("=" * 74)


if __name__ == "__main__":
    main()
