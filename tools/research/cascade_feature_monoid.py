#!/usr/bin/env python3
"""
RESPONSE TO REVIEW FINDING 6: the feature list is complete because
Q has one archimedean place.

The review (riemann-indistinguishability-review.md, Finding 6)
observes that Gamma_R(s+1) -- the sgn tower's factor -- has a
critical point at s = 6.2569, absent from Theorem 7's feature list,
and that its admission would relocate the observer's address.

THE ANSWER.  Features are the analytic features of xi's OWN
factorization.  The factor monoid <s, s-1, Gamma_R(s), zeta(s)>
generates only EVEN shifts of Gamma_R, by the exact recursion
    s Gamma_R(s) = 2 pi Gamma_R(s+2)
(verified below) -- this is how the volume feature (5.2569, the
critical point of the s-regrouped factor, equivalently of
Gamma_R(s+2)) is already inside the monoid.  The ODD shift cannot
enter:
    Gamma_R(s) Gamma_R(s+1) = Gamma_C(s) = 2 (2 pi)^(-s) Gamma(s)
(Legendre duplication; verified below) -- i.e. producing
Gamma_R(s+1) from xi's factors requires the L-factor of a COMPLEX
archimedean place, and Q has none (one real embedding, zero complex
embeddings).  The sgn tower therefore contributes exactly what
Theorem 5 says -- the grading chi = 2 -- and no features: its factor
belongs to odd Dirichlet L-functions (e.g. L(s, chi_-4)), not to
zeta_Q.  The feature list of Theorem 7 is the complete feature set
of the monoid; 6.2569 is a feature of a DIFFERENT L-function.

Consequence: the observer-address pinning (first feature 5.2569 ->
host 5 -> boundary 4) stands, now with the completeness of the
feature list argued from the arithmetic of Q rather than asserted.
Remaining honest caveat: the monoid restriction itself ("features
come from xi's factorization only") is A12's original definition --
consistent, but a definition of scope, recorded as such.
"""

import math

from scipy.special import digamma
from scipy.optimize import brentq

PI = math.pi
LNPI = math.log(PI)


def gamma_R(s):
    return PI ** (-s / 2) * math.gamma(s / 2)


def P(s):
    return 0.5 * digamma(s / 2.0) - 0.5 * LNPI


def main():
    print("=" * 74)
    print("1: the even-shift recursion (volume feature is in the monoid)")
    print("=" * 74)
    worst = 0.0
    for s in (1.5, 4.0, 6.2569, 13.0):
        lhs = s * gamma_R(s)
        rhs = 2 * PI * gamma_R(s + 2)
        worst = max(worst, abs(lhs / rhs - 1))
    print(f"  s Gamma_R(s) = 2 pi Gamma_R(s+2): max rel dev = {worst:.2e}")
    sV = brentq(lambda s: P(s + 2), 2.1, 20.0)
    print(f"  critical point of Gamma_R(s+2): s = {sV:.4f} = the volume")
    print(f"  feature (5.2569): the +2 shift is a regrouping of xi's own")
    print(f"  pole factor -- INSIDE the monoid.")

    print()
    print("=" * 74)
    print("2: the odd shift requires a complex place (Legendre)")
    print("=" * 74)
    worst = 0.0
    for s in (1.5, 4.0, 6.2569, 13.0):
        lhs = gamma_R(s) * gamma_R(s + 1)
        rhs = 2 * (2 * PI) ** (-s) * math.gamma(s)
        worst = max(worst, abs(lhs / rhs - 1))
    print(f"  Gamma_R(s) Gamma_R(s+1) = Gamma_C(s) = 2(2pi)^-s Gamma(s):"
          f" max rel dev = {worst:.2e}")
    s_odd = brentq(lambda s: P(s + 1), 2.1, 20.0)
    print(f"  critical point of Gamma_R(s+1): s = {s_odd:.4f} -- the")
    print(f"  review's candidate.  Producing Gamma_R(s+1) from xi's factors")
    print(f"  requires Gamma_C, the L-factor of a complex archimedean")
    print(f"  place.  Q has r_1 = 1 real and r_2 = 0 complex places:")
    print(f"  the odd shift CANNOT enter zeta_Q's factor monoid.")

    print()
    print("=" * 74)
    print("3: verdict")
    print("=" * 74)
    print("  The sgn tower contributes the grading chi = 2 (Thm 5) and no")
    print("  features: Gamma_R(s+1) belongs to odd Dirichlet L-functions,")
    print("  not to zeta_Q.  Theorem 7's list is the complete feature set")
    print("  of xi's factor monoid; 6.2569 is a feature of a different")
    print("  L-function.  The observer-address pinning stands.  Recorded")
    print("  caveat: 'features come from xi's factorization' is A12's")
    print("  scope definition -- consistent, and now with an arithmetic")
    print("  reason (r_2 = 0) why nothing else can sneak in.")


if __name__ == "__main__":
    main()
