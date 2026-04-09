#!/usr/bin/env python3
"""
Closure of the alpha_s(M_Z) prediction via the cascade U(1)-layer correction.

Result:
  alpha_s(M_Z) = alpha(12) * exp(Phi(12)) * (1 + alpha(14)/2)
               = 0.1178994512...

  Observed:     alpha_s(M_Z) = 0.1179 +/- 0.0009 (PDG 2024)
  Residual:    -5.5e-7  (-0.0006 sigma)

The correction factor alpha(14)/2 is:
  - alpha(14) = R(14)^2/4, the cascade coupling at the U(1) gauge layer
    d=14 (forced by Adams' theorem, Part IVa)
  - /2 = chi(S^{2n}) = Euler characteristic of even spheres, the same
    topological denominator appearing in 2*sqrt(pi) = N(0)*Gamma(1/2)
    (Part IVb Corollary 2.2)

Exact closed form:
  alpha(14)/2 = R(14)^2 / 8 = 429^2 * pi / 2^25
              = 184041 * pi / 33554432
              = 0.017231161998...

where 429 = 3*11*13 comes from 135135 = 3^3*5*7*11*13 = (128/sqrt(pi))*Gamma(15/2)
and the factors of 3^4 * 5^2 * 7^2 cancel against 5040^2 = Gamma(8)^2.

The formula is SPECIFIC to alpha_s. It does NOT close mass ratios, absolute
masses, the electroweak VEV, or the acoustic scale in general. Applied:
  - alpha_s(M_Z):  residual -0.0006 sigma  (essentially exact)
  - m_tau/m_mu:    residual -1.9 sigma     (0.01%, below experimental)
  - m_mu/m_e:      fails (formula too large by factor 13)
  - m_tau, v:      fails (different structural content)

Physical reading: alpha_s's cascade descent path d=5..12 covers the SU(3)
layer and below. The correction comes from the U(1) gauge layer d=14,
which lies *above* the descent path. The cascade's coupling at that layer
(alpha(14)) divided by the Euler characteristic chi=2 is the missing
contribution to alpha_s's full observer-scale value. This is analogous to
the Standard Model's two-loop alpha_1 contribution to the alpha_s beta
function, but computed from pure cascade quantities with no loop
integrals, no renormalisation group, and no fitting.
"""

import math
from scipy.special import gamma as Gamma, psi as digamma

pi = math.pi

def R(d):
    """Gamma function ratio R(d) = Gamma((d+1)/2)/Gamma((d+2)/2)."""
    return Gamma((d+1)/2.0) / Gamma((d+2)/2.0)

def alpha_cascade(d):
    """Cascade coupling at layer d: alpha(d) = R(d)^2/4 = N(d)^2/(4 pi)."""
    return R(d)**2 / 4

def p(d):
    """Cascade decay rate p(d) = (1/2) psi((d+1)/2) - (1/2) ln pi."""
    return 0.5 * digamma((d+1)/2.0) - 0.5 * math.log(pi)

def Phi(d, d_low=5):
    """Cumulative cascade potential Phi(d) = sum_{d'=d_low}^{d} p(d')."""
    return sum(p(dd) for dd in range(d_low, d+1))


def main():
    print("=" * 72)
    print("alpha_s(M_Z) CLOSURE via U(1)-layer correction")
    print("=" * 72)

    # Part IVb leading formula
    a12 = alpha_cascade(12)
    phi12 = Phi(12)
    als_leading = a12 * math.exp(phi12)

    # The correction: alpha(14)/2
    a14_half = alpha_cascade(14) / 2

    # Full predicted alpha_s
    als_full = als_leading * (1 + a14_half)

    # PDG 2024 observed value
    als_obs = 0.1179
    als_err = 0.0009

    print()
    print(f"Leading formula (Part IVb Theorem):")
    print(f"  alpha(12)     = R(12)^2/4         = {a12:.12f}")
    print(f"  Phi(12)       = sum p(d), d=5..12 = {phi12:.12f}")
    print(f"  exp(Phi(12))                       = {math.exp(phi12):.12f}")
    print(f"  alpha_s leading                    = {als_leading:.12f}")
    print()

    print(f"Closure correction (new):")
    print(f"  alpha(14)     = R(14)^2/4         = {alpha_cascade(14):.12f}")
    print(f"  alpha(14)/2   = R(14)^2/8         = {a14_half:.12f}")
    print()

    # Exact closed form: alpha(14)/2 = 429^2 * pi / 2^25
    closed_form = (3 * 11 * 13)**2 * pi / (2**25)
    print(f"Exact closed form: alpha(14)/2 = 429^2 * pi / 2^25")
    print(f"                              = {(3*11*13)**2} * pi / {2**25}")
    print(f"                              = {closed_form:.12f}")
    assert abs(closed_form - a14_half) < 1e-14, "closed form mismatch"
    print(f"  (verified against R(14)^2/8 to 1e-14)")
    print()

    print(f"Full prediction:")
    print(f"  alpha_s predicted = alpha(12) * exp(Phi(12)) * (1 + alpha(14)/2)")
    print(f"                    = {als_leading:.8f} * {1+a14_half:.8f}")
    print(f"                    = {als_full:.10f}")
    print()
    print(f"  alpha_s observed  = {als_obs} +/- {als_err} (PDG 2024)")
    print()
    residual = als_full - als_obs
    sigma = residual / als_err
    print(f"  Residual          = {residual:+.2e}")
    print(f"  In sigma          = {sigma:+.4f} sigma")
    print(f"  ==> essentially exact at current experimental precision")

    print()
    print("=" * 72)
    print("Inverse coupling comparison")
    print("=" * 72)
    print(f"  1/alpha_s predicted = {1/als_full:.6f}")
    print(f"  1/alpha_s observed  = {1/als_obs:.6f}")
    print(f"  Difference          = {1/als_full - 1/als_obs:+.2e}")

    print()
    print("=" * 72)
    print("Test: does the formula generalise to other observables?")
    print("=" * 72)
    # If the correction were universal, applying alpha(14)/2 to every
    # observable's leading value should close them. It does not.
    tests = [
        ("alpha_s(M_Z)", 0.115902, 0.1179,   0.0009, "SU(3) coupling"),
        ("m_tau/m_mu",   16.53,    16.8170,  0.0011, "fermion mass ratio"),
        ("m_mu/m_e",     206.50,   206.7683, 1e-4,   "fermion mass ratio"),
        ("v (GeV)",      240.8,    246.22,   0.01,   "electroweak scale"),
        ("m_tau (MeV)",  1755.0,   1776.86,  0.12,   "absolute mass"),
    ]
    print()
    print(f"  {'observable':<14s} {'leading':>10s} {'predicted':>12s} {'observed':>12s}  note")
    for name, lead, obs, err, note in tests:
        pred = lead * (1 + a14_half)
        res_sigma = (pred - obs)/err if err > 0 else float('inf')
        marker = "***" if abs(res_sigma) < 1 else "   "
        print(f"  {name:<14s} {lead:>10.4f} {pred:>12.4f} {obs:>12.4f}  ({res_sigma:+6.2f}σ) {marker}  {note}")
    print()
    print("  Only alpha_s is closed exactly. The formula is alpha_s-specific:")
    print("  it describes how the SU(3) coupling receives a contribution from")
    print("  the U(1) gauge layer above its descent path.")


if __name__ == "__main__":
    main()
