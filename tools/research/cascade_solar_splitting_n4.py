#!/usr/bin/env python3
"""
Solar mass-squared splitting from cascade four-source n=4 product?

THE NEAR-MATCH
==============
Survey of natural 4-fold cascade structures (cascade_n4_native_survey.py)
identified one suggestive numerical coincidence:

    alpha(5) * alpha(7) * alpha(14) * alpha(19) * 2*pi^2 = 1.05e-4

vs observed solar mass-squared splitting

    Delta m^2_sol = 7.5e-5 eV^2  (NuFIT 2024)

Off by factor 1.4 (log10 ratio +0.15).  This is suggestive enough to
investigate whether a clean cascade-internal mechanism produces an
exact match.

THE STRUCTURAL READING
======================
The four sources d^* in {d_V=5, d_0=7, d_gw=14, d_1=19} are the cascade's
four distinguished non-sink layers (Part IVb prop:source-selection).
Each is currently used one-at-a-time as the source in the alpha(d^*)/chi^k
correction family.  The hypothesis is that a NOVEL cascade observable
exercises ALL FOUR sources simultaneously, with cascade structural form

    Q^(novel) = (cascade-internal kinematic factor) * prod_d^* alpha(d^*)
              * chi^(m-k) * (per-leg primitives)

For the n=4 chirality slot, chi^(m-k) = chi at m=1, k=0 (closed loop with
no external chirality modes), and per-leg primitive Gamma(1/2)^n at
n-leg topology.  For n=4: chi * Gamma(1/2)^4 = 2*pi^2.

So the hypothesis is

    Delta m^2_sol = (alpha(5) * alpha(7) * alpha(14) * alpha(19))
                    * 2*pi^2 * (cascade-internal dimensional factor)

WHAT THIS SCRIPT DOES
=====================
  1. Computes the four-source n=4 product precisely.
  2. Searches for a cascade-internal multiplicative factor that brings
     the prediction to exact match with observed Delta m^2_sol.
  3. Tests whether that factor is cascade-natural (e.g., R(d), N(d),
     simple cascade primitives) or arbitrary.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Force a structural closure.  If the multiplicative factor is not
    cascade-natural, report the near-match as suggestive but not
    closing.
"""

from __future__ import annotations

import math


def R_cascade(d: int) -> float:
    return math.exp(math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0))


def alpha_cascade(d: int) -> float:
    return R_cascade(d) ** 2 / 4.0


def N_cascade(d: int) -> float:
    return math.sqrt(math.pi) * R_cascade(d)


CHI = 2
GAMMA_HALF = math.sqrt(math.pi)
TWOPISQ = 2 * math.pi ** 2

# Four distinguished sources
SOURCES = [5, 7, 14, 19]


def four_source_product():
    P = 1.0
    for d in SOURCES:
        P *= alpha_cascade(d)
    return P


def main():
    print("=" * 76)
    print("Solar mass-squared splitting from cascade four-source n=4?")
    print("=" * 76)
    print()

    P = four_source_product()
    cascade_4src_n4 = P * TWOPISQ

    obs_dm2_sol = 7.50e-5   # eV^2, NuFIT 2024
    obs_dm2_sol_err = 0.21e-5  # 1-sigma

    print("Step 1: Four-source product")
    print("-" * 76)
    print(f"  alpha(5)  = {alpha_cascade(5):.6f}")
    print(f"  alpha(7)  = {alpha_cascade(7):.6f}")
    print(f"  alpha(14) = {alpha_cascade(14):.6f}")
    print(f"  alpha(19) = {alpha_cascade(19):.6f}")
    print(f"  P_4src = prod = {P:.6e}")
    print()
    print(f"  P_4src * 2*pi^2 = {cascade_4src_n4:.6e}")
    print(f"  Observed Delta m^2_sol = {obs_dm2_sol:.6e} eV^2")
    print()
    factor_needed = obs_dm2_sol / cascade_4src_n4
    print(f"  Required cascade dimensional factor = obs / cascade_4src_n4")
    print(f"                                      = {factor_needed:.6f}")
    print()

    print("Step 2: search for cascade-natural factor matching {factor_needed}")
    print("-" * 76)

    # Test cascade-internal candidates for the dimensional factor
    candidates = [
        ("1/sqrt(2)",                    1/math.sqrt(2)),
        ("1/sqrt(pi)",                   1/math.sqrt(math.pi)),
        ("1/2",                          0.5),
        ("R(5)",                         R_cascade(5)),
        ("R(7)",                         R_cascade(7)),
        ("R(14)",                        R_cascade(14)),
        ("R(19)",                        R_cascade(19)),
        ("R(4)",                         R_cascade(4)),
        ("alpha(4)",                     alpha_cascade(4)),
        ("alpha(d_gw=14)",               alpha_cascade(14)),
        ("alpha(d_1=19)",                alpha_cascade(19)),
        ("R(5) * R(7)",                  R_cascade(5) * R_cascade(7)),
        ("R(14) / R(19)",                R_cascade(14) / R_cascade(19)),
        ("1 / pi",                       1/math.pi),
        ("2 / pi",                       2/math.pi),
        ("3/4",                          0.75),
        ("5/7",                          5/7),
        ("e/4",                          math.e/4),
        ("1 - 1/(2*pi)",                 1 - 1/(2*math.pi)),
        ("Gamma(1/2)/Gamma(1)",          math.sqrt(math.pi)/1.0),
        ("alpha(20)/alpha(19)",          alpha_cascade(20)/alpha_cascade(19)),
        ("alpha(19)/alpha(20)",          alpha_cascade(19)/alpha_cascade(20)),
    ]

    print(f"  Looking for factor approx {factor_needed:.4f}")
    print(f"  (within +/- 5%, i.e. {factor_needed*0.95:.4f} to {factor_needed*1.05:.4f}):")
    print()
    print(f"  {'Candidate':<35s}  {'value':>10s}  {'cascade pred (eV^2)':>22s}  {'dev':>10s}")
    for name, val in candidates:
        pred = cascade_4src_n4 * val
        dev = (pred - obs_dm2_sol) / obs_dm2_sol * 100
        match = " <-- match" if abs(dev) < 5 else ""
        print(f"  {name:<35s}  {val:>10.4f}  {pred:>22.4e}  {dev:>+9.2f}%{match}")
    print()

    print("Step 3: cleaner reading -- structural anchor")
    print("-" * 76)
    print()
    print("  Try: cascade structurally predicts Delta m^2_sol =")
    print("    (four-source product) * (chirality-theorem n=4 factor)")
    print("    /  (some natural cascade primitive that makes it dimensionful)")
    print()
    print(f"  Bare four-source product = {P:.4e} (dimensionless)")
    print(f"  Times 2*pi^2:             {cascade_4src_n4:.4e}")
    print()

    # The four-source product alpha(5)*alpha(7)*alpha(14)*alpha(19) is dimensionless
    # in cascade-natural units.  To get eV^2, we need a dimensional factor.
    # The cascade's natural mass scale is m_29 ~ 543 eV, so m_29^2 ~ 3e5 eV^2.
    # Or v ~ 246 GeV -> v^2 ~ 6e22 eV^2.  Or M_Pl^2 ~ 6e36 eV^2.
    print("  Possible dimensional anchors:")
    print(f"    m_29^2 (neutrino source mass)^2 = {543**2:.4e} eV^2")
    print(f"    m_e^2  (electron mass)^2        = {511_000**2:.4e} eV^2")
    print(f"    m_1^2  (cascade Gen 1 neutrino) = {0.0493**2:.4e} eV^2")
    print(f"    m_29^2 / chi^k:")
    for k in range(8, 16):
        anchor = 543**2 / (CHI ** k)
        pred = cascade_4src_n4 * anchor / 543**2  # actually we want
        # cascade_pred = (4src product) * (TWOPISQ) but we already have cascade_4src_n4
        # multiplied by m_29^2 gives the anchor times the dimensionless product.
        # If anchor is m_29^2/chi^k, then total prediction is (4src product) * 2pi^2 * m_29^2 / chi^k
        # / additional units?  Let me think again.
        pass

    # Different framing: cascade_4src_n4 IS dimensionless (alpha is dimensionless),
    # so to compare with eV^2, we need to recognise that the cascade's natural
    # SCALE for neutrino-mass-squared splittings is set by m_29^2 / chi^(2*n_descent).
    # Try: cascade_4src_n4 * (m_29^2 / chi^(2*8))?
    print()
    print("  Cascade-natural eV^2 scales (per-source-product times mass-scale):")
    for k in range(0, 20):
        anchor = 543**2 / (CHI ** k)
        if anchor < 1e-3 or anchor > 1e8:
            continue
        pred = cascade_4src_n4 * anchor / 543**2
        # actually let's just multiply
        pred_alt = P * TWOPISQ * anchor
        dev = (pred_alt - obs_dm2_sol) / obs_dm2_sol * 100
        match = " <-- match" if abs(dev) < 10 else ""
        if abs(dev) < 100 or match:
            print(f"    P * 2*pi^2 * m_29^2/chi^{k:>2}  = {pred_alt:>10.4e} eV^2  ({dev:>+9.2f}%){match}")
    print()


if __name__ == "__main__":
    main()
