#!/usr/bin/env python3
"""
Research: derive the Gram first-order correction from the cascade action.

The cascade scalar action (Part IVb Remark 4.6) is:

    S[phi] = sum_d (1/(2 alpha(d))) (Delta phi)^2,    Delta phi(d) = phi(d+1) - phi(d).

Its marginal Green's function gives the alpha(d*)/chi^k family (Part IVb).

The Gram first-order correction (Part 0 Supplement Theorem 14.6) is:

    delta Phi = sum_k (1 - C^2_{d_k, d_{k+1}}),    C_{ij} = G_{ij}/sqrt(G_ii G_jj).

The asymptotic match 1 - C^2_{d,d+1} ~ alpha(d)^2/2 (sub-percent at d>=10)
suggests Gram is the *bilinear* version of the action's *linear* source response.

This script tests several candidate identifications:

  H1: 1 - C^2 = alpha(d)^2 / 2   (asymptotic match)
  H2: 1 - C^2 = alpha(d) * alpha(d+1) / 2    (adjacent-pair product)
  H3: 1 - C^2 = (alpha(d) + alpha(d+1))^2 / 8    (averaged-squared)
  H4: 1 - C^2 = alpha(d)^2 / 2 + correction    (search for closed-form correction)

Each candidate is tested across d = 4..50, looking for either an exact match
(structural unification candidate) or a recoverable closed-form correction.
"""

import math
import os
import sys

import numpy as np
from scipy.special import gammaln, betaln

# Add tools/ to path
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", ".."))
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))


def beta(a, b):
    """Beta function B(a,b)."""
    return math.exp(betaln(a, b))


def gram_entry(d_i, d_j):
    """Gram matrix entry G_{ij} = B(1/2, (d_i+d_j)/2 + 1)."""
    return beta(0.5, (d_i + d_j) / 2.0 + 1.0)


def correlation(d_i, d_j):
    """Correlation matrix entry C_{ij} = G_{ij} / sqrt(G_ii G_jj)."""
    return gram_entry(d_i, d_j) / math.sqrt(gram_entry(d_i, d_i) * gram_entry(d_j, d_j))


def gram_deficit(d):
    """Per-step Gram deficit 1 - C^2_{d, d+1}."""
    c = correlation(d, d + 1)
    return 1.0 - c * c


def R_func(d):
    """Slicing recurrence coefficient R(d) = Gamma((d+1)/2) / Gamma((d+2)/2)."""
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha_func(d):
    """Cascade gauge coupling alpha(d) = R(d)^2 / 4."""
    return R_func(d) ** 2 / 4.0


def main():
    print("=" * 78)
    print("RESEARCH: GRAM FIRST-ORDER CORRECTION FROM CASCADE ACTION")
    print("=" * 78)
    print()
    print("Testing candidate identifications for 1 - C^2_{d, d+1}")
    print("at exact (Beta function) values vs cascade-action quantities.")
    print()

    # ------------------------------------------------------------------
    # 1. Tabulate Gram deficit and gauge coupling
    # ------------------------------------------------------------------
    print("-" * 78)
    print("1. Gram deficit vs alpha(d) at exact values")
    print("-" * 78)
    print(
        f"{'d':>4}  {'1-C^2_{d,d+1}':>16}  {'alpha(d)':>14}  "
        f"{'alpha(d)^2/2':>14}  {'ratio':>10}"
    )
    print("-" * 78)

    d_values = list(range(4, 30)) + [50, 100, 200]
    for d in d_values:
        deficit = gram_deficit(d)
        alpha = alpha_func(d)
        candidate = alpha ** 2 / 2.0
        ratio = candidate / deficit if deficit != 0 else float("nan")
        print(
            f"{d:>4}  {deficit:>16.8e}  {alpha:>14.8e}  "
            f"{candidate:>14.8e}  {ratio:>10.6f}"
        )

    # ------------------------------------------------------------------
    # 2. Test multiple candidates
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("2. Multiple candidate identifications")
    print("-" * 78)
    print("Candidates:")
    print("  H1:  alpha(d)^2 / 2")
    print("  H2:  alpha(d) * alpha(d+1) / 2")
    print("  H3:  (alpha(d) + alpha(d+1))^2 / 8")
    print("  H4:  alpha(d)^2 / 2 - alpha(d)^3 / something")
    print()
    print(
        f"{'d':>4}  {'1-C^2':>14}  {'H1':>14}  {'H1 ratio':>10}  "
        f"{'H2':>14}  {'H2 ratio':>10}  {'H3':>14}  {'H3 ratio':>10}"
    )
    print("-" * 78)

    for d in [4, 5, 6, 7, 10, 15, 20, 30, 50, 100]:
        deficit = gram_deficit(d)
        alpha_d = alpha_func(d)
        alpha_d1 = alpha_func(d + 1)
        H1 = alpha_d ** 2 / 2.0
        H2 = alpha_d * alpha_d1 / 2.0
        H3 = (alpha_d + alpha_d1) ** 2 / 8.0
        r1 = H1 / deficit
        r2 = H2 / deficit
        r3 = H3 / deficit
        print(
            f"{d:>4}  {deficit:>14.8e}  {H1:>14.8e}  {r1:>10.6f}  "
            f"{H2:>14.8e}  {r2:>10.6f}  {H3:>14.8e}  {r3:>10.6f}"
        )

    # ------------------------------------------------------------------
    # 3. Search for the exact closed form
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("3. Searching for an exact closed form via Beta function identities")
    print("-" * 78)

    # The exact deficit is 1 - C^2 = 1 - B(1/2, d+3/2)^2 / [B(1/2, d+1) B(1/2, d+2)]
    # Use Beta function reduction identity: B(1/2, n+1) = sqrt(pi) Gamma(n+1)/Gamma(n+3/2)
    #
    # Let's compute exact ratios.

    print("Exact 1 - C^2 in terms of Gamma function ratios:")
    print()
    print(
        f"{'d':>4}  {'1-C^2 numeric':>16}  {'closed form':>20}  "
        f"{'closed/numeric':>14}"
    )
    print("-" * 78)

    for d in [4, 5, 7, 10, 19, 50]:
        deficit = gram_deficit(d)
        # Try: 1 - C^2 = 1 - [Gamma(d+5/2)^2 Gamma(d+3/2) / (Gamma(d+2)^2 Gamma(d+5/2)^2)]^...
        # Actually let's just compute the deficit via ln Gamma to get high precision.
        # deficit = 1 - exp(2*gammaln(d+5/2) - gammaln(d+2) - gammaln(d+5/2)
        #                  + gammaln(d+1)/2 + ...)
        # Hmm this is getting messy. Let's use the formulation:
        # G_ij = B(1/2, (d_i + d_j)/2 + 1) = sqrt(pi) Gamma((d_i+d_j)/2 + 1) / Gamma((d_i+d_j)/2 + 3/2)
        # For i=d, j=d+1: G_{d,d+1} = sqrt(pi) Gamma(d+3/2) / Gamma(d+2)
        # For i=j=d:     G_dd      = sqrt(pi) Gamma(d+1)   / Gamma(d+3/2)
        # For i=j=d+1:   G_{d+1,d+1} = sqrt(pi) Gamma(d+2)   / Gamma(d+5/2)
        #
        # C^2 = G_{d,d+1}^2 / (G_dd * G_{d+1,d+1})
        #     = pi * [Gamma(d+3/2)^2 / Gamma(d+2)^2] / (pi * Gamma(d+1)/Gamma(d+3/2) * Gamma(d+2)/Gamma(d+5/2))
        #     = [Gamma(d+3/2)^2 / Gamma(d+2)^2] * [Gamma(d+3/2) Gamma(d+5/2) / (Gamma(d+1) Gamma(d+2))]
        #     = Gamma(d+3/2)^3 Gamma(d+5/2) / (Gamma(d+1) Gamma(d+2)^3)

        # Let's verify this:
        ln_C2 = 3 * gammaln(d + 1.5) + gammaln(d + 2.5) - gammaln(d + 1) - 3 * gammaln(d + 2)
        C2_check = math.exp(ln_C2)
        deficit_check = 1.0 - C2_check
        print(f"{d:>4}  {deficit:>16.10e}  {deficit_check:>20.10e}  {deficit_check/deficit:>14.8f}")

    # ------------------------------------------------------------------
    # 4. Use Gamma function identities to express 1 - C^2 cleanly
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("4. Using Gamma duplication / shift identities")
    print("-" * 78)
    # Gamma(d+3/2) = (d+1/2) Gamma(d+1/2)
    # Gamma(d+5/2) = (d+3/2)(d+1/2) Gamma(d+1/2)
    # Gamma(d+2) = (d+1) Gamma(d+1)
    # So C^2 = Gamma(d+3/2)^3 (d+3/2)(d+1/2) Gamma(d+1/2) / [Gamma(d+1) (d+1)^3 Gamma(d+1)^3]
    # Hmm let's simplify differently:
    # C^2 = Gamma(d+3/2)^3 Gamma(d+5/2) / [Gamma(d+1) Gamma(d+2)^3]
    #     = Gamma(d+3/2)^3 / Gamma(d+2)^3  *  Gamma(d+5/2) / [Gamma(d+1) * 1]
    #     = R(2d+2)^3 * Gamma(d+5/2)/Gamma(d+1)
    # where R(d) = Gamma((d+1)/2)/Gamma((d+2)/2). But that's at half-integer arguments...
    # Let's use a cleaner approach: define r(d) = Gamma(d+3/2)/Gamma(d+2) -- this is "R(2d+2)/sqrt(pi)" up to indexing.
    # Then C^2 = r(d)^3 / r(d) * Gamma(d+5/2)/Gamma(d+1)... actually this isn't simplifying easily.
    #
    # Simplest computational form: 1 - C^2 in terms of two consecutive R values.
    # Note R(2d+1) = Gamma(d+1)/Gamma(d+3/2)  (with R(d) = Gamma((d+1)/2)/Gamma((d+2)/2), so R(2d+1) takes (2d+2)/2 = d+1 and (2d+3)/2 = d+3/2, OK so this is not the same as alpha(d)'s R)
    # Hmm, R(d) in cascade_constants.py uses single-d input.
    # alpha(d) = R(d)^2/4 = [Gamma((d+1)/2)/Gamma((d+2)/2)]^2 / 4
    # For d -> 2d+1 (odd): R(2d+1) = Gamma(d+1)/Gamma(d+3/2)
    # For d -> 2d+2 (even): R(2d+2) = Gamma(d+3/2)/Gamma(d+2)
    print("Using the relation R(2d+2) = Gamma(d+3/2)/Gamma(d+2):")
    print()
    print(
        f"{'d':>4}  {'R(2d+2)':>14}  {'1-C^2':>16}  "
        f"{'R(2d+2)^2 form?':>16}  {'ratio':>10}"
    )
    print("-" * 78)
    for d in [4, 5, 7, 10, 19, 50]:
        deficit = gram_deficit(d)
        # R(2d+2) = Gamma(d+3/2)/Gamma(d+2)
        R2dp2 = math.exp(gammaln(d + 1.5) - gammaln(d + 2.0))
        # candidate = R(2d+2)^2 * something
        # We have C^2 = R(2d+2)^3 * (other stuff)
        # 1 - C^2 = 1 - R(2d+2)^3 * Gamma(d+5/2)/Gamma(d+1)
        # Hmm. Let me just print R2dp2 and see.
        # Try candidate alpha(2d+2) = R(2d+2)^2/4 — but the supplement uses alpha(d), not alpha(2d+2)
        candidate = R2dp2 ** 2  # just R^2, no /4 yet
        ratio = candidate / deficit if deficit != 0 else float("nan")
        print(f"{d:>4}  {R2dp2:>14.8e}  {deficit:>16.8e}  {candidate:>16.8e}  {ratio:>10.6f}")

    # ------------------------------------------------------------------
    # 5. Beta function asymptotic refinement
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("5. Higher-order asymptotic of 1 - C^2 vs alpha(d)^2/2")
    print("-" * 78)
    print("Asymptotic: 1 - C^2 = 1/(8(d+a)^2) for some a.")
    print("If a = 0: 1/(8 d^2). If a = 3 (R_eff convention): 1/(8(d+3)^2).")
    print()
    print(
        f"{'d':>4}  {'1-C^2':>16}  {'1/(8d^2)':>14}  {'1/(8(d+3)^2)':>16}  "
        f"{'alpha(d)^2/2':>16}"
    )
    print("-" * 78)
    for d in [4, 5, 6, 7, 10, 15, 19, 30, 50, 100]:
        deficit = gram_deficit(d)
        a0 = 1.0 / (8.0 * d ** 2)
        a3 = 1.0 / (8.0 * (d + 3) ** 2)
        a_alpha = alpha_func(d) ** 2 / 2.0
        print(
            f"{d:>4}  {deficit:>16.10e}  {a0:>14.8e}  {a3:>16.10e}  "
            f"{a_alpha:>16.10e}"
        )

    # ------------------------------------------------------------------
    # 6. Test: is 1 - C^2 = alpha(2d+2)^2/2?
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("6. Test: 1 - C^2 vs alpha at shifted argument")
    print("-" * 78)
    print("If the gauge coupling that matches Gram is alpha(2d+2) (Beta-function reduction):")
    print()
    print(
        f"{'d':>4}  {'1-C^2':>16}  {'alpha(2d+2)':>14}  "
        f"{'alpha(2d+2)/2':>14}  {'ratio':>10}"
    )
    print("-" * 78)
    for d in [4, 5, 7, 10, 19, 50]:
        deficit = gram_deficit(d)
        # alpha(2d+2) = R(2d+2)^2/4
        R2dp2 = math.exp(gammaln(d + 1.5) - gammaln(d + 2.0))
        alpha_2dp2 = R2dp2 ** 2 / 4.0
        candidate = alpha_2dp2 / 2.0
        ratio = candidate / deficit if deficit != 0 else float("nan")
        print(
            f"{d:>4}  {deficit:>16.10e}  {alpha_2dp2:>14.8e}  "
            f"{candidate:>14.8e}  {ratio:>10.6f}"
        )

    print()
    print("If ratio = 1.000000 exactly, this is the structural identity.")
    print()


if __name__ == "__main__":
    main()
