#!/usr/bin/env python3
"""
Closed-form expression for the Gram correlation C^2_{d,d+1}.

From Section 3 of gram_from_action.py:
    C^2_{d,d+1} = Gamma(d+3/2)^3 Gamma(d+5/2) / [Gamma(d+1) Gamma(d+2)^3]

Using Gamma(d+5/2) = (d+3/2) Gamma(d+3/2) and Gamma(d+2) = (d+1) Gamma(d+1):

    C^2 = (d+3/2)/(d+1)^3 * [Gamma(d+3/2)/Gamma(d+1)]^4

And Gamma(d+3/2)/Gamma(d+1) = (d+1) * Gamma(d+3/2)/Gamma(d+2) = (d+1) R(2d+2),
where R(d) = Gamma((d+1)/2)/Gamma((d+2)/2) is the cascade slicing ratio.

Therefore:
    C^2_{d,d+1} = (d+1)(d+3/2) R(2d+2)^4

This is an EXACT closed form for the Gram correlation in terms of the cascade
slicing ratio at the "doubled" argument 2d+2 (which lives at the even-sphere
layers in the cascade, the same layers where chirality factorisation happens
in Part IVb Theorem 4.8).

This script:
1. Verifies the closed form to machine precision.
2. Re-expresses 1 - C^2 in terms of cascade primitives.
3. Tests whether the closed form connects to alpha(d) of the cascade action.
"""

import math

import numpy as np
from scipy.special import betaln, gammaln


def beta(a, b):
    return math.exp(betaln(a, b))


def gram_C2(d):
    """C^2_{d,d+1} via direct computation."""
    # G_ij = B(1/2, (d_i+d_j)/2 + 1)
    G_dd = beta(0.5, d + 1.0)
    G_d1d1 = beta(0.5, d + 2.0)
    G_dd1 = beta(0.5, d + 1.5)
    return G_dd1 ** 2 / (G_dd * G_d1d1)


def R_func(d):
    """Cascade slicing ratio R(d) = Gamma((d+1)/2) / Gamma((d+2)/2)."""
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def C2_closed_form(d):
    """Closed form: C^2_{d,d+1} = (d+1)(d+3/2) R(2d+2)^4."""
    R_val = R_func(2 * d + 2)
    return (d + 1) * (d + 1.5) * R_val ** 4


def alpha(d):
    """Cascade gauge coupling alpha(d) = R(d)^2 / 4."""
    return R_func(d) ** 2 / 4.0


def main():
    print("=" * 78)
    print("CLOSED FORM FOR C^2_{d,d+1}")
    print("=" * 78)
    print()
    print("Claim:  C^2_{d,d+1} = (d+1)(d+3/2) R(2d+2)^4")
    print()
    print("where R(d) = Gamma((d+1)/2)/Gamma((d+2)/2) is the cascade slicing ratio.")
    print()

    # ------------------------------------------------------------------
    # 1. Verify the closed form
    # ------------------------------------------------------------------
    print("-" * 78)
    print("1. Verification of closed form")
    print("-" * 78)
    print(
        f"{'d':>4}  {'C^2 direct':>20}  {'C^2 closed form':>20}  {'ratio':>14}"
    )
    print("-" * 78)
    for d in [4, 5, 7, 10, 15, 19, 30, 50, 100, 200]:
        c2_direct = gram_C2(d)
        c2_closed = C2_closed_form(d)
        ratio = c2_closed / c2_direct
        print(f"{d:>4}  {c2_direct:>20.14e}  {c2_closed:>20.14e}  {ratio:>14.10f}")

    # ------------------------------------------------------------------
    # 2. Re-express in terms of alpha(2d+2)
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("2. C^2 in terms of cascade gauge coupling alpha(2d+2)")
    print("-" * 78)
    print("Note: alpha(d) = R(d)^2/4, so R(2d+2)^4 = (4*alpha(2d+2))^2 = 16 alpha(2d+2)^2")
    print()
    print("Therefore:  C^2_{d,d+1} = 16 (d+1)(d+3/2) alpha(2d+2)^2")
    print()
    print(
        f"{'d':>4}  {'C^2':>16}  {'16(d+1)(d+3/2)alpha(2d+2)^2':>32}  {'ratio':>10}"
    )
    print("-" * 78)
    for d in [4, 5, 7, 10, 19, 50, 100]:
        c2 = gram_C2(d)
        a_val = alpha(2 * d + 2)
        candidate = 16.0 * (d + 1) * (d + 1.5) * a_val ** 2
        ratio = candidate / c2
        print(f"{d:>4}  {c2:>16.10e}  {candidate:>32.10e}  {ratio:>10.6f}")

    # ------------------------------------------------------------------
    # 3. Closed form for 1 - C^2
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("3. Closed form for the Gram deficit 1 - C^2_{d,d+1}")
    print("-" * 78)
    print("1 - C^2 = 1 - (d+1)(d+3/2) R(2d+2)^4")
    print()
    print("The factor (d+1)(d+3/2) R(2d+2)^4 is structurally clean:")
    print("  - (d+1)(d+3/2) is a polynomial in d.")
    print("  - R(2d+2)^4 is the fourth power of the cascade ratio at doubled argument.")
    print()
    print(
        f"{'d':>4}  {'1-C^2':>16}  {'1-(d+1)(d+3/2)R(2d+2)^4':>30}  {'ratio':>10}"
    )
    print("-" * 78)
    for d in [4, 5, 7, 10, 19, 50, 100]:
        deficit_direct = 1.0 - gram_C2(d)
        deficit_closed = 1.0 - C2_closed_form(d)
        ratio = deficit_closed / deficit_direct
        print(f"{d:>4}  {deficit_direct:>16.10e}  {deficit_closed:>30.10e}  {ratio:>10.6f}")

    # ------------------------------------------------------------------
    # 4. Asymptotic structure of the closed form
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("4. Asymptotic structure")
    print("-" * 78)
    print("R(d) ~ sqrt(2/(d+1)), so R(2d+2)^4 ~ 4/(2d+3)^2 ~ 1/(d+3/2)^2")
    print("Therefore (d+1)(d+3/2) R(2d+2)^4 ~ (d+1)/(d+3/2) ~ 1 - 1/(2d) + ...")
    print()
    print(
        f"{'d':>4}  {'C^2 closed':>16}  "
        f"{'1 - 1/(2d) + 3/(8d^2)':>22}  {'1 - 1/(2(d+1))':>16}"
    )
    print("-" * 78)
    for d in [4, 5, 10, 20, 50, 100]:
        c2 = gram_C2(d)
        # Asymptotic check
        candidate1 = 1.0 - 1.0 / (2.0 * d) + 3.0 / (8.0 * d ** 2)
        candidate2 = 1.0 - 1.0 / (2.0 * (d + 1))
        print(f"{d:>4}  {c2:>16.10e}  {candidate1:>22.10e}  {candidate2:>16.10e}")

    # ------------------------------------------------------------------
    # 5. Connection to cascade Green's function?
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("5. Does (d+1)(d+3/2) R(2d+2)^4 connect to the Green's function?")
    print("-" * 78)
    print()
    print("Cascade Green's function (Part IVb):")
    print("  - Marginal: G(d_obs, d*) - G(d_obs, d*+1) = alpha(d*).")
    print("  - alpha(d*) = R(d*)^2/4 at single layer.")
    print()
    print("Gram deficit involves R(2d+2)^4 — fourth power, doubled argument.")
    print("The doubled argument 2d+2 corresponds to 'two layers above d' in some sense:")
    print("  d -> 2d+2 maps consecutive cascade layers to 'doubled' indices.")
    print("  This may be related to the chirality factorisation: Part IVb has")
    print("  even-sphere layers (d odd, S^{d-1} = S^{2n} where 2n = d-1).")
    print("  For d even, 2d+2 is also even.")
    print()
    print("Alternative reading: R(2d+2)^4 = (R(2d+2)^2)^2 = (4 alpha(2d+2))^2")
    print("                              = 16 alpha(2d+2)^2")
    print()
    print("So C^2_{d,d+1} = 16 (d+1)(d+3/2) alpha(2d+2)^2.")
    print()
    print("This connects the Gram correlation to the SQUARE of the cascade gauge")
    print("coupling at the doubled argument — i.e., the BILINEAR response.")
    print()


if __name__ == "__main__":
    main()
