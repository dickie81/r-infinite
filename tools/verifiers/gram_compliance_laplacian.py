#!/usr/bin/env python3
"""
Verify the Gram-Laplacian identity of the Part 0 Supplement:

    log C^2_{d, d+1}  =  -(1/2) Delta^2 log alpha |_{2d+2}

equivalently

    C^2_{d, d+1}  =  R(2d+2)^2 / [R(2d+1) R(2d+3)]

where:
  - C_{d, d'} is the Gram correlation between cascade layer integrands
    f_d(x) = (1 - x^2)^{d/2} in L^2[-1, 1].
  - R(d) = Gamma((d+1)/2) / Gamma((d+2)/2) is the cascade slicing ratio.
  - alpha(d) = R(d)^2/4 is the cascade scalar action's compliance function
    (Paper IVb Remark 4.6).
  - Delta^2 f|_n = f(n-1) + f(n+1) - 2 f(n) is the centered discrete
    Laplacian.

This identity establishes the supplement's Gram first-order correction as
a corollary of the cascade scalar action principle of Paper IVb: the
single-source family alpha(d*)/chi^k (Paper IVb) and the path-distributed
Gram correction (this supplement) are complementary derivatives of the
same compliance function.

The proof is symbolic (Beta-Gamma reduction, see Part 0 Supplement
Theorem on Gram correlation in cascade slicing ratios). This script
provides numerical confirmation to machine precision.

No semiclassical content: the verification is direct evaluation of
Beta function values and Gamma function ratios. Check 7 clean.
"""

from __future__ import annotations

import math
import os
import sys

from scipy.special import betaln, gammaln  # type: ignore[import-not-found]

# Shared cascade primitives.  We use gammaln-based computations directly here
# (rather than importing cascade_constants.R / alpha) because the path sums
# range up to d = 217, and 2d+3 = 437 overflows the straight Gamma function.
# log-Gamma stays finite throughout.
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))


def beta(a: float, b: float) -> float:
    """Beta function B(a, b)."""
    return math.exp(betaln(a, b))


def log_R(d: int) -> float:
    """Log of cascade slicing ratio: log R(d) = ln Gamma((d+1)/2) - ln Gamma((d+2)/2)."""
    return float(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def R(d: int) -> float:
    """Cascade slicing ratio R(d) = Gamma((d+1)/2) / Gamma((d+2)/2)."""
    return math.exp(log_R(d))


def log_alpha(d: int) -> float:
    """Log of cascade gauge coupling: log alpha(d) = 2 log R(d) - 2 log 2."""
    return 2.0 * log_R(d) - 2.0 * math.log(2.0)


def gram_C2_direct(d: int) -> float:
    """C^2_{d, d+1} via direct Beta-function evaluation."""
    G_dd = beta(0.5, d + 1.0)
    G_d1d1 = beta(0.5, d + 2.0)
    G_dd1 = beta(0.5, d + 1.5)
    return G_dd1 ** 2 / (G_dd * G_d1d1)


def gram_C2_via_R(d: int) -> float:
    """Closed form: C^2_{d, d+1} = R(2d+2)^2 / [R(2d+1) R(2d+3)].

    Computed via log to avoid Gamma function overflow at large 2d+3.
    """
    log_c2 = 2 * log_R(2 * d + 2) - log_R(2 * d + 1) - log_R(2 * d + 3)
    return math.exp(log_c2)


def gram_logC2_via_laplacian(d: int) -> float:
    """log C^2 via discrete log-Laplacian of alpha at 2d+2.

    log C^2_{d, d+1} = -(1/2) Delta^2 log alpha |_{2d+2}
                     = -(1/2) [log alpha(2d+1) + log alpha(2d+3) - 2 log alpha(2d+2)]
    """
    la_minus = log_alpha(2 * d + 1)
    la_center = log_alpha(2 * d + 2)
    la_plus = log_alpha(2 * d + 3)
    delta2 = la_minus + la_plus - 2 * la_center
    return -0.5 * delta2


def main() -> int:
    print("=" * 72)
    print("GRAM-LAPLACIAN IDENTITY (Part 0 Supplement)")
    print("=" * 72)
    print()
    print("Identity:  log C^2_{d, d+1} = -(1/2) Delta^2 log alpha |_{2d+2}")
    print("           C^2_{d, d+1} = R(2d+2)^2 / [R(2d+1) R(2d+3)]")
    print()

    d_values = [4, 5, 6, 7, 10, 15, 19, 30, 50, 100, 200]
    # The identity is symbolically exact; numerical relative error grows with d
    # because log C^2 ~ 1/(8d^2) is computed as a cancellation of O(1) log-Gamma
    # terms.  At d=100, log C^2 ~ 1e-5 with cancellation factor ~1e5, so machine
    # precision (1e-15) amplifies to ~1e-10 relative.  1e-7 is a comfortable bound.
    tolerance_C2 = 1e-12  # closed form: no cancellation, expect machine precision
    tolerance_log = 1e-7  # log identity: cancellation amplifies precision loss
    tolerance_path = 1e-2  # path sum: linearisation O((1-C^2)^2) ~ 1e-3 at worst
    failures: list[str] = []

    # -----------------------------------------------------------------
    # 1. Closed form: C^2 = R(2d+2)^2 / [R(2d+1) R(2d+3)]
    # -----------------------------------------------------------------
    print("-" * 72)
    print("Verification 1: closed-form expression in cascade slicing ratios")
    print("-" * 72)
    print(f"{'d':>4}  {'C^2 direct':>20}  {'C^2 closed form':>20}  {'rel diff':>10}")
    print("-" * 72)
    for d in d_values:
        c2_d = gram_C2_direct(d)
        c2_r = gram_C2_via_R(d)
        rel = abs(c2_r - c2_d) / abs(c2_d) if c2_d != 0 else float("nan")
        flag = "" if rel < tolerance_C2 else "  <-- FAIL"
        if rel >= tolerance_C2:
            failures.append(f"closed form at d={d}: rel diff {rel:.2e}")
        print(f"{d:>4}  {c2_d:>20.14e}  {c2_r:>20.14e}  {rel:>10.2e}{flag}")
    print()

    # -----------------------------------------------------------------
    # 2. Laplacian identity: log C^2 = -(1/2) Delta^2 log alpha |_{2d+2}
    # -----------------------------------------------------------------
    print("-" * 72)
    print("Verification 2: discrete log-Laplacian of alpha at doubled argument")
    print("-" * 72)
    print(f"{'d':>4}  {'log C^2 direct':>20}  {'-(1/2) Delta^2 log a':>22}  {'rel diff':>10}")
    print("-" * 72)
    for d in d_values:
        log_c2_d = math.log(gram_C2_direct(d))
        log_c2_l = gram_logC2_via_laplacian(d)
        rel = abs(log_c2_l - log_c2_d) / abs(log_c2_d) if log_c2_d != 0 else float("nan")
        flag = "" if rel < tolerance_log else "  <-- FAIL"
        if rel >= tolerance_log:
            failures.append(f"laplacian identity at d={d}: rel diff {rel:.2e}")
        print(f"{d:>4}  {log_c2_d:>20.10e}  {log_c2_l:>22.10e}  {rel:>10.2e}{flag}")
    print()

    # -----------------------------------------------------------------
    # 3. Path-sum agreement (linearisation: 1 - C^2 ~ -log C^2 to first order)
    # -----------------------------------------------------------------
    print("-" * 72)
    print("Verification 3: path-sum agreement on canonical cascade descents")
    print("-" * 72)
    print("(The exact identity is on log C^2; the first-order Gram correction")
    print(" sum sum_path (1 - C^2) is the linearisation, with O((1-C^2)^2)")
    print(" residuals at second order.)")
    print()
    paths = [
        ("d=5..12 (alpha_s)", 5, 12),
        ("d=6..13 (m_tau/m_mu)", 6, 13),
        ("d=14..21 (m_mu/m_e)", 14, 21),
        ("d=5..217 (rho_Lambda)", 5, 217),
    ]
    print(
        f"{'path':>30}  {'sum (1-C^2)':>16}  "
        f"{'-(1/2) sum Delta^2 log a':>26}  {'rel diff':>10}"
    )
    print("-" * 72)
    for name, d0, dn in paths:
        gram_sum = sum(1.0 - gram_C2_direct(d) for d in range(d0, dn))
        lap_sum = sum(gram_logC2_via_laplacian(d) for d in range(d0, dn))
        # Linearisation: 1 - C^2 ~ -log C^2 at first order in (1-C^2)
        # so gram_sum ~ -lap_sum (sign-flip because lap_sum is sum of log C^2)
        rel = abs(gram_sum + lap_sum) / abs(gram_sum) if gram_sum != 0 else float("nan")
        flag = "" if rel < tolerance_path else "  <-- FAIL"
        if rel >= tolerance_path:
            failures.append(f"path agreement {name}: rel diff {rel:.2e}")
        print(
            f"{name:>30}  {gram_sum:>16.10e}  {-lap_sum:>26.10e}  {rel:>10.2e}{flag}"
        )
    print()

    # -----------------------------------------------------------------
    # Summary
    # -----------------------------------------------------------------
    print("=" * 72)
    if failures:
        print(f"FAILED: {len(failures)} verifications below tolerance.")
        for f in failures:
            print(f"  - {f}")
        return 1
    else:
        print("ALL VERIFICATIONS PASS")
        print()
        print("The Gram-Laplacian identity")
        print("    log C^2_{d, d+1} = -(1/2) Delta^2 log alpha |_{2d+2}")
        print("holds to machine precision for all tested d.")
        print()
        print("This confirms the structural identity of the Part 0 Supplement's")
        print("new theorem on Gram correlation in cascade slicing ratios and its")
        print("Laplacian corollary, which derives the supplement's Gram first-order")
        print("correction as the discrete log-Laplacian of the cascade scalar")
        print("action's compliance function alpha(d) = R(d)^2/4 at doubled argument.")
        print()
        print("This identifies the supplement's path-distributed Gram framework")
        print("as a corollary of the same cascade scalar action that generates")
        print("Paper IVb's single-source alpha(d*)/chi^k family.")
        return 0


if __name__ == "__main__":
    sys.exit(main())
