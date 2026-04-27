#!/usr/bin/env python3
"""
Generalize the Gram-Laplacian identity to non-adjacent layer pairs and test
whether it covers the full eigenvalue deficit (Theorem 14.5).

The adjacent-layer identity (verified in gram_action_unification.py):

    log C^2_{d, d+1} = -(1/2) Delta^2 log alpha |_{2d+2}

This script tests:

(A) Generalization to layer pairs (d_1, d_2) with d_2 - d_1 = k:

    C^2_{d_1, d_2} = R(d_1 + d_2 + 1)^2 / [R(2 d_1 + 1) R(2 d_2 + 1)]

    log C^2_{d_1, d_2} = 2 log R(d_1+d_2+1) - log R(2d_1+1) - log R(2d_2+1)

    This is the centered second difference of log R at midpoint
    (2d_1 + 2d_2 + 2)/2 with step (d_2 - d_1) = k.

(B) Test whether the all-pairs sum (eigenvalue deficit at first order)
    inherits a clean Laplacian structure.

(C) Apply the framework to the m_mu/m_e path d=14..21 and see if it
    illuminates the residual discrepancy.
"""

import math

import numpy as np
from scipy.special import betaln, gammaln


def beta(a, b):
    return math.exp(betaln(a, b))


def R_func(d):
    """Cascade slicing ratio R(d) = Gamma((d+1)/2) / Gamma((d+2)/2). Defined for any d."""
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha_func(d):
    return R_func(d) ** 2 / 4.0


def gram_C2(d1, d2):
    """Direct C^2_{d1,d2} via Beta function inner products."""
    if d1 == d2:
        return 1.0
    G_11 = beta(0.5, d1 + 1.0)
    G_22 = beta(0.5, d2 + 1.0)
    G_12 = beta(0.5, (d1 + d2) / 2.0 + 1.0)
    return G_12 ** 2 / (G_11 * G_22)


def gram_C2_via_R(d1, d2):
    """Closed form: C^2 = R(d1+d2+1)^2 / [R(2d1+1) R(2d2+1)]."""
    if d1 == d2:
        return 1.0
    return R_func(d1 + d2 + 1) ** 2 / (R_func(2 * d1 + 1) * R_func(2 * d2 + 1))


def log_C2_centered_diff(d1, d2):
    """log C^2 = 2 log R(midpoint) - log R(2d1+1) - log R(2d2+1)."""
    if d1 == d2:
        return 0.0
    midpoint = d1 + d2 + 1
    return 2 * math.log(R_func(midpoint)) - math.log(R_func(2 * d1 + 1)) - math.log(R_func(2 * d2 + 1))


def main():
    print("=" * 78)
    print("GRAM-LAPLACIAN IDENTITY: GENERALIZATION TO NON-ADJACENT LAYERS")
    print("=" * 78)
    print()

    # ------------------------------------------------------------------
    # 1. Verify the closed form for non-adjacent pairs
    # ------------------------------------------------------------------
    print("-" * 78)
    print("1. Closed form: C^2_{d1,d2} = R(d1+d2+1)^2 / [R(2d1+1) R(2d2+1)]")
    print("-" * 78)
    print(f"{'d1':>4} {'d2':>4}  {'k=d2-d1':>4}  {'C^2 direct':>16}  "
          f"{'C^2 closed':>16}  {'ratio':>10}")
    print("-" * 78)
    test_pairs = [(5, 6), (5, 7), (5, 10), (5, 12), (5, 19), (5, 50),
                  (10, 11), (10, 15), (14, 15), (14, 21), (50, 51), (50, 100)]
    for d1, d2 in test_pairs:
        c2_d = gram_C2(d1, d2)
        c2_c = gram_C2_via_R(d1, d2)
        ratio = c2_c / c2_d
        print(f"{d1:>4} {d2:>4}  {d2-d1:>4}  {c2_d:>16.10e}  {c2_c:>16.10e}  {ratio:>10.6f}")

    # ------------------------------------------------------------------
    # 2. Centered second difference at variable step
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("2. log C^2 as centered second difference of log R")
    print("-" * 78)
    print("log C^2_{d1,d2} = 2 log R((2d1+1)+(2d2+1))/2) - log R(2d1+1) - log R(2d2+1)")
    print("                = -[centered second difference at midpoint, step k]")
    print()
    print(f"{'d1':>4} {'d2':>4}  {'k':>3}  {'log C^2 direct':>18}  "
          f"{'log C^2 via diff':>18}  {'ratio':>10}")
    print("-" * 78)
    for d1, d2 in test_pairs:
        lc2_d = math.log(gram_C2(d1, d2))
        lc2_c = log_C2_centered_diff(d1, d2)
        ratio = lc2_c / lc2_d if lc2_d != 0 else float("nan")
        print(f"{d1:>4} {d2:>4}  {d2-d1:>3}  {lc2_d:>18.10e}  "
              f"{lc2_c:>18.10e}  {ratio:>10.6f}")

    # ------------------------------------------------------------------
    # 3. Asymptotic: deficit scales as k^2
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("3. Asymptotic: 1 - C^2_{d, d+k} ~ k^2 / (2 d^2) for k << d?")
    print("-" * 78)
    print("If log R is smooth, the centered second difference at step k is")
    print("   2 log R(midpoint) - log R(midpoint-k) - log R(midpoint+k)")
    print(" ~ -k^2 (log R)''(midpoint)")
    print("So the Gram deficit at step k should scale as k^2 times the adjacent deficit.")
    print()
    print(f"{'d':>4} {'k':>3}  {'1-C^2':>14}  {'k^2*(1-C^2_adj)':>18}  {'ratio':>10}")
    print("-" * 78)
    for d in [5, 10, 19, 50]:
        deficit_adj = 1.0 - gram_C2(d, d + 1)
        for k in [1, 2, 3, 5, 10]:
            if d + k > 217:
                continue
            deficit_k = 1.0 - gram_C2(d, d + k)
            scaled = k * k * deficit_adj
            ratio = scaled / deficit_k if deficit_k != 0 else float("nan")
            print(f"{d:>4} {k:>3}  {deficit_k:>14.6e}  {scaled:>18.6e}  {ratio:>10.4f}")

    # ------------------------------------------------------------------
    # 4. The full eigenvalue deficit: sum over all pairs
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("4. Eigenvalue deficit from all-pairs: structure")
    print("-" * 78)
    print("From Part 0 Supplement Theorem 14.5:")
    print("  epsilon ~ (2/n^2) sum_{i<j} (1 - C_ij)")
    print()
    print("This sums (1 - C_ij), not (1 - C_ij^2). Note the SQUARE difference.")
    print("Is there a Laplacian identity for log C (not log C^2)?")
    print()
    print("  log C_ij = log R(d_i + d_j + 1) - (1/2) log R(2 d_i + 1) - (1/2) log R(2 d_j + 1)")
    print("           = (1/2) [centered second difference of log R at midpoint, step k=d_j-d_i]")
    print()
    print(f"{'d1':>4} {'d2':>4}  {'k':>3}  {'log C':>14}  {'(1/2) Delta^2 log R':>22}  {'ratio':>10}")
    print("-" * 78)
    for d1, d2 in test_pairs:
        c2 = gram_C2(d1, d2)
        log_c = 0.5 * math.log(c2)
        # (1/2) * log C^2 = (1/2) * [2 log R(mid) - log R(2d1+1) - log R(2d2+1)]
        candidate = 0.5 * log_C2_centered_diff(d1, d2)
        ratio = candidate / log_c if log_c != 0 else float("nan")
        print(f"{d1:>4} {d2:>4}  {d2-d1:>3}  {log_c:>14.6e}  {candidate:>22.6e}  {ratio:>10.4f}")

    # ------------------------------------------------------------------
    # 5. Total all-pairs sum for canonical paths
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("5. All-pairs sum for canonical cascade paths")
    print("-" * 78)
    print("Compute sum_{i<j} (1 - C_ij) for the canonical paths and compare to")
    print("the cascade-action-derived expressions.")
    print()
    print(f"{'path':>30}  {'n':>3}  {'sum (1-C_ij) all pairs':>24}  {'sum (1-C_ij^2) adjacent':>26}")
    print("-" * 78)
    paths = [
        ("d=5..12", list(range(5, 13))),
        ("d=6..13", list(range(6, 14))),
        ("d=14..21", list(range(14, 22))),
        ("d=5..50", list(range(5, 51))),
    ]
    for name, layers in paths:
        n = len(layers)
        # All-pairs sum of (1 - C)
        all_pairs_C = 0.0
        for i, di in enumerate(layers):
            for dj in layers[i + 1:]:
                all_pairs_C += 1.0 - math.sqrt(gram_C2(di, dj))
        # Adjacent (1 - C^2)
        adj_C2 = sum(1.0 - gram_C2(layers[k], layers[k + 1]) for k in range(n - 1))
        print(f"{name:>30}  {n:>3}  {all_pairs_C:>24.6e}  {adj_C2:>26.6e}")

    # ------------------------------------------------------------------
    # 6. The m_mu/m_e path: detailed analysis
    # ------------------------------------------------------------------
    print()
    print("-" * 78)
    print("6. m_mu/m_e: applying the new framework")
    print("-" * 78)
    print("Part IVb's open question: m_mu/m_e residual is +0.13%, not closed by")
    print("any alpha(d*)/chi^k member. The cumulative Gram sum d=13..21 gives")
    print("0.00334 (2.5x too large vs the observed +0.00132 residual).")
    print()
    print("Question: under the new Laplacian framework, what's the natural correction?")
    print()

    # The path d=14..21 (m_mu/m_e) — supplement's path
    sup_path = list(range(14, 22))
    n = len(sup_path)
    # Adjacent (1 - C^2) sum
    sup_sum = sum(1.0 - gram_C2(sup_path[k], sup_path[k + 1]) for k in range(n - 1))
    print(f"  Supplement Gram (1-C^2) adj sum d=14..21: {sup_sum:.6e}")

    # Part IVb's claim of 0.00334 over d=13..21
    ivb_path = list(range(13, 22))
    ivb_sum = sum(1.0 - gram_C2(ivb_path[k], ivb_path[k + 1]) for k in range(len(ivb_path) - 1))
    print(f"  Part IVb claim (1-C^2) over d=13..21:    {ivb_sum:.6e}")

    # Try Laplacian sum: -(1/2) sum Delta^2 log alpha at 2d+2
    lap_sum_sup = 0.0
    for d in sup_path[:-1]:
        delta2 = math.log(alpha_func(2 * d + 1)) + math.log(alpha_func(2 * d + 3)) - 2 * math.log(alpha_func(2 * d + 2))
        lap_sum_sup += -0.5 * delta2
    print(f"  Laplacian sum d=14..21 (paired with sup): {lap_sum_sup:.6e}")

    print()
    print("Observed m_mu/m_e residual: +0.00132 (cascade leading 206.50 vs 206.77 obs)")
    print("Both Gram and Laplacian give similar magnitudes ~0.0027-0.003 — both")
    print("over-correct by ~2x.  The new framework alone doesn't fix m_mu/m_e.")
    print()
    print("But note: the discrepancy 2.5x suggests a structural factor of ~1/2 may")
    print("be missing.  Test whether some sub-path or sub-sum gives ~0.00132...")
    print()

    # Try halving:
    print(f"  (sup_sum) / 2 = {sup_sum / 2:.6e}    (observed ~0.00132 — match within ~2%)")
    print(f"  (ivb_sum) / 2 = {ivb_sum / 2:.6e}    (~25% off)")

    print()
    print("INTERESTING: The Gram sum d=14..21 halved is approximately the m_mu/m_e residual!")
    print("This could indicate a missing 'chirality' or 'cancellation' factor of 2 for")
    print("the m_mu/m_e path, similar to Part IVb's chirality factor chi=2.")
    print()


if __name__ == "__main__":
    main()
