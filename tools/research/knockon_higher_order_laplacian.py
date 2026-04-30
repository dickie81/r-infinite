#!/usr/bin/env python3
"""
Item 7 + Item 8 from the knock-on assessment.

ITEM 7: k-step Gram-Laplacian identity.
========================================
Conjecture (generalisation of Cor 14.4):
   log C^2_{d, d+k}  =  -(1/2) Delta_k^2 log alpha |_{2d+k+1}
where  Delta_k^2 f|_n := f(n-k) + f(n+k) - 2 f(n)  is the k-step Laplacian
and    alpha(d) = R(d)^2 / 4  the cascade compliance.

The k=1 case is the adjacent-pair Gram-Laplacian identity (Cor 14.4 in
Part 0.0).  k >= 2 extends to non-adjacent pairs.

ITEM 8: cross-observable correlations.
======================================
For two cascade observables A, B sharing layers (e.g., both rooted in
the U(1) descent through d=14), their Gram corrections share off-diagonal
entries of the full correlation matrix C_{ij}.  Test:
  - For a pair of paths sharing >=1 layer, build the joint correlation
    matrix and inspect its eigenvalue structure.
  - The shared-eigenvector overlap quantifies the cancellation in
    ratios A/B vs the accumulation in products A*B.
  - Specific test: alpha_s (d=5..12) vs m_tau/m_mu (d=6..13), which
    share layers d=6..12.
"""

from __future__ import annotations

import math
import sys

import mpmath as mp  # type: ignore[import-not-found]
import numpy as np

mp.mp.dps = 50


def R_mp(d: int) -> mp.mpf:
    return mp.gamma(mp.mpf(d + 1) / 2) / mp.gamma(mp.mpf(d + 2) / 2)


def log_R_mp(d: int) -> mp.mpf:
    return mp.log(R_mp(d))


def log_alpha_mp(d: int) -> mp.mpf:
    """log alpha(d) = 2 log R(d) - 2 log 2."""
    return 2 * log_R_mp(d) - 2 * mp.log(2)


def log_C_squared(d_i: int, d_j: int) -> mp.mpf:
    """log C^2_{d_i, d_j} = 2 log R(d_i + d_j + 1) - log R(2 d_i + 1) - log R(2 d_j + 1)."""
    return 2 * log_R_mp(d_i + d_j + 1) - log_R_mp(2 * d_i + 1) - log_R_mp(2 * d_j + 1)


def step_k_laplacian_log_alpha(n: int, k: int) -> mp.mpf:
    """Delta_k^2 log alpha |_n = log alpha(n-k) + log alpha(n+k) - 2 log alpha(n)."""
    return log_alpha_mp(n - k) + log_alpha_mp(n + k) - 2 * log_alpha_mp(n)


def C_value(d_i: int, d_j: int) -> mp.mpf:
    """C_{d_i, d_j} = R(d_i+d_j+1) / sqrt(R(2 d_i+1) R(2 d_j+1))."""
    return R_mp(d_i + d_j + 1) / mp.sqrt(R_mp(2 * d_i + 1) * R_mp(2 * d_j + 1))


def main() -> int:
    print("=" * 78)
    print("KNOCK-ON ITEM 7: k-STEP GRAM-LAPLACIAN GENERALISATION")
    print("=" * 78)
    print()
    print("Conjecture: log C^2_{d, d+k} = -(1/2) Delta_k^2 log alpha |_{2d+k+1}")
    print()
    print("Verification across (d, k) cascade-physics samples:")
    print()
    print(f"{'d':>4} {'k':>3}  {'log C^2 (direct)':>22}  "
          f"{'-(1/2) Delta_k^2 log a':>26}  {'rel diff':>12}")
    print("-" * 78)
    failures = 0
    samples = [
        (5, 1), (5, 2), (5, 3), (5, 5), (5, 7),
        (10, 1), (10, 2), (10, 5), (10, 10),
        (14, 1), (14, 3), (14, 7),
        (19, 1), (19, 5), (19, 10),
        (50, 1), (50, 10),
        (100, 1), (100, 25),
    ]
    for d, k in samples:
        log_C2_direct = log_C_squared(d, d + k)
        center = 2 * d + k + 1
        lap = step_k_laplacian_log_alpha(center, k)
        predicted = -lap / 2
        rel = abs(log_C2_direct - predicted) / abs(log_C2_direct) if log_C2_direct != 0 else mp.mpf(0)
        flag = "" if float(rel) < 1e-30 else "  <-- FAIL"
        if float(rel) >= 1e-30:
            failures += 1
        print(f"{d:>4} {k:>3}  {mp.nstr(log_C2_direct, 14):>22}  "
              f"{mp.nstr(predicted, 14):>26}  {float(rel):>12.2e}{flag}")
    print()
    if failures == 0:
        print("k-step Gram-Laplacian identity verified to mpmath precision (50 digits).")
    else:
        print(f"FAIL: {failures} samples disagreed.")
        return 1
    print()

    # -----------------------------------------------------------------
    # Item 8: cross-observable correlations
    # -----------------------------------------------------------------
    print("=" * 78)
    print("KNOCK-ON ITEM 8: CROSS-OBSERVABLE CORRELATIONS")
    print("=" * 78)
    print()
    print("Test: two paths sharing layers have overlapping Gram corrections.")
    print()

    def build_C_subset(layers: list[int]) -> np.ndarray:
        """Build correlation matrix for an arbitrary set of cascade layers."""
        n = len(layers)
        log_C = np.empty((n, n))
        for i, d_i in enumerate(layers):
            for j, d_j in enumerate(layers):
                log_C[i, j] = float(log_C_squared(d_i, d_j) / 2)  # log C, not log C^2
        return np.exp(log_C)

    # Path A: alpha_s descent, d=5..12
    # Path B: m_tau/m_mu, d=6..13
    # Joint layers: union d=5..13
    print("Test 1: alpha_s (d=5..12) vs m_tau/m_mu (d=6..13)")
    print("  Shared layers: d=6..12 (7 layers); A-only: d=5; B-only: d=13.")
    layers_A = list(range(5, 13))   # 5..12
    layers_B = list(range(6, 14))   # 6..13
    layers_AB = sorted(set(layers_A) | set(layers_B))  # 5..13

    C_A = build_C_subset(layers_A)
    C_B = build_C_subset(layers_B)
    C_AB = build_C_subset(layers_AB)

    eigs_A = sorted(np.linalg.eigvalsh(C_A), reverse=True)
    eigs_B = sorted(np.linalg.eigvalsh(C_B), reverse=True)
    eigs_AB = sorted(np.linalg.eigvalsh(C_AB), reverse=True)

    eps_A = 1 - eigs_A[0] / len(layers_A)
    eps_B = 1 - eigs_B[0] / len(layers_B)
    eps_AB = 1 - eigs_AB[0] / len(layers_AB)

    print(f"  epsilon_A (alpha_s):       {eps_A:.6e}")
    print(f"  epsilon_B (m_tau/m_mu):    {eps_B:.6e}")
    print(f"  epsilon_AB (joint 9 layers): {eps_AB:.6e}")
    print(f"  Decoupled prediction (eps_A + eps_B - shared): would require independence")
    print()
    print(f"  Top 3 eigenvalues of joint:  {[f'{e:.4f}' for e in eigs_AB[:3]]}")
    print(f"  Sub-dominant ratio lambda_2/lambda_1: {eigs_AB[1]/eigs_AB[0]:.4e}")
    print()

    # Test the shared-correction hypothesis: the ratio (m_tau/m_mu)/alpha_s
    # would have a "cleaner" Gram correction than the absolute values, because
    # shared-layer corrections cancel.
    #
    # Specifically: if A = exp(sum_{d in path_A} (1-C^2_{d,d+1})) and similarly B,
    # then B/A = exp(sum_path_B - sum_path_A) which only retains layer-specific
    # contributions.  Test whether this cancellation is exact at first order.

    print("Test 2: ratio cancellation -- corrections to A, B, B/A")
    Gram_A = sum(1.0 - float(C_value(d, d + 1)) ** 2 for d in layers_A[:-1])
    Gram_B = sum(1.0 - float(C_value(d, d + 1)) ** 2 for d in layers_B[:-1])
    # Path for B/A: differ by removing d=5 and adding d=13 contributions.
    # In leading order: log(B/A)_Gram = Gram_B - Gram_A.
    # Direct computation of B/A Gram correction along the symmetric difference path:
    # Path A: 5-6, 6-7, 7-8, 8-9, 9-10, 10-11, 11-12   (7 transitions)
    # Path B: 6-7, 7-8, 8-9, 9-10, 10-11, 11-12, 12-13 (7 transitions)
    # Difference: A has 5-6 not in B; B has 12-13 not in A.
    # So Gram_B - Gram_A = (1 - C^2_{12,13}) - (1 - C^2_{5,6})
    diff_direct = (1.0 - float(C_value(12, 13)) ** 2) - (1.0 - float(C_value(5, 6)) ** 2)
    diff_predicted = Gram_B - Gram_A
    print(f"  Gram_A (alpha_s):          {Gram_A:.6e}")
    print(f"  Gram_B (m_tau/m_mu):       {Gram_B:.6e}")
    print(f"  Gram_B - Gram_A:           {diff_predicted:.6e}")
    print(f"  Direct: (1-C^2_{{12,13}}) - (1-C^2_{{5,6}}): {diff_direct:.6e}")
    print(f"  Match: {abs(diff_predicted - diff_direct):.2e} (should be 0 at adjacent-only level)")
    print()
    print("  Interpretation: ratios of observables on overlapping cascade paths")
    print("  inherit ONLY the symmetric-difference Gram correction.  The shared")
    print("  layers contribute identically to A and B and cancel in B/A.")
    print()

    # Test 3: structural prediction for two-path observable correlations.
    # If A = e^{Phi(d_A)} and B = e^{Phi(d_B)} are descent-multiplicative observables
    # rooted at distinguished layer d^*, then the residual Gram correction on the
    # ratio only depends on the disjoint-path layers.
    print("Test 3: residuals' shared-layer structure")
    print("  For shared U(1) layer d*=14, observables routed through d=14:")
    print()
    test_pairs = [
        ("alpha_s (5..12)", "m_tau/m_mu (6..13)", list(range(5, 13)), list(range(6, 14))),
        ("alpha_s (5..12)", "ell_A (5..12)", list(range(5, 13)), list(range(5, 13))),
        ("m_mu/m_e (14..21)", "m_tau/m_mu (6..13)", list(range(14, 22)), list(range(6, 14))),
    ]
    for name_A, name_B, path_A, path_B in test_pairs:
        shared = set(path_A) & set(path_B)
        only_A = set(path_A) - set(path_B)
        only_B = set(path_B) - set(path_A)
        # Compute pair correlations across paths
        cross_corr = []
        for d_a in path_A:
            for d_b in path_B:
                cross_corr.append(float(C_value(d_a, d_b)))
        avg_cross = sum(cross_corr) / len(cross_corr)
        max_cross_offdiag = max(c for c in cross_corr if c < 0.999999)
        print(f"  {name_A} vs {name_B}:")
        print(f"    shared={len(shared)}, only A={len(only_A)}, only B={len(only_B)}")
        print(f"    avg cross-path C_{{ij}}: {avg_cross:.4f}")
        print(f"    max off-diag cross C_{{ij}}: {max_cross_offdiag:.6f}")
    print()

    print("=" * 78)
    print("CONCLUSIONS")
    print("=" * 78)
    print()
    print("Item 7 (k-step Gram-Laplacian identity): VERIFIED to mpmath precision.")
    print("  log C^2_{d, d+k} = -(1/2) Delta_k^2 log alpha |_{2d+k+1}")
    print("  Center shifts to 2d+k+1; step is k.  k=1 reproduces Cor 14.4.")
    print("  This is a genuine new structural identity extending the adjacent")
    print("  Gram-Laplacian to non-adjacent pairs.")
    print()
    print("Item 8 (cross-observable correlations): partial.")
    print("  Shared-layer cancellation in ratios is a CLEAN observation:")
    print("  the symmetric-difference path determines the joint Gram correction.")
    print("  Cross-path off-diagonal C_{ij} entries are computable but their")
    print("  physical interpretation as 'observable correlations' is non-trivial:")
    print("  the cascade predicts forced VALUES, not joint distributions.")
    print("  A genuine prediction would be: residuals after Gram correction")
    print("  satisfy a structural relation tied to the shared-layer structure.")
    print("  Untested in this script -- requires domain-specific observable")
    print("  modelling.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
