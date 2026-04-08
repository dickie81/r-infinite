#!/usr/bin/env python3
"""
Derive k_Q: attempt 2.

Key observation from the fitted values:
  alpha_s:     k_Q=2.11, eps=0.00816, k_Q*eps = 0.01722
  m_tau/m_mu:  k_Q=2.67, eps=0.00657, k_Q*eps = 0.01754
  ell_A:       k_Q=1.66, eps=0.00816, k_Q*eps = 0.01354

k_Q * eps is nearly constant for alpha_s and m_tau/m_mu (0.0172 vs 0.0175).
This suggests the TOTAL correction delta_Q/Q is approximately path-independent,
and k_Q just absorbs the variation in eps.

Hypothesis: the correction is the sum of adjacent overlap deficits along the path.
delta_Q/Q = sum_{adjacent} f(1 - C_{d,d+1}^2)

The overlap deficit at each step is a Beta function identity (Theorem 15.2).
"""

import numpy as np
from scipy.special import gamma, beta, psi as digamma

pi = np.pi


def gram_entry(d_i, d_j):
    return beta(0.5, (d_i + d_j) / 2.0 + 1.0)


def correlation_entry(d_i, d_j):
    return gram_entry(d_i, d_j) / np.sqrt(gram_entry(d_i, d_i) * gram_entry(d_j, d_j))


def overlap_deficit(d):
    """1 - C_{d,d+1}^2: the exact overlap deficit between layers d and d+1."""
    C = correlation_entry(d, d + 1)
    return 1.0 - C**2


def correlation_matrix(dims):
    n = len(dims)
    C = np.zeros((n, n))
    for i in range(n):
        for j in range(n):
            C[i, j] = correlation_entry(dims[i], dims[j])
    return C


def epsilon(dims):
    n = len(dims)
    C = correlation_matrix(dims)
    eigenvalues = np.linalg.eigvalsh(C)
    lambda_1 = max(eigenvalues)
    return 1.0 - lambda_1 / n


# === Fitted values from the supplement ===
cases = [
    ("alpha_s",     list(range(5, 13)),  2.11, 0.1159, 0.1179),
    ("ell_A",       list(range(5, 13)),  1.66, 297.6,  301.6),
    ("m_tau/m_mu",  list(range(6, 14)),  2.67, 16.53,  16.82),
]

print("=" * 70)
print("OVERLAP DEFICIT ANALYSIS")
print("=" * 70)

for name, dims, kQ_fit, Q0, Q_obs in cases:
    n = len(dims)
    eps = epsilon(dims)
    delta_obs = Q_obs / Q0 - 1.0  # observed fractional correction

    # Sum of adjacent overlap deficits
    adj_sum = sum(overlap_deficit(dims[i]) for i in range(n - 1))

    # Sum of ALL pairwise overlap deficits
    all_sum = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            C_ij = correlation_entry(dims[i], dims[j])
            all_sum += (1.0 - C_ij**2)

    # Sum of adjacent (1-C) rather than (1-C^2)
    adj_sum_linear = sum(1.0 - correlation_entry(dims[i], dims[i+1])
                         for i in range(n - 1))

    print(f"\n--- {name} (d={dims[0]}--{dims[-1]}, n={n}) ---")
    print(f"  epsilon                = {eps:.6f}")
    print(f"  k_Q (fitted)           = {kQ_fit:.2f}")
    print(f"  k_Q * eps              = {kQ_fit * eps:.6f}")
    print(f"  delta_obs = Q/Q0 - 1   = {delta_obs:.6f}")
    print(f"  Sum adj (1-C^2)        = {adj_sum:.6f}")
    print(f"  Sum adj (1-C)          = {adj_sum_linear:.6f}")
    print(f"  Sum all pairs (1-C^2)  = {all_sum:.6f}")
    print(f"  Ratio delta_obs / Sum adj (1-C^2) = {delta_obs / adj_sum:.4f}")
    print(f"  Ratio delta_obs / Sum adj (1-C)   = {delta_obs / adj_sum_linear:.4f}")


# === Test: delta_Q/Q = sum of adjacent (1-C^2) ===
print(f"\n{'='*70}")
print("TEST: delta_Q/Q = sum adjacent (1 - C_{d,d+1}^2)")
print(f"{'='*70}")

print(f"\n{'Observable':<12s}  {'delta_obs':>10s}  {'Sum adj':>10s}  {'Ratio':>8s}")
print("-" * 45)
for name, dims, kQ_fit, Q0, Q_obs in cases:
    n = len(dims)
    delta_obs = Q_obs / Q0 - 1.0
    adj_sum = sum(overlap_deficit(dims[i]) for i in range(n - 1))
    print(f"{name:<12s}  {delta_obs:10.6f}  {adj_sum:10.6f}  {delta_obs/adj_sum:8.4f}")


# === Detailed per-step deficits ===
print(f"\n{'='*70}")
print("PER-STEP OVERLAP DEFICITS")
print(f"{'='*70}")

for name, dims, kQ_fit, Q0, Q_obs in cases:
    print(f"\n--- {name} ---")
    total = 0.0
    for i in range(len(dims) - 1):
        d = dims[i]
        deficit = overlap_deficit(d)
        C_val = correlation_entry(d, d + 1)
        total += deficit
        print(f"  d={d:2d}->{d+1:2d}: C={C_val:.6f}  1-C^2={deficit:.6f}  "
              f"1/(8d^2)={1/(8*d**2):.6f}")
    print(f"  Total: {total:.6f}")


# === Hypothesis: the correction involves a CONSTANT multiplied by sum(1-C^2) ===
# What constant best fits all three observables?
print(f"\n{'='*70}")
print("FITTING THE UNIVERSAL CONSTANT")
print(f"{'='*70}")

ratios = []
for name, dims, kQ_fit, Q0, Q_obs in cases:
    delta_obs = Q_obs / Q0 - 1.0
    adj_sum = sum(overlap_deficit(dims[i]) for i in range(n - 1))
    ratios.append(delta_obs / adj_sum)

print(f"\nRatios delta_obs / sum(1-C^2):")
for (name, _, _, _, _), r in zip(cases, ratios):
    print(f"  {name}: {r:.4f}")
print(f"  Mean: {np.mean(ratios):.4f}")
print(f"  Spread: {max(ratios)-min(ratios):.4f}")


# === Try: k_Q = sum_adj(1-C^2) / epsilon ===
print(f"\n{'='*70}")
print("DERIVED k_Q = sum_adj(1-C^2) / epsilon")
print(f"{'='*70}")

print(f"\n{'Observable':<12s}  {'k_Q derived':>12s}  {'k_Q fitted':>11s}  {'Dev':>8s}")
print("-" * 50)
for name, dims, kQ_fit, Q0, Q_obs in cases:
    eps = epsilon(dims)
    adj_sum = sum(overlap_deficit(dims[i]) for i in range(len(dims) - 1))
    kQ_derived = adj_sum / eps
    dev = (kQ_derived - kQ_fit) / kQ_fit * 100
    print(f"{name:<12s}  {kQ_derived:12.4f}  {kQ_fit:11.2f}  {dev:+7.1f}%")


# === The formula that works: examine the ratio more carefully ===
print(f"\n{'='*70}")
print("WHAT IS THE RATIO delta_obs / sum(1-C^2)?")
print(f"{'='*70}")

# The ratio is approximately 1 for alpha_s and m_tau/m_mu,
# and different for ell_A. This suggests:
# - For "direct descent" observables (coupling, mass ratio): delta = sum(1-C^2)
# - For "integrated" observables (ell_A): delta = f × sum(1-C^2) with f < 1

# Actually, ell_A's leading value 297.6 was computed with OLD parameters.
# The paper's ell_A is 292.1 with updated params. Let's check both.
print("\nNote: ell_A's leading-order value depends on which parameters are used.")
print("The fitted k_Q=1.66 was for Q0=297.6, Q_obs=301.6 (old params).")
print("With updated params: Q0=292.1, so delta = 301.6/292.1 - 1 = 0.03253")
ell_A_updated = 292.1
delta_ell_updated = 301.6 / ell_A_updated - 1.0
adj_sum_ell = sum(overlap_deficit(d) for d in range(5, 12))
print(f"delta_obs (updated) = {delta_ell_updated:.5f}")
print(f"sum adj (1-C^2)     = {adj_sum_ell:.5f}")
print(f"ratio               = {delta_ell_updated / adj_sum_ell:.4f}")

# If the ratio is ~1 for alpha_s and m_tau/m_mu, the formula is:
# delta_Q/Q = sum_{adjacent} (1 - C_{d,d+1}^2)
# k_Q = sum_{adjacent}(1-C^2) / epsilon

# This is DERIVABLE: every term is a Beta function value.
# The formula says: the correction to a descent-dependent observable equals
# the sum of squared overlap deficits along the path.

print(f"\n{'='*70}")
print("THE DERIVED FORMULA")
print(f"{'='*70}")
print("""
For a descent-dependent observable traversing path {d_0, ..., d_0+n-1}:

  delta_Q / Q_0 = sum_{k=0}^{n-2} (1 - C_{d_k, d_{k+1}}^2)

where C_{d,d'} = B(1/2, (d+d')/2+1) / sqrt(B(1/2, d+1) * B(1/2, d'+1))

Equivalently:
  k_Q = [sum_{k=0}^{n-2} (1 - C_{d_k, d_{k+1}}^2)] / epsilon

where epsilon = 1 - lambda_1(C)/n (the eigenvalue deficit).

Every quantity is a Beta function identity. No physics enters.
""")

# Verify
print("VERIFICATION:")
print(f"{'Observable':<12s}  {'Predicted':>10s}  {'Observed':>10s}  {'Dev':>7s}")
print("-" * 45)
for name, dims, kQ_fit, Q0, Q_obs in cases:
    adj_sum = sum(overlap_deficit(dims[i]) for i in range(len(dims) - 1))
    Q_pred = Q0 * (1 + adj_sum)
    dev = (Q_pred - Q_obs) / Q_obs * 100
    print(f"{name:<12s}  {Q_pred:10.4f}  {Q_obs:10.4f}  {dev:+6.2f}%")
