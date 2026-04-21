#!/usr/bin/env python3
"""
Compute the first-order inter-layer correction for ALL descent-dependent
quantities in the cascade series.

Formula: delta_Q/Q_0 = sum_{adjacent} (1 - C_{d,d+1}^2)

where C_{d,d+1} = B(1/2,(2d+1)/2+1) / sqrt(B(1/2,d+1)*B(1/2,d+2))
"""

import numpy as np
from scipy.special import beta, psi as digamma

pi = np.pi


def C_adj(d):
    """Correlation between adjacent layers d and d+1."""
    G_dd = beta(0.5, d + 1.0)
    G_d1d1 = beta(0.5, d + 2.0)
    G_dd1 = beta(0.5, (2*d + 1) / 2.0 + 1.0)
    return G_dd1 / np.sqrt(G_dd * G_d1d1)


def overlap_deficit(d):
    """1 - C_{d,d+1}^2"""
    c = C_adj(d)
    return 1.0 - c**2


def path_correction(d_start, d_end):
    """Sum of adjacent overlap deficits for path d_start to d_end."""
    return sum(overlap_deficit(d) for d in range(d_start, d_end))


def epsilon(d_start, d_end):
    """Eigenvalue deficit for path. Perturbation theory formula."""
    n = d_end - d_start + 1
    dims = list(range(d_start, d_end + 1))
    total = 0.0
    for i in range(n):
        for j in range(i + 1, n):
            G_ij = beta(0.5, (dims[i] + dims[j]) / 2.0 + 1.0)
            G_ii = beta(0.5, dims[i] + 1.0)
            G_jj = beta(0.5, dims[j] + 1.0)
            C_ij = G_ij / np.sqrt(G_ii * G_jj)
            total += (1.0 - C_ij)
    return 2.0 * total / n**2


# === All descent-dependent quantities from the series ===
print("=" * 80)
print("FIRST-ORDER INTER-LAYER CORRECTIONS FOR ALL DESCENT QUANTITIES")
print("=" * 80)
print(f"\nFormula: delta_Q/Q_0 = sum_adj (1 - C_{{d,d+1}}^2) [Beta function identity]")

quantities = [
    # (name, path_start, path_end, Q0_leading, Q_observed, paper)
    ("alpha_s",      5, 12, 0.1159,  0.1179,  "IVb"),
    ("m_tau/m_mu",   6, 13, 16.53,   16.82,   "IVb"),
    ("m_mu/m_e",    14, 21, 206.50,  206.77,  "IVb"),
    ("m_tau (MeV)", 5, 12, 1755.0,  1777.0,  "IVb"),  # same path as alpha_s
    ("m_mu (MeV)",  5, 13, 106.2,   105.66,  "IVb"),  # d=5-13
    ("m_e (MeV)",   5, 21, 0.514,   0.511,   "IVb"),  # d=5-21
    ("v (GeV)",     5, 12, 240.8,   246.22,  "IVb"),  # same path as alpha_s
    ("m_W (GeV)",   5, 12, 79.89,   80.38,   "IVb"),
    ("Cabibbo",     12, 13, 13.26,   13.04,  "IVb"),  # single step
]

print(f"\n{'Quantity':<14s}  {'Path':<10s}  {'Correction':>10s}  {'Q0':>10s}  "
      f"{'Q_corr':>10s}  {'Q_obs':>10s}  {'Dev_before':>10s}  {'Dev_after':>10s}")
print("-" * 100)

for name, d_s, d_e, Q0, Q_obs, paper in quantities:
    corr = path_correction(d_s, d_e)
    Q_corr = Q0 * (1.0 + corr)
    dev_before = (Q0 - Q_obs) / Q_obs * 100
    dev_after = (Q_corr - Q_obs) / Q_obs * 100

    print(f"{name:<14s}  d={d_s:d}-{d_e:<5d}  {corr:10.5f}  {Q0:10.4f}  "
          f"{Q_corr:10.4f}  {Q_obs:10.4f}  {dev_before:+9.2f}%  {dev_after:+9.2f}%")


# === Summary table for the papers ===
print(f"\n{'='*80}")
print("SUMMARY: CORRECTED PREDICTIONS")
print(f"{'='*80}")

print(f"\n{'Quantity':<14s}  {'Leading':>10s}  {'Corrected':>10s}  {'Observed':>10s}  "
      f"{'Before':>8s}  {'After':>8s}")
print("-" * 65)

for name, d_s, d_e, Q0, Q_obs, paper in quantities:
    corr = path_correction(d_s, d_e)
    Q_corr = Q0 * (1.0 + corr)
    dev_before = (Q0 - Q_obs) / Q_obs * 100
    dev_after = (Q_corr - Q_obs) / Q_obs * 100
    print(f"{name:<14s}  {Q0:10.4f}  {Q_corr:10.4f}  {Q_obs:10.4f}  "
          f"{dev_before:+7.2f}%  {dev_after:+7.2f}%")


# === Per-step deficits for reference ===
print(f"\n{'='*80}")
print("PER-STEP OVERLAP DEFICITS (1 - C_{d,d+1}^2)")
print(f"{'='*80}")
print(f"{'d':>3s}  {'1-C^2':>12s}  {'1/(8d^2)':>12s}  {'Cumulative':>12s}")
print("-" * 45)
cumul = 0.0
for d in range(5, 22):
    deficit = overlap_deficit(d)
    approx = 1.0 / (8.0 * d**2)
    cumul += deficit
    print(f"{d:3d}  {deficit:12.6f}  {approx:12.6f}  {cumul:12.6f}")


# === The correction for Omega_m^Bott ===
print(f"\n{'='*80}")
print("NOTE ON OMEGA_M")
print(f"{'='*80}")
print("""
Omega_m = 1/pi (leading order, geometric) carries NO descent correction
(it's a single-step algebraic identity, not a multi-layer descent).

Omega_m^Bott = 0.31150 (descent-dependent) WOULD receive the correction,
but its path is the entire cascade d=5-217, making the sum of adjacent
deficits very small at high d (1-C^2 ~ 1/(8d^2) -> 0).

The full correction for d=5-217:
""")
full_corr = path_correction(5, 217)
print(f"  sum_adj(1-C^2) for d=5-217 = {full_corr:.6f}")
print(f"  Omega_m^Bott corrected = {0.31150 * (1 + full_corr):.5f}")
print(f"  Observed = 0.315")
print(f"  Deviation: {(0.31150*(1+full_corr) - 0.315)/0.315*100:+.2f}%")
