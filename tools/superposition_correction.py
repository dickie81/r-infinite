#!/usr/bin/env python3
"""
What if the cascade layers are in perfect superposition?

Independent-step: P_ind = prod_d integral f_d(x) dx  [each layer its own variable]
Perfect superposition: P_sup = integral prod_d f_d(x) dx  [shared variable]

f_d(x) = (1-x^2)^{d/2}

P_sup = integral (1-x^2)^{S/2} dx where S = sum of all d in the path
      = B(1/2, S/2 + 1)

P_ind = prod_d B(1/2, d/2 + 1)  [which is prod N(d) up to constants]

The correction delta = P_sup / P_ind - 1 measures the difference between
coherent and incoherent propagation through the cascade.
"""

import numpy as np
from scipy.special import gamma, beta

pi = np.pi


def omega(d):
    return 2.0 * pi**((d+1)/2.0) / gamma((d+1)/2.0)


def N_lapse(d):
    return np.sqrt(pi) * gamma((d+1)/2.0) / gamma((d+2)/2.0)


# === Compute independent product and superposition for each path ===

def independent_product(dims):
    """Product of individual integrals: prod B(1/2, d/2+1)"""
    return np.prod([beta(0.5, d/2.0 + 1.0) for d in dims])


def superposition_integral(dims):
    """Integral with shared variable: B(1/2, S/2+1) where S = sum(dims)"""
    S = sum(dims)
    return beta(0.5, S/2.0 + 1.0)


def coherence_ratio(dims):
    """P_sup / P_ind"""
    return superposition_integral(dims) / independent_product(dims)


# === Test paths ===
paths = [
    ("alpha_s",    list(range(5, 13)),  0.1159, 0.1179),
    ("m_tau/m_mu", list(range(6, 14)),  16.53,  16.82),
    ("m_mu/m_e",   list(range(14, 22)), 206.50, 206.77),
    ("m_tau",      list(range(5, 13)),  1755.0, 1777.0),
    ("v",          list(range(5, 13)),  240.8,  246.22),
    ("ell_A",      list(range(5, 13)),  297.6,  301.6),
    ("m_W",        list(range(5, 13)),  79.89,  80.38),
]

print("=" * 90)
print("INDEPENDENT vs SUPERPOSITION")
print("=" * 90)

print(f"\n{'Path':<14s}  {'dims':<12s}  {'S=sum(d)':>8s}  {'P_ind':>14s}  "
      f"{'P_sup':>14s}  {'Ratio':>10s}  {'delta':>10s}")
print("-" * 85)

for name, dims, Q0, Q_obs in paths:
    S = sum(dims)
    P_ind = independent_product(dims)
    P_sup = superposition_integral(dims)
    ratio = P_sup / P_ind
    delta = ratio - 1.0

    print(f"{name:<14s}  d={dims[0]:d}-{dims[-1]:<5d}  {S:8d}  "
          f"{P_ind:14.6e}  {P_sup:14.6e}  {ratio:10.6f}  {delta:+10.6f}")


# === The correction as interpolation between independent and superposition ===
print(f"\n{'='*90}")
print("THE CASCADE IS BETWEEN INDEPENDENT AND SUPERPOSITION")
print(f"{'='*90}")

print("""
The true cascade is neither fully independent (C=0) nor fully superposed (C=1).
The eigenvalue deficit epsilon = 0.008 means the layers are 99.2% coherent.

The correction should be an interpolation:
  P_true = P_ind * (P_sup/P_ind)^f  for some fraction f

Or equivalently:
  ln(P_true/P_ind) = f * ln(P_sup/P_ind)

What fraction f reproduces the observed corrections?
""")

print(f"\n{'Observable':<14s}  {'delta_ind':>10s}  {'delta_sup':>10s}  "
      f"{'delta_obs':>10s}  {'f':>8s}  {'Q_f':>10s}  {'Q_obs':>10s}  {'Dev':>8s}")
print("-" * 90)

fractions = []
for name, dims, Q0, Q_obs in paths:
    P_ind = independent_product(dims)
    P_sup = superposition_integral(dims)

    delta_sup = P_sup / P_ind - 1.0
    delta_obs = Q_obs / Q0 - 1.0

    # f = delta_obs / delta_sup (linear interpolation)
    if abs(delta_sup) > 1e-15:
        f = delta_obs / delta_sup
    else:
        f = 0.0

    Q_f = Q0 * (1.0 + f * delta_sup)
    dev = (Q_f - Q_obs) / Q_obs * 100

    fractions.append(f)
    print(f"{name:<14s}  {0.0:+10.6f}  {delta_sup:+10.6f}  "
          f"{delta_obs:+10.6f}  {f:8.4f}  {Q_f:10.4f}  {Q_obs:10.4f}  {dev:+7.3f}%")


# === Is f universal? ===
print(f"\n{'='*90}")
print("IS THE SUPERPOSITION FRACTION f UNIVERSAL?")
print(f"{'='*90}")

f_values = np.array(fractions)
print(f"\n  f values: {[f'{f:.4f}' for f in f_values]}")
print(f"  Mean: {np.mean(f_values):.4f}")
print(f"  Std:  {np.std(f_values):.4f}")
print(f"  Range: {np.min(f_values):.4f} to {np.max(f_values):.4f}")

# Exclude negative f values (m_mu, m_e have positive leading deviations)
positive_f = [f for f in f_values if f > 0]
if positive_f:
    print(f"\n  Positive f values: {[f'{f:.4f}' for f in positive_f]}")
    print(f"  Mean (positive): {np.mean(positive_f):.4f}")


# === Test universal f ===
print(f"\n{'='*90}")
print("TEST: UNIVERSAL SUPERPOSITION FRACTION")
print(f"{'='*90}")

for f_test_label, f_test in [
    ("mean(all)", np.mean(f_values)),
    ("mean(positive)", np.mean(positive_f) if positive_f else 0),
    ("epsilon (0.00816)", 0.00816),
    ("2*epsilon", 2 * 0.00816),
    ("lambda_2/n (0.00808)", 0.00808),
    ("1/(4*pi) = alpha_GUT", 1/(4*pi)),
]:
    print(f"\n  f = {f_test_label} = {f_test:.5f}:")
    print(f"  {'Observable':<14s}  {'Q_corr':>10s}  {'Q_obs':>10s}  {'Dev':>8s}")
    devs = []
    for name, dims, Q0, Q_obs in paths:
        P_ind = independent_product(dims)
        P_sup = superposition_integral(dims)
        delta_sup = P_sup / P_ind - 1.0
        Q_corr = Q0 * (1.0 + f_test * delta_sup)
        dev = (Q_corr - Q_obs) / Q_obs * 100
        devs.append(dev)
        print(f"  {name:<14s}  {Q_corr:10.4f}  {Q_obs:10.4f}  {dev:+7.3f}%")
    rms = np.sqrt(np.mean(np.array(devs)**2))
    print(f"  {'RMS:':<14s}  {rms:10.3f}%")


# === What IS the superposition ratio geometrically? ===
print(f"\n{'='*90}")
print("GEOMETRIC MEANING OF THE SUPERPOSITION RATIO")
print(f"{'='*90}")

for name, dims, Q0, Q_obs in paths:
    S = sum(dims)
    n = len(dims)
    d_mean = S / n

    print(f"\n  {name}: path d={dims[0]}-{dims[-1]}")
    print(f"    n = {n}, S = sum(d) = {S}, mean(d) = {d_mean:.1f}")
    print(f"    Superposition integral = B(1/2, {S/2+1:.0f})")
    print(f"    = integral of (1-x^2)^{S/2:.0f} dx")
    print(f"    Effective single layer at d_eff = {S:.0f}")
    print(f"    Omega_{S-1} = {omega(S-1):.6e}")
    print(f"    Product of individual Omega's: {np.prod([omega(d-1) for d in dims]):.6e}")
