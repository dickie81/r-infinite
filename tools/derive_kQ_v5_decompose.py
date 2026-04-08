#!/usr/bin/env python3
"""
Decompose compound observables into their net cascade-path sensitivity.

Key insight: when an observable depends on multiple factors that share
cascade paths, the NET sensitivity to each step determines the correction.

Example: m_tau = (alpha_s * v / sqrt(2)) * exp(-Phi(5)) * (2*sqrt(pi))^{-2}
  - alpha_s = alpha_GUT * exp(+Phi_5->12) : +1 traversal of d=5-12
  - v = M_Pl * alpha_s * exp(-pi/alpha(5)) : +1 more traversal of d=5-12
  - exp(-Phi(5)) = exp(-p(5)) : -1 traversal of d=5
  Total: +2 traversals of d=5-12, -1 traversal of d=5

Net sensitivity at each step:
  d=5: 2-1 = +1 (appears in alpha_s path twice, cancelled once by exp(-Phi))
  d=6-12: +2 each (both alpha_s copies, no cancellation)

The propagator correction at step d is Omega_{d-1} * (1-C^2) / Omega_3.
The observable's total correction is: sum_d [multiplicity(d) * Omega_{d-1} * (1-C^2)] / Omega_3
"""

import numpy as np
from scipy.special import gamma, beta, psi as digamma

pi = np.pi


def omega(d):
    return 2.0 * pi**((d+1)/2.0) / gamma((d+1)/2.0)

def C_adj(d):
    G_dd = beta(0.5, d + 1.0)
    G_d1d1 = beta(0.5, d + 2.0)
    G_dd1 = beta(0.5, (2*d+1)/2.0 + 1.0)
    return G_dd1 / np.sqrt(G_dd * G_d1d1)

def overlap_deficit(d):
    return 1.0 - C_adj(d)**2

def p_decay(d):
    return 0.5 * digamma((d+1)/2.0) - 0.5*np.log(pi)


Omega_3 = omega(3)  # = 2*pi^2


def step_correction(d):
    """Per-step Omega-weighted correction: Omega_{d-1} * (1-C^2) / Omega_3"""
    return omega(d-1) * overlap_deficit(d) / Omega_3


# === Define net multiplicity for each observable ===
# The multiplicity m(d) at step d is: how many times does the observable's
# exponent traverse step d, with sign.
#
# For exp(n*Phi): m(d) = n at every d in the path
# For a product: add the multiplicities
# For a ratio: subtract the multiplicities

def make_multiplicity(terms):
    """
    Build multiplicity map from a list of (coefficient, d_start, d_end) terms.
    coefficient: how many times this path appears (+1 for exp(Phi), -1 for exp(-Phi))
    d_start, d_end: the path traversed (steps d_start to d_end-1)
    """
    mult = {}
    for coeff, d_start, d_end in terms:
        for d in range(d_start, d_end):
            mult[d] = mult.get(d, 0) + coeff
    return mult


def compute_correction(mult):
    """Total correction from a multiplicity map."""
    total = 0.0
    for d, m in mult.items():
        total += m * step_correction(d)
    return total


# === Observable decompositions ===
#
# alpha_s = alpha_GUT * exp(Phi(12->4))
#   Phi(12->4) = sum_{d=5}^{12} p(d)
#   Net: +1 traversal of d=5-12
#
# v = M_Pl * alpha_s * exp(-pi/alpha(5))
#   = M_Pl * alpha_GUT * exp(Phi(12->4)) * exp(-pi/alpha(5))
#   alpha(5) = N(5)^2/(4*pi), single layer, exact
#   Net: +1 traversal of d=5-12
#
# m_tau = alpha_s * v / sqrt(2) * exp(-Phi(5)) * (2*sqrt(pi))^{-2}
#   = alpha_GUT^2 * M_Pl * exp(2*Phi(12->4)) * exp(-pi/alpha(5)) / sqrt(2)
#     * exp(-Phi(5)) * (2*sqrt(pi))^{-2}
#   Phi(12->4) contributes +2 traversals of d=5-12
#   Phi(5) = p(5) contributes -1 traversal of d=5
#   Net: d=5 gets 2-1=+1, d=6-12 get +2 each
#
# m_mu = alpha_s * v / sqrt(2) * exp(-Phi(13)) * (2*sqrt(pi))^{-3}
#   Phi(12->4) contributes +2 traversals of d=5-12
#   Phi(13) = sum_{d=5}^{13} p(d) contributes -1 traversal of d=5-13
#   Net: d=5-12 get 2-1=+1 each, d=13 gets 0-1=-1
#   Wait: Phi(13) goes from d=5 to d=13
#   d=5: +2 (from alpha_s^2) -1 (from Phi(13)) = +1
#   d=6-12: +2 -1 = +1
#   d=13: 0 -1 = -1
#
# m_e = alpha_s * v / sqrt(2) * exp(-Phi(21)) * (2*sqrt(pi))^{-4}
#   d=5-12: +2 -1 = +1
#   d=13-21: 0 -1 = -1 each
#
# m_tau/m_mu = exp(Phi(13)-Phi(5)) * 2*sqrt(pi)
#   = exp(sum_{d=6}^{13} p(d)) * 2*sqrt(pi)
#   Net: +1 traversal of d=6-13
#
# m_mu/m_e = exp(Phi(21)-Phi(13)) * 2*sqrt(pi)
#   = exp(sum_{d=14}^{21} p(d)) * 2*sqrt(pi)
#   Net: +1 traversal of d=14-21
#
# ell_A: depends on H(z) which depends on Omega_m, Omega_Lambda, etc.
#   The path is d=5-12 but with integration weighting. Use multiplicity +1.
#
# m_W: depends on sin^2(theta_W) from GUT couplings, NOT simply a propagator.
#   Path d=5-12 but through the Weinberg angle. Use multiplicity +1.

observables = [
    ("alpha_s", 0.1159, 0.1179,
     [(+1, 5, 13)],  # +1 traversal d=5-12
     "alpha_GUT * exp(Phi_5->12)"),

    ("m_tau (MeV)", 1755.0, 1777.0,
     [(+2, 5, 13), (-1, 5, 6)],  # +2 from alpha_s^2, -1 from exp(-Phi(5))
     "alpha_s^2 * M_Pl * ... * exp(-Phi(5))"),

    ("v (GeV)", 240.8, 246.22,
     [(+1, 5, 13)],  # v contains one copy of alpha_s
     "M_Pl * alpha_s * exp(-pi/alpha(5))"),

    ("m_mu (MeV)", 106.2, 105.66,
     [(+2, 5, 13), (-1, 5, 14)],  # +2 from alpha_s^2, -1 from exp(-Phi(13))
     "alpha_s^2 * M_Pl * ... * exp(-Phi(13))"),

    ("m_e (MeV)", 0.514, 0.511,
     [(+2, 5, 13), (-1, 5, 22)],  # +2 from alpha_s^2, -1 from exp(-Phi(21))
     "alpha_s^2 * M_Pl * ... * exp(-Phi(21))"),

    ("m_tau/m_mu", 16.53, 16.82,
     [(+1, 6, 14)],  # exp(Delta_Phi) through d=6-13
     "exp(Phi(13)-Phi(5)) * 2*sqrt(pi)"),

    ("m_mu/m_e", 206.50, 206.77,
     [(+1, 14, 22)],  # exp(Delta_Phi) through d=14-21
     "exp(Phi(21)-Phi(13)) * 2*sqrt(pi)"),

    ("m_W (GeV)", 79.89, 80.38,
     [(+1, 5, 13)],  # single propagator path
     "m_Z * cos(theta_W), where theta_W from cascade descent"),

    ("ell_A", 297.6, 301.6,
     [(+1, 5, 13)],  # single propagator path
     "pi * D_M(z*) / r_d, descent through d=5-12"),
]


print("=" * 90)
print("DECOMPOSITION: NET CASCADE-PATH MULTIPLICITY")
print("=" * 90)

print(f"\n{'Observable':<14s}  {'Formula':<45s}")
print("-" * 65)
for name, Q0, Q_obs, terms, formula in observables:
    print(f"{name:<14s}  {formula:<45s}")
    mult = make_multiplicity(terms)
    for d in sorted(mult.keys()):
        if mult[d] != 0:
            sc = step_correction(d)
            print(f"    d={d:2d}: multiplicity={mult[d]:+d}  "
                  f"step_corr={sc:.6f}  contribution={mult[d]*sc:+.6f}")

print(f"\n{'='*90}")
print("RESULTS: DECOMPOSED OMEGA-WEIGHTED CORRECTION")
print(f"{'='*90}")

print(f"\n{'Observable':<14s}  {'delta_decomp':>12s}  {'delta_obs':>10s}  "
      f"{'Q_corr':>10s}  {'Q_obs':>10s}  {'Dev':>8s}")
print("-" * 70)

for name, Q0, Q_obs, terms, formula in observables:
    mult = make_multiplicity(terms)
    delta = compute_correction(mult)
    Q_corr = Q0 * (1.0 + delta)
    delta_obs = Q_obs / Q0 - 1.0
    dev = (Q_corr - Q_obs) / Q_obs * 100

    print(f"{name:<14s}  {delta:12.6f}  {delta_obs:10.6f}  "
          f"{Q_corr:10.4f}  {Q_obs:10.4f}  {dev:+7.3f}%")


# === Compare all correction methods ===
print(f"\n{'='*90}")
print("COMPARISON: ALL CORRECTION METHODS")
print(f"{'='*90}")

print(f"\n{'Observable':<14s}  {'Uncorrected':>11s}  {'Uniform':>8s}  "
      f"{'Omega(1x)':>9s}  {'Decomposed':>10s}")
print("-" * 60)

for name, Q0, Q_obs, terms, formula in observables:
    # Identify the primary path for uniform and omega(1x)
    # Use the first term's path
    d_s = min(d for _, ds, de in terms for d in range(ds, de))
    d_e = max(d for _, ds, de in terms for d in range(ds, de)) + 1

    corr_uni = sum(overlap_deficit(d) for d in range(d_s, d_e))
    corr_omega_1x = sum(step_correction(d) for d in range(d_s, d_e))
    mult = make_multiplicity(terms)
    corr_decomp = compute_correction(mult)

    dev_none = (Q0 - Q_obs) / Q_obs * 100
    dev_uni = (Q0*(1+corr_uni) - Q_obs) / Q_obs * 100
    dev_omega = (Q0*(1+corr_omega_1x) - Q_obs) / Q_obs * 100
    dev_decomp = (Q0*(1+corr_decomp) - Q_obs) / Q_obs * 100

    print(f"{name:<14s}  {dev_none:+10.2f}%  {dev_uni:+7.2f}%  "
          f"{dev_omega:+8.2f}%  {dev_decomp:+9.2f}%")

# RMS summary
print(f"\n{'RMS':<14s}  ", end="")
for method in ['none', 'uni', 'omega', 'decomp']:
    devs = []
    for name, Q0, Q_obs, terms, formula in observables:
        d_s = min(d for _, ds, de in terms for d in range(ds, de))
        d_e = max(d for _, ds, de in terms for d in range(ds, de)) + 1

        if method == 'none':
            Q_corr = Q0
        elif method == 'uni':
            corr = sum(overlap_deficit(d) for d in range(d_s, d_e))
            Q_corr = Q0 * (1 + corr)
        elif method == 'omega':
            corr = sum(step_correction(d) for d in range(d_s, d_e))
            Q_corr = Q0 * (1 + corr)
        elif method == 'decomp':
            mult = make_multiplicity(terms)
            corr = compute_correction(mult)
            Q_corr = Q0 * (1 + corr)

        devs.append((Q_corr - Q_obs) / Q_obs * 100)

    rms = np.sqrt(np.mean(np.array(devs)**2))
    print(f"{rms:10.3f}%  ", end="")
print()
