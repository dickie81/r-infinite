#!/usr/bin/env python3
"""
Second-order correction with sphere-area (Omega) weighting.

Hypothesis: the observable's sensitivity to inter-layer coupling at step d
is proportional to the sphere area Omega_{d-1} — the cascade's content
at that level. Sphere areas are the unique independent cascade quantities
(Part 0, Corollary 3.2). The sensitivity should weight by content, not
by the decay rate p(d).

The first-order correction sum_adj(1-C^2) implicitly uses UNIFORM weighting.
The second-order correction should use the CONTENT-WEIGHTED overlap deficit.
"""

import numpy as np
from scipy.special import gamma, beta, psi as digamma

pi = np.pi


def omega(d):
    """Sphere area Omega_d = 2*pi^((d+1)/2) / Gamma((d+1)/2)"""
    return 2.0 * pi**((d + 1) / 2.0) / gamma((d + 1) / 2.0)


def C_adj(d):
    """Correlation between adjacent layers d and d+1."""
    G_dd = beta(0.5, d + 1.0)
    G_d1d1 = beta(0.5, d + 2.0)
    G_dd1 = beta(0.5, (2*d + 1) / 2.0 + 1.0)
    return G_dd1 / np.sqrt(G_dd * G_d1d1)


def overlap_deficit(d):
    return 1.0 - C_adj(d)**2


def lapse(d):
    """N(d) = sqrt(pi) * Gamma((d+1)/2) / Gamma((d+2)/2)"""
    return np.sqrt(pi) * gamma((d+1)/2.0) / gamma((d+2)/2.0)


def p_decay(d):
    """p(d) = (1/2)*psi((d+1)/2) - (1/2)*ln(pi)"""
    return 0.5 * digamma((d+1)/2.0) - 0.5 * np.log(pi)


# === Test cases ===
cases = [
    ("alpha_s",    list(range(5, 13)),  0.1159,  0.1179),
    ("ell_A",      list(range(5, 13)),  297.6,   301.6),
    ("m_tau/m_mu", list(range(6, 14)),  16.53,   16.82),
]


# === Various weighting schemes for the correction ===
print("=" * 80)
print("OMEGA-WEIGHTED CORRECTIONS")
print("=" * 80)

# The correction should be a WEIGHTED sum of per-step deficits:
#   delta_Q/Q_0 = sum_k w_k * (1 - C_{d_k,d_{k+1}}^2)
#
# where w_k is the weight of step k. Different weightings:

def uniform_weights(dims):
    """Uniform: w_k = 1 (the first-order formula)"""
    return np.ones(len(dims) - 1)

def omega_weights(dims):
    """Weight by sphere area at the step: Omega_{d-1}"""
    return np.array([omega(d - 1) for d in dims[:-1]])

def omega_geo_mean_weights(dims):
    """Weight by geometric mean of sphere areas at both ends of the step"""
    return np.array([np.sqrt(omega(d-1) * omega(d)) for d in dims[:-1]])

def omega_ratio_weights(dims):
    """Weight by ratio Omega_{d-1}/Omega_{d_0-1} (normalised to observer end)"""
    O_ref = omega(dims[0] - 1)
    return np.array([omega(d-1) / O_ref for d in dims[:-1]])

def lapse_weights(dims):
    """Weight by lapse function N(d)"""
    return np.array([lapse(d) for d in dims[:-1]])

def content_flow_weights(dims):
    """Weight by Omega_{d-1} * N(d) — content times propagation rate"""
    return np.array([omega(d-1) * lapse(d) for d in dims[:-1]])

def inv_omega_weights(dims):
    """Weight by 1/Omega_{d-1} — inverse content (amplification)"""
    return np.array([1.0/omega(d-1) for d in dims[:-1]])

def boundary_ratio_weights(dims):
    """Weight by boundary dominance ratio d/(d+1)"""
    return np.array([d / (d + 1.0) for d in dims[:-1]])

def p_weights(dims):
    """Weight by decay rate p(d)"""
    return np.array([p_decay(d) for d in dims[:-1]])


weighting_schemes = [
    ("uniform (1st order)",      uniform_weights),
    ("Omega_{d-1}",              omega_weights),
    ("sqrt(Omega_d * Omega_{d+1})", omega_geo_mean_weights),
    ("Omega/Omega_ref",          omega_ratio_weights),
    ("N(d) lapse",               lapse_weights),
    ("Omega * N(d)",             content_flow_weights),
    ("1/Omega_{d-1}",           inv_omega_weights),
    ("d/(d+1)",                  boundary_ratio_weights),
    ("p(d) decay rate",          p_weights),
]


def weighted_correction(dims, weight_fn):
    """Compute normalised weighted sum of overlap deficits."""
    w = weight_fn(dims)
    deficits = np.array([overlap_deficit(d) for d in dims[:-1]])

    # The weighted correction, normalised so that uniform weights
    # give the first-order formula
    n = len(dims) - 1
    correction = np.sum(w * deficits) / np.sum(w) * n
    return correction


print(f"\n{'Weighting':<30s}  ", end="")
for name, dims, Q0, Q_obs in cases:
    print(f"  {name:>12s}", end="")
print(f"  {'RMS dev':>8s}")
print("-" * 85)

for wname, wfn in weighting_schemes:
    devs = []
    print(f"{wname:<30s}  ", end="")
    for name, dims, Q0, Q_obs in cases:
        corr = weighted_correction(dims, wfn)
        Q_corr = Q0 * (1.0 + corr)
        dev = (Q_corr - Q_obs) / Q_obs * 100
        devs.append(dev)
        print(f"  {dev:+11.3f}%", end="")
    rms = np.sqrt(np.mean(np.array(devs)**2))
    print(f"  {rms:8.3f}%")

print(f"\n{'(observed)':30s}  ", end="")
for name, dims, Q0, Q_obs in cases:
    print(f"  {0.0:+11.3f}%", end="")
print()


# === Deep dive into the best Omega-based scheme ===
print(f"\n{'='*80}")
print("DETAILED: OMEGA-WEIGHTED CORRECTION")
print(f"{'='*80}")

for name, dims, Q0, Q_obs in cases:
    print(f"\n--- {name} (d={dims[0]}--{dims[-1]}) ---")

    # Per-step analysis
    print(f"  {'Step':>6s}  {'1-C^2':>10s}  {'Omega_{d-1}':>12s}  "
          f"{'w*(1-C^2)':>12s}  {'N(d)':>8s}")
    print(f"  {'-'*55}")

    deficits = []
    omegas = []
    for d in dims[:-1]:
        deficit = overlap_deficit(d)
        om = omega(d - 1)
        deficits.append(deficit)
        omegas.append(om)
        print(f"  d={d:2d}->{d+1:2d}  {deficit:10.6f}  {om:12.4f}  "
              f"{om*deficit:12.8f}  {lapse(d):8.5f}")

    deficits = np.array(deficits)
    omegas = np.array(omegas)
    n = len(deficits)

    uniform_corr = np.sum(deficits)
    omega_corr = np.sum(omegas * deficits) / np.sum(omegas) * n

    print(f"\n  Uniform correction:  {uniform_corr:.6f}")
    print(f"  Omega-weighted:      {omega_corr:.6f}")
    print(f"  Ratio Omega/uniform: {omega_corr/uniform_corr:.4f}")
    print(f"  Q_uniform:  {Q0*(1+uniform_corr):.4f}  (dev {(Q0*(1+uniform_corr)-Q_obs)/Q_obs*100:+.2f}%)")
    print(f"  Q_omega:    {Q0*(1+omega_corr):.4f}  (dev {(Q0*(1+omega_corr)-Q_obs)/Q_obs*100:+.2f}%)")
    print(f"  Q_observed: {Q_obs:.4f}")


# === Try combinations of uniform + omega ===
print(f"\n{'='*80}")
print("LINEAR COMBINATION: delta = a*uniform + b*omega_weighted")
print(f"{'='*80}")

# Compute uniform and omega corrections for each case
uni = []
ome = []
obs_delta = []
for name, dims, Q0, Q_obs in cases:
    u = sum(overlap_deficit(d) for d in dims[:-1])
    o = weighted_correction(dims, omega_weights)
    d = Q_obs/Q0 - 1.0
    uni.append(u)
    ome.append(o)
    obs_delta.append(d)

uni = np.array(uni)
ome = np.array(ome)
obs_delta = np.array(obs_delta)

# Solve: a*uni + b*ome = obs_delta (least squares with 3 equations, 2 unknowns)
A = np.column_stack([uni, ome])
result = np.linalg.lstsq(A, obs_delta, rcond=None)
a, b = result[0]

print(f"\n  Best fit: delta = {a:.4f} * uniform + {b:.4f} * omega_weighted")
print(f"\n  {'Observable':<14s}  {'Predicted':>10s}  {'Observed':>10s}  {'Dev':>8s}")
print(f"  {'-'*45}")
for i, (name, dims, Q0, Q_obs) in enumerate(cases):
    pred = a * uni[i] + b * ome[i]
    Q_pred = Q0 * (1.0 + pred)
    dev = (Q_pred - Q_obs) / Q_obs * 100
    print(f"  {name:<14s}  {Q_pred:10.4f}  {Q_obs:10.4f}  {dev:+7.3f}%")


# === Try: the correction IS the omega-weighted deficit (not normalised) ===
print(f"\n{'='*80}")
print("RAW OMEGA-WEIGHTED DEFICIT (unnormalised)")
print(f"{'='*80}")

for name, dims, Q0, Q_obs in cases:
    deficits = np.array([overlap_deficit(d) for d in dims[:-1]])
    omegas_raw = np.array([omega(d-1) for d in dims[:-1]])

    # Various normalisations
    raw = np.sum(omegas_raw * deficits)
    norm_by_omega4 = raw / omega(3)  # normalise by observer's sphere area
    norm_by_omega_start = raw / omega(dims[0] - 1)

    delta_obs = Q_obs/Q0 - 1.0
    print(f"\n  {name}:")
    print(f"    raw sum(Omega*deficit) = {raw:.6f}")
    print(f"    / Omega_3 (=2*pi^2)   = {norm_by_omega4:.6f}  (obs: {delta_obs:.6f})")
    print(f"    / Omega_{dims[0]-1}          = {norm_by_omega_start:.6f}  (obs: {delta_obs:.6f})")


# === The cascade-native formula: weight by Omega, normalise by Omega at observer ===
print(f"\n{'='*80}")
print("CANDIDATE: delta = sum[Omega_{d-1} * (1-C^2)] / Omega_3")
print(f"{'='*80}")

print(f"\n  Omega_3 = 2*pi^2 = {omega(3):.4f}")
print(f"\n  {'Observable':<14s}  {'Predicted':>10s}  {'Observed':>10s}  {'Dev':>8s}")
print(f"  {'-'*45}")
for name, dims, Q0, Q_obs in cases:
    deficits = np.array([overlap_deficit(d) for d in dims[:-1]])
    omegas_raw = np.array([omega(d-1) for d in dims[:-1]])
    pred_delta = np.sum(omegas_raw * deficits) / omega(3)
    Q_pred = Q0 * (1.0 + pred_delta)
    dev = (Q_pred - Q_obs) / Q_obs * 100
    print(f"  {name:<14s}  {Q_pred:10.4f}  {Q_obs:10.4f}  {dev:+7.3f}%")
