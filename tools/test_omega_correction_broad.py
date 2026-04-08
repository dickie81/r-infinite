#!/usr/bin/env python3
"""
Broad test of the Omega-weighted propagator correction.

Formula: delta_Q/Q_0 = sum[Omega_{d-1} * (1-C_{d,d+1}^2)] / Omega_3

Test against ALL descent-dependent quantities in the series.
Key question: does the propagator formula work for direct propagator
quantities, and does the +/-0.4% pattern persist for indirect ones?
"""

import numpy as np
from scipy.special import gamma, beta

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


def uniform_correction(d_start, d_end):
    """First-order: sum(1-C^2) [uniform weighting]"""
    return sum(overlap_deficit(d) for d in range(d_start, d_end))


def omega_correction(d_start, d_end):
    """Second-order: sum[Omega_{d-1} * (1-C^2)] / Omega_3"""
    Omega_3 = omega(3)  # = 2*pi^2, observer's sphere area
    total = sum(omega(d - 1) * overlap_deficit(d) for d in range(d_start, d_end))
    return total / Omega_3


# === ALL descent-dependent quantities ===
# (name, path_start, path_end, Q0, Q_obs, type)
# type: "propagator" = direct exp(Phi), "ratio" = ratio of propagators,
#       "integrated" = involves integral, "product" = compound

quantities = [
    # Direct propagator quantities (Q = const * exp(Phi))
    ("alpha_s",       5, 12, 0.1159,  0.1179,  "propagator"),
    ("m_tau (MeV)",   5, 12, 1755.0,  1777.0,  "propagator"),  # alpha_s * v * propagator
    ("v (GeV)",       5, 12, 240.8,   246.22,  "propagator"),  # M_Pl * alpha_s * exp(-pi/alpha(5))

    # Mass ratios (ratio of propagators * topological factor)
    ("m_tau/m_mu",    6, 13, 16.53,   16.82,   "ratio"),
    ("m_mu/m_e",     14, 21, 206.50,  206.77,  "ratio"),

    # Absolute masses with longer paths
    ("m_mu (MeV)",    5, 13, 106.2,   105.66,  "product"),  # propagator d=5-13
    ("m_e (MeV)",     5, 21, 0.514,   0.511,   "product"),  # propagator d=5-21

    # Integrated / compound quantities
    ("ell_A",         5, 12, 297.6,   301.6,   "integrated"),
    ("m_W (GeV)",     5, 12, 79.89,   80.38,   "propagator"),

    # Cosmological descent quantities
    ("Omega_m^Bott",  5, 217, 0.31150, 0.315,  "integrated"),
]


print("=" * 100)
print("BROAD TEST: OMEGA-WEIGHTED PROPAGATOR CORRECTION")
print("=" * 100)
print(f"\nOmega_3 = 2*pi^2 = {omega(3):.4f}")
print(f"\nFormula: delta = sum[Omega_{{d-1}} * (1-C^2)] / Omega_3")

print(f"\n{'Quantity':<14s}  {'Type':<12s}  {'Path':<10s}  "
      f"{'Uniform':>8s}  {'Omega':>8s}  "
      f"{'Q0':>10s}  {'Q_uni':>10s}  {'Q_omega':>10s}  {'Q_obs':>10s}  "
      f"{'Dev_uni':>8s}  {'Dev_omega':>8s}")
print("-" * 120)

results_by_type = {}

for name, d_s, d_e, Q0, Q_obs, qtype in quantities:
    corr_uni = uniform_correction(d_s, d_e)
    corr_omega = omega_correction(d_s, d_e)

    Q_uni = Q0 * (1.0 + corr_uni)
    Q_omega = Q0 * (1.0 + corr_omega)

    dev_uni = (Q_uni - Q_obs) / Q_obs * 100
    dev_omega = (Q_omega - Q_obs) / Q_obs * 100

    print(f"{name:<14s}  {qtype:<12s}  d={d_s:d}-{d_e:<5d}  "
          f"{corr_uni:8.5f}  {corr_omega:8.5f}  "
          f"{Q0:10.4f}  {Q_uni:10.4f}  {Q_omega:10.4f}  {Q_obs:10.4f}  "
          f"{dev_uni:+7.2f}%  {dev_omega:+7.2f}%")

    if qtype not in results_by_type:
        results_by_type[qtype] = []
    results_by_type[qtype].append({
        'name': name, 'dev_uni': dev_uni, 'dev_omega': dev_omega,
        'corr_uni': corr_uni, 'corr_omega': corr_omega,
    })


# === Summary by type ===
print(f"\n{'='*100}")
print("SUMMARY BY OBSERVABLE TYPE")
print(f"{'='*100}")

for qtype, results in results_by_type.items():
    devs_uni = [r['dev_uni'] for r in results]
    devs_omega = [r['dev_omega'] for r in results]
    rms_uni = np.sqrt(np.mean(np.array(devs_uni)**2))
    rms_omega = np.sqrt(np.mean(np.array(devs_omega)**2))

    print(f"\n  {qtype.upper()} (n={len(results)}):")
    print(f"    {'Quantity':<14s}  {'Uniform':>8s}  {'Omega':>8s}")
    for r in results:
        print(f"    {r['name']:<14s}  {r['dev_uni']:+7.2f}%  {r['dev_omega']:+7.2f}%")
    print(f"    {'RMS:':<14s}  {rms_uni:7.2f}%  {rms_omega:7.2f}%")


# === Detailed path analysis for longer paths ===
print(f"\n{'='*100}")
print("PATH ANALYSIS: OMEGA-WEIGHTED DEFICIT ACCUMULATION")
print(f"{'='*100}")

Omega_3 = omega(3)
for path_label, d_s, d_e in [("d=5-12 (alpha_s)", 5, 12),
                               ("d=6-13 (m_tau/m_mu)", 6, 13),
                               ("d=14-21 (m_mu/m_e)", 14, 21),
                               ("d=5-13 (m_mu)", 5, 13),
                               ("d=5-21 (m_e)", 5, 21)]:
    print(f"\n  {path_label}:")
    cum_uni = 0.0
    cum_omega = 0.0
    for d in range(d_s, d_e):
        deficit = overlap_deficit(d)
        om = omega(d - 1)
        cum_uni += deficit
        cum_omega += om * deficit / Omega_3
        if d < d_s + 3 or d >= d_e - 3 or d_e - d_s <= 8:
            print(f"    d={d:3d}: 1-C^2={deficit:.6f}  "
                  f"Omega_{d-1:d}={om:10.4f}  "
                  f"cum_uni={cum_uni:.6f}  cum_omega={cum_omega:.6f}")
        elif d == d_s + 3:
            print(f"    ...")
    print(f"    Total: uniform={cum_uni:.6f}, omega={cum_omega:.6f}, "
          f"ratio={cum_omega/cum_uni:.4f}")


# === The critical comparison ===
print(f"\n{'='*100}")
print("THE CRITICAL QUESTION: PROPAGATOR vs NON-PROPAGATOR")
print(f"{'='*100}")

print("""
If the Omega-weighted formula is the PROPAGATOR correction, then:
  - Direct propagator quantities should match to ~0.01%
  - Indirect quantities should have systematic residuals

Results:
""")

propagator_devs = []
non_propagator_devs = []

for name, d_s, d_e, Q0, Q_obs, qtype in quantities:
    corr = omega_correction(d_s, d_e)
    Q_corr = Q0 * (1.0 + corr)
    dev = (Q_corr - Q_obs) / Q_obs * 100

    if qtype == "propagator":
        propagator_devs.append((name, dev))
    else:
        non_propagator_devs.append((name, dev))

print(f"  DIRECT PROPAGATOR quantities:")
for name, dev in propagator_devs:
    print(f"    {name:<14s}  {dev:+7.3f}%")
rms_prop = np.sqrt(np.mean([d**2 for _, d in propagator_devs]))
print(f"    {'RMS:':<14s}  {rms_prop:7.3f}%")

print(f"\n  NON-PROPAGATOR quantities:")
for name, dev in non_propagator_devs:
    print(f"    {name:<14s}  {dev:+7.3f}%")
rms_non = np.sqrt(np.mean([d**2 for _, d in non_propagator_devs]))
print(f"    {'RMS:':<14s}  {rms_non:7.3f}%")

print(f"\n  Improvement factor: {rms_non/rms_prop:.1f}x worse for non-propagator")
print(f"  (Expected: non-propagator should be systematically worse)")
