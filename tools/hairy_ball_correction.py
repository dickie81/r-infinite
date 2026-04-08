#!/usr/bin/env python3
"""
Hairy ball modulation of the inter-layer correction.

At each cascade step d, the sphere S^{d-1} is:
  - Even-dimensional (d odd): hairy ball theorem forces a zero
  - Odd-dimensional (d even): smooth, no forced zero

The topological obstruction at hairy ball steps should modulate the
inter-layer correction. At a zero, the propagator is disrupted —
the coherent channel is partially blocked.

The Omega-weighted correction without hairy ball is:
  delta = sum Omega_{d-1} * (1-C^2) / Omega_3

With hairy ball modulation:
  delta = sum Omega_{d-1} * (1-C^2) * h(d) / Omega_3

where h(d) depends on whether S^{d-1} has a forced zero.
"""

import numpy as np
from scipy.special import gamma, beta

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

def has_hairy_ball(d):
    """Does S^{d-1} have a forced zero? Yes if d-1 is even, i.e., d is odd."""
    return d % 2 == 1


Omega_3 = omega(3)


# Test cases
cases = [
    ("alpha_s",    list(range(5, 13)),  0.1159, 0.1179),
    ("m_tau/m_mu", list(range(6, 14)),  16.53,  16.82),
    ("m_mu/m_e",   list(range(14, 22)), 206.50, 206.77),
    ("m_tau",      list(range(5, 13)),  1755.0, 1777.0),
    ("v",          list(range(5, 13)),  240.8,  246.22),
    ("ell_A",      list(range(5, 13)),  297.6,  301.6),
    ("m_W",        list(range(5, 13)),  79.89,  80.38),
]


def compute_correction(dims, h_zero, h_smooth):
    """Omega-weighted correction with hairy ball modulation."""
    total = 0.0
    for d in dims[:-1]:
        w = omega(d - 1) * overlap_deficit(d) / Omega_3
        if has_hairy_ball(d):
            total += w * h_zero
        else:
            total += w * h_smooth
    return total


# === Show the hairy ball pattern ===
print("=" * 80)
print("HAIRY BALL PATTERN IN THE CASCADE")
print("=" * 80)

for d in range(5, 22):
    hb = "ZERO (hairy ball)" if has_hairy_ball(d) else "smooth"
    om = omega(d-1)
    deficit = overlap_deficit(d)
    step = om * deficit / Omega_3
    print(f"  d={d:2d}  S^{d-1:d} {'even' if (d-1)%2==0 else 'odd ':4s}  "
          f"{hb:<20s}  Omega={om:10.4f}  step_corr={step:.6f}")


# === Scan h_zero values ===
print(f"\n{'='*80}")
print("SCAN: h(hairy ball) with h(smooth) = 1")
print(f"{'='*80}")

best_rms = 1e10
best_h = 0

print(f"\n{'h_zero':>8s}  ", end="")
for name, _, _, _ in cases:
    print(f"  {name:>12s}", end="")
print(f"  {'RMS':>8s}")
print("-" * 100)

for h_zero_10 in range(0, 31):  # 0.0 to 3.0 in steps of 0.1
    h_zero = h_zero_10 / 10.0
    devs = []
    print(f"{h_zero:8.1f}  ", end="")
    for name, dims, Q0, Q_obs in cases:
        corr = compute_correction(dims, h_zero, 1.0)
        Q_corr = Q0 * (1.0 + corr)
        dev = (Q_corr - Q_obs) / Q_obs * 100
        devs.append(dev)
        print(f"  {dev:+11.3f}%", end="")
    rms = np.sqrt(np.mean(np.array(devs)**2))
    if rms < best_rms:
        best_rms = rms
        best_h = h_zero
    print(f"  {rms:8.3f}%")

print(f"\nBest h_zero = {best_h:.1f} with RMS = {best_rms:.3f}%")


# === Fine scan around best ===
print(f"\n{'='*80}")
print(f"FINE SCAN around h_zero = {best_h:.1f}")
print(f"{'='*80}")

best_rms_fine = 1e10
best_h_fine = 0

for h_zero_100 in range(max(0, int(best_h*100)-50), int(best_h*100)+51):
    h_zero = h_zero_100 / 100.0
    devs = []
    for name, dims, Q0, Q_obs in cases:
        corr = compute_correction(dims, h_zero, 1.0)
        Q_corr = Q0 * (1.0 + corr)
        dev = (Q_corr - Q_obs) / Q_obs * 100
        devs.append(dev)
    rms = np.sqrt(np.mean(np.array(devs)**2))
    if rms < best_rms_fine:
        best_rms_fine = rms
        best_h_fine = h_zero

print(f"Best h_zero = {best_h_fine:.2f} with RMS = {best_rms_fine:.3f}%")


# === Also scan both h_zero and h_smooth ===
print(f"\n{'='*80}")
print("2D SCAN: h_zero and h_smooth")
print(f"{'='*80}")

best_rms_2d = 1e10
best_hz = 0
best_hs = 0

for hz_10 in range(0, 31):
    for hs_10 in range(5, 25):
        h_z = hz_10 / 10.0
        h_s = hs_10 / 10.0
        devs = []
        for name, dims, Q0, Q_obs in cases:
            corr = compute_correction(dims, h_z, h_s)
            Q_corr = Q0 * (1.0 + corr)
            dev = (Q_corr - Q_obs) / Q_obs * 100
            devs.append(dev)
        rms = np.sqrt(np.mean(np.array(devs)**2))
        if rms < best_rms_2d:
            best_rms_2d = rms
            best_hz = h_z
            best_hs = h_s

print(f"Best: h_zero = {best_hz:.1f}, h_smooth = {best_hs:.1f}, RMS = {best_rms_2d:.3f}%")


# === Test cascade-motivated h values ===
print(f"\n{'='*80}")
print("CASCADE-MOTIVATED h VALUES")
print(f"{'='*80}")

# chi(S^{2n}) = 2, so the topological "cost" of a hairy ball zero is 2.
# Possible h values:
# h = 1/2 (half correction at zeros: 1/chi)
# h = 0 (no correction at zeros: fully blocked)
# h = 1/chi(S^{2n}) = 1/2
# h = (chi-1)/chi = 1/2
# h = 1/(2*sqrt(pi)) (the topological factor from the mass formula!)

candidates = [
    ("h=0 (blocked)", 0.0, 1.0),
    ("h=1/2 (1/chi)", 0.5, 1.0),
    ("h=1 (no modulation)", 1.0, 1.0),
    ("h=2 (enhanced at zeros)", 2.0, 1.0),
    ("h=1/(2sqrt(pi))", 1.0/(2*np.sqrt(pi)), 1.0),
    ("h=sqrt(pi)/2", np.sqrt(pi)/2, 1.0),
    ("h=1/pi", 1.0/pi, 1.0),
    ("h=2/pi", 2.0/pi, 1.0),
    (f"h={best_h_fine:.2f} (best fit)", best_h_fine, 1.0),
    ("zero:0, smooth:2", 0.0, 2.0),
    ("zero:1/2, smooth:3/2", 0.5, 1.5),
]

print(f"\n{'Candidate':<25s}  ", end="")
for name, _, _, _ in cases:
    print(f"  {name:>10s}", end="")
print(f"  {'RMS':>8s}")
print("-" * 105)

for label, h_z, h_s in candidates:
    devs = []
    print(f"{label:<25s}  ", end="")
    for name, dims, Q0, Q_obs in cases:
        corr = compute_correction(dims, h_z, h_s)
        Q_corr = Q0 * (1.0 + corr)
        dev = (Q_corr - Q_obs) / Q_obs * 100
        devs.append(dev)
        print(f"  {dev:+9.3f}%", end="")
    rms = np.sqrt(np.mean(np.array(devs)**2))
    print(f"  {rms:8.3f}%")


# === The "only smooth steps" formula ===
print(f"\n{'='*80}")
print("ONLY SMOOTH STEPS (h_zero = 0)")
print(f"{'='*80}")

print(f"\nFormula: delta = sum_{{d even}} Omega_{{d-1}} * (1-C^2) / Omega_3")
print(f"(Only steps where S^{{d-1}} is odd-dimensional, no hairy ball zero)\n")

for name, dims, Q0, Q_obs in cases:
    smooth_steps = [d for d in dims[:-1] if not has_hairy_ball(d)]
    zero_steps = [d for d in dims[:-1] if has_hairy_ball(d)]

    corr_smooth = sum(omega(d-1)*overlap_deficit(d)/Omega_3 for d in smooth_steps)
    corr_zero = sum(omega(d-1)*overlap_deficit(d)/Omega_3 for d in zero_steps)
    corr_total = corr_smooth + corr_zero
    delta_obs = Q_obs/Q0 - 1.0

    print(f"  {name}: smooth={corr_smooth:.6f}  zero={corr_zero:.6f}  "
          f"total={corr_total:.6f}  obs={delta_obs:.6f}  "
          f"smooth/obs={corr_smooth/delta_obs:.3f}")
