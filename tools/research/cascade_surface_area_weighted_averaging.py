#!/usr/bin/env python3
"""
Surface-area-weighted Bott averaging: test whether weighting by Omega_d
suppresses over-correction at descent-region generations and matches
required mass residuals.

USER INSIGHT: surface area Omega_d peaks at d=7 and decreases for d>7.
Weighting Bott averages by Omega_d gives MOST weight to layers near
d=7 (peak) and SUPPRESSES contributions from high-d descent-region
layers.  This might combat the over-correction problem of uniform Bott
averaging at high d.

Required residual corrections:
  tau (d_g=5):  +1.25%
  mu (d_g=13):  -0.47%
  e (d_g=21):   -0.58%
"""

from __future__ import annotations
import math
from scipy.special import digamma, gamma


def p_d(d): return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_d(d, d_min=4):
    if d <= d_min:
        return 0.0
    return sum(p_d(dprime) for dprime in range(d_min + 1, d + 1))


def Omega_d(d):
    """Surface area of unit (d-1)-sphere: 2 pi^{d/2} / Gamma(d/2)."""
    return 2 * math.pi ** (d / 2) / gamma(d / 2)


def R_d(d):
    return math.exp(math.lgamma(d / 2 + 1) - math.lgamma((d + 3) / 2))


def alpha_d(d):
    return R_d(d) ** 2 / 4


def N_d(d):
    return math.sqrt(math.pi) * math.exp(math.lgamma((d + 1) / 2) - math.lgamma((d + 2) / 2))


# Cascade-leading values
ALPHA_S_LEAD = 0.1159
V_LEAD = 240.8
C_LEAD = ALPHA_S_LEAD * V_LEAD / math.sqrt(2)
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
GENERATIONS = {1: 21, 2: 13, 3: 5}
N_D_COUNT = {1: 3, 2: 2, 3: 1}
M_TAU_OBS = 1776.86
M_MU_OBS = 105.66
M_E_OBS = 0.5110


def cascade_mass(d_g, n_D, Phi_eff, C=C_LEAD):
    return C * 1e3 * math.exp(-Phi_eff) * (TWO_SQRT_PI ** -(n_D + 1))


def main():
    print("=" * 78)
    print("Surface-area-weighted Bott averaging vs cascade lepton residuals")
    print("=" * 78)
    print()

    # Show Omega_d trend
    print("Surface area Omega_d trend (peaks at d=7):")
    for d in [4, 5, 6, 7, 8, 9, 11, 13, 15, 19, 21, 25, 29]:
        print(f"  d={d:3d}  Omega(d) = {Omega_d(d):>10.4f}  R(d) = {R_d(d):.4f}  N(d) = {N_d(d):.4f}")
    print()

    # Test 1: surface-area-weighted average over Bott windows from d_g forward
    print("=" * 78)
    print("TEST 1: Omega-weighted average over [d_g, d_g+7] (8-layer forward)")
    print("=" * 78)
    print()
    for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
        d_g = GENERATIONS[gen]
        n_D = N_D_COUNT[gen]
        window = list(range(d_g, d_g + 8))
        weights = [Omega_d(d) for d in window]
        wsum = sum(weights)
        Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
        Phi_pt = Phi_d(d_g)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        m_pt = cascade_mass(d_g, n_D, Phi_pt)
        m_avg = cascade_mass(d_g, n_D, Phi_avg)
        res_pt = (m_obs - m_pt) / m_pt * 100
        res_avg = (m_obs - m_avg) / m_avg * 100
        print(f"  {label:>5} (d_g={d_g}): Phi_avg = {Phi_avg:+.4f}, corr = {corr:+.3f}%, "
              f"res(point)={res_pt:+.2f}%, res(avg)={res_avg:+.2f}%")
    print()

    # Test 2: Omega-weighted over a NARROWER window (just gauge-region)
    print("=" * 78)
    print("TEST 2: Omega-weighted average over [d_g, d_g+3] (4-layer)")
    print("=" * 78)
    print()
    for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
        d_g = GENERATIONS[gen]
        n_D = N_D_COUNT[gen]
        window = list(range(d_g, d_g + 4))
        weights = [Omega_d(d) for d in window]
        wsum = sum(weights)
        Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
        Phi_pt = Phi_d(d_g)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        res_avg = (m_obs - cascade_mass(d_g, n_D, Phi_avg)) / cascade_mass(d_g, n_D, Phi_avg) * 100
        print(f"  {label:>5} (d_g={d_g}): Phi_avg = {Phi_avg:+.4f}, corr = {corr:+.3f}%, res(avg)={res_avg:+.2f}%")
    print()

    # Test 3: Omega-weighted over [d_g, d_g+1] (2-layer, the previous best)
    print("=" * 78)
    print("TEST 3: Omega-weighted (d_g, d_g+1) two-layer (refining previous best)")
    print("=" * 78)
    print()
    for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
        d_g = GENERATIONS[gen]
        n_D = N_D_COUNT[gen]
        window = [d_g, d_g + 1]
        weights = [Omega_d(d) for d in window]
        wsum = sum(weights)
        Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
        Phi_pt = Phi_d(d_g)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        res_avg = (m_obs - cascade_mass(d_g, n_D, Phi_avg)) / cascade_mass(d_g, n_D, Phi_avg) * 100
        m_pt = cascade_mass(d_g, n_D, Phi_pt)
        res_pt = (m_obs - m_pt) / m_pt * 100
        print(f"  {label:>5} (d_g={d_g}): weights = ({weights[0]:.2f}, {weights[1]:.2f}), "
              f"Phi_avg = {Phi_avg:+.4f}, corr = {corr:+.3f}%")
        print(f"          res(point)={res_pt:+.2f}%  res(avg)={res_avg:+.2f}%")
    print()

    # Test 4: alpha-weighted (alpha(d) = R(d)^2/4 -- decreases sharply at high d)
    print("=" * 78)
    print("TEST 4: alpha(d)-weighted over [d_g, d_g+7] (8-layer)")
    print("=" * 78)
    print()
    for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
        d_g = GENERATIONS[gen]
        n_D = N_D_COUNT[gen]
        window = list(range(d_g, d_g + 8))
        weights = [alpha_d(d) for d in window]
        wsum = sum(weights)
        Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
        Phi_pt = Phi_d(d_g)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        res_avg = (m_obs - cascade_mass(d_g, n_D, Phi_avg)) / cascade_mass(d_g, n_D, Phi_avg) * 100
        print(f"  {label:>5} (d_g={d_g}): Phi_avg = {Phi_avg:+.4f}, corr = {corr:+.3f}%, res(avg)={res_avg:+.2f}%")
    print()

    # Test 5: 1/Omega_d weighted (favoring HIGH d) -- probably wrong but let's see
    print("=" * 78)
    print("TEST 5: 1/Omega(d)-weighted over [d_g, d_g+7] (8-layer, INVERSE)")
    print("=" * 78)
    print()
    for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
        d_g = GENERATIONS[gen]
        n_D = N_D_COUNT[gen]
        window = list(range(d_g, d_g + 8))
        weights = [1 / Omega_d(d) for d in window]
        wsum = sum(weights)
        Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
        Phi_pt = Phi_d(d_g)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        res_avg = (m_obs - cascade_mass(d_g, n_D, Phi_avg)) / cascade_mass(d_g, n_D, Phi_avg) * 100
        print(f"  {label:>5} (d_g={d_g}): Phi_avg = {Phi_avg:+.4f}, corr = {corr:+.3f}%, res(avg)={res_avg:+.2f}%")
    print()

    # Test 6: Most natural: weight averaging by Omega(d) where d_g is the centerpoint
    print("=" * 78)
    print("TEST 6: Omega-weighted over CASCADE-CENTERED window [d_g-3, d_g+4]")
    print("=" * 78)
    print()
    for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
        d_g = GENERATIONS[gen]
        n_D = N_D_COUNT[gen]
        window = [d for d in range(d_g - 3, d_g + 5) if d >= 5]  # cutoff at d=5 (above observer)
        weights = [Omega_d(d) for d in window]
        wsum = sum(weights)
        Phi_avg = sum(w * Phi_d(d) for w, d in zip(weights, window)) / wsum
        Phi_pt = Phi_d(d_g)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        res_avg = (m_obs - cascade_mass(d_g, n_D, Phi_avg)) / cascade_mass(d_g, n_D, Phi_avg) * 100
        print(f"  {label:>5} (d_g={d_g}, window={window}): Phi_avg = {Phi_avg:+.4f}, corr = {corr:+.3f}%, res(avg)={res_avg:+.2f}%")
    print()

    print("=" * 78)
    print("ASSESSMENT")
    print("=" * 78)
    print()
    print("Required: tau +1.25%, mu -0.47%, e -0.58%")
    print()
    print("Compare which scheme best matches all three.")


if __name__ == "__main__":
    main()
