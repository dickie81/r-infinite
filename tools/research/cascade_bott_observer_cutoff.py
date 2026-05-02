#!/usr/bin/env python3
"""
Bott-window averaging WITH OBSERVER-FRAME CUTOFF.

User correction: cannot include dimensions between observer (d=4) and 0
in the averaging.  Test: for each generation, average over the Bott-period
window starting at d_g UPWARD, never including d <= 4.

For Gen 3 at d_g=5: average over [5, 12] (8 layers, never below observer)
For Gen 2 at d_g=13: average over [13, 20] (8 layers)
For Gen 1 at d_g=21: average over [21, 28] (8 layers)

Or alternatively: average over [d_g, d_g + Bott_period - 1] = 8-layer
forward window.

Test against required residuals: tau +1.25%, mu -0.47%, e -0.58%.
"""
from __future__ import annotations
import math
from scipy.special import digamma


def p_d(d): return 0.5 * digamma((d + 1) / 2) - 0.5 * math.log(math.pi)


def Phi_d(d, d_min=4):
    if d <= d_min:
        return 0.0
    return sum(p_d(dprime) for dprime in range(d_min + 1, d + 1))


ALPHA_S_LEAD = 0.1159
V_LEAD = 240.8
C_LEAD = ALPHA_S_LEAD * V_LEAD / math.sqrt(2)
TWO_SQRT_PI = 2 * math.sqrt(math.pi)
GENERATIONS = {1: 21, 2: 13, 3: 5}
N_D_COUNT = {1: 3, 2: 2, 3: 1}
M_TAU_OBS = 1776.86
M_MU_OBS = 105.66
M_E_OBS = 0.5110

OBSERVER = 4


def cascade_mass(d_g, n_D, Phi_eff, C=C_LEAD):
    return C * 1e3 * math.exp(-Phi_eff) * (TWO_SQRT_PI ** -(n_D + 1))


def main():
    print("=" * 78)
    print("Bott averaging with observer-frame cutoff (d >= 5 only)")
    print("=" * 78)
    print()

    print("Required residual corrections:")
    print(f"  tau:  +1.25%, mu:  -0.47%, e:   -0.58%")
    print()

    schemes = [
        ("[d_g, d_g+7] (8 layer forward)", lambda d_g: [d for d in range(max(d_g, OBSERVER + 1), d_g + 8)]),
        ("[d_g, d_g+6] (7 layer forward, excl d_g+7)", lambda d_g: [d for d in range(max(d_g, OBSERVER + 1), d_g + 7)]),
        ("[max(5, d_g-1), d_g+6] (one back, 7 forward, cutoff)",
            lambda d_g: [d for d in range(max(d_g - 1, OBSERVER + 1), d_g + 7)]),
        ("(d_g, d_g+1) two-layer forward", lambda d_g: [d_g, d_g + 1]),
        ("(d_g, d_g+1, d_g+2) three-layer forward", lambda d_g: [d_g, d_g + 1, d_g + 2]),
        ("Bott alignment [d_g, d_g+7] strict",
            lambda d_g: [d for d in range(d_g, d_g + 8) if d >= OBSERVER + 1]),
    ]

    for name, window_fn in schemes:
        print(f"SCHEME: {name}")
        print(f"  {'particle':>8} {'window':>30} {'Phi(d_g)':>10} {'<Phi>':>10} {'corr':>10} {'res(point)':>11} {'res(avg)':>11}")
        sign_match = True
        residuals_avg = []
        for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
            d_g = GENERATIONS[gen]
            n_D = N_D_COUNT[gen]
            window = window_fn(d_g)
            Phi_pt = Phi_d(d_g)
            Phi_avg = sum(Phi_d(d) for d in window) / len(window)
            corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
            m_pt = cascade_mass(d_g, n_D, Phi_pt)
            m_avg = cascade_mass(d_g, n_D, Phi_avg)
            res_pt = (m_obs - m_pt) / m_pt * 100
            res_avg = (m_obs - m_avg) / m_avg * 100
            residuals_avg.append((label, corr, res_pt, res_avg))
            window_str = f"[{window[0]},...,{window[-1]}] ({len(window)} d)"
            print(f"  {label:>8} {window_str:>30} {Phi_pt:>+10.4f} {Phi_avg:>+10.4f} {corr:>+9.3f}% {res_pt:>+10.2f}% {res_avg:>+10.2f}%")

        # Check sign pattern
        signs = [(l, c) for l, c, _, _ in residuals_avg]
        tau_sign = signs[0][1] > 0  # need +
        mu_sign = signs[1][1] < 0   # need -
        e_sign = signs[2][1] < 0    # need -
        sign_match = tau_sign and mu_sign and e_sign
        print(f"  Sign match (tau +, mu -, e -): {sign_match}")
        print()

    # Now also test averaging where only the absolute UPWARD Bott window matters
    # For each generation, find the window starting at the SU(3)-replica position
    # (d ≡ 4 mod 8) AT OR ABOVE d_g (i.e., the first such window where d_min >= d_g)
    print("=" * 78)
    print("ALTERNATIVE: 'next Bott window above d_g' average")
    print("=" * 78)
    print()
    print("For each generation: find next Bott window [d_b, d_b+7] with d_b >= d_g")
    print("  Gen 3 (d=5): next Bott window starts at d_b=12 (since 4<5<=12)")
    print("  Gen 2 (d=13): next Bott window starts at d_b=20")
    print("  Gen 1 (d=21): next Bott window starts at d_b=28")
    print()
    for gen, label, m_obs in [(3, "tau", M_TAU_OBS), (2, "mu", M_MU_OBS), (1, "e", M_E_OBS)]:
        d_g = GENERATIONS[gen]
        n_D = N_D_COUNT[gen]
        # Find smallest Bott window starting position d_b = 4 + 8*k with d_b >= d_g
        k_above = math.ceil((d_g - 4) / 8)
        d_b = 4 + 8 * k_above
        window = list(range(d_b, d_b + 8))
        Phi_pt = Phi_d(d_g)
        Phi_avg = sum(Phi_d(d) for d in window) / len(window)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        m_pt = cascade_mass(d_g, n_D, Phi_pt)
        m_avg = cascade_mass(d_g, n_D, Phi_avg)
        res_pt = (m_obs - m_pt) / m_pt * 100
        res_avg = (m_obs - m_avg) / m_avg * 100
        window_str = f"[{window[0]}-{window[-1]}]"
        print(f"  {label:>5}: window {window_str}  Phi_avg={Phi_avg:+.4f}  Phi(d_g)={Phi_pt:+.4f}  corr={corr:+.3f}%")
        print(f"          res(point)={res_pt:+.2f}%  res(avg)={res_avg:+.2f}%")
    print()

    # Also: for Gen 3 only, test averaging from d=5 UP, excluding d=4 entirely
    print("=" * 78)
    print("KEY TEST: For Gen 3, averaging from d=5 UP (cutoff at observer)")
    print("=" * 78)
    print()
    # Various window sizes from d=5 upward
    for window_size in [2, 3, 4, 5, 6, 7, 8]:
        window = list(range(5, 5 + window_size))
        Phi_pt = Phi_d(5)
        Phi_avg = sum(Phi_d(d) for d in window) / len(window)
        corr = (math.exp(-(Phi_avg - Phi_pt)) - 1) * 100
        print(f"  Gen 3 window [5, {5 + window_size - 1}] ({window_size} layers): "
              f"Phi_avg={Phi_avg:+.4f}, correction={corr:+.3f}%")
    print()


if __name__ == "__main__":
    main()
