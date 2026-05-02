#!/usr/bin/env python3
"""
Cascade dynamical-tick w(z): testing whether rho_Lambda(N) gives
DESI's apparent w(z) signal.

CONTEXT
=======
Dynamical-tick reading: 1 Planck tick = 1 dimensional collapse.
Universe started at d=0, ascended through 217 in early phase, continues
ascending.  Current N ~ 10^60 ticks.

CONJECTURE: rho_Lambda(N) = C / N^k for some k determined by cascade
descent's residual-measure scaling.  Test which k (if any) reproduces
DESI's apparent w(z) signal.

DESI 2024 (DR2) BAO:  w_0 ~ -0.76, w_a ~ -0.55  (CPL parameterization)
LCDM / cascade static (Part III):  w_0 = -1, w_a = 0 exactly.

CHECK 7: cascade-internal cosmology only.  No semiclassics.
"""

from __future__ import annotations

import math


# Cosmic constants
T_PLANCK = 5.39e-44  # s
H_0_KM_S_MPC = 66.78  # cascade Option A
H_0 = H_0_KM_S_MPC * 1e3 / 3.086e22  # 1/s
T_HUBBLE = 1 / H_0
T_NOW = 13.8e9 * 3.156e7  # s
N_0 = T_NOW / T_PLANCK    # cumulative ticks now ~ 8e60

OMEGA_M = 0.3147
OMEGA_R = 8.28e-5
OMEGA_L = 1 - OMEGA_M - OMEGA_R


# ---------------------------------------------------------------
# Analytic w(t) for rho_Lambda(t) = rho_Lambda_0 (t_0/t)^k
# ---------------------------------------------------------------
# Continuity: dot(rho) + 3H(1+w)rho = 0
# rho(t) = rho_0 (t_0/t)^k => dot(rho)/rho = -k/t
# => -k/t = -3H(1+w)
# => 1 + w = k/(3 H t)
# => w(t) = -1 + k/(3 H t)
#
# In terms of cosmic age and Hubble parameter, w depends on H*t product.
# At matter-dominated era: H*t = 2/3, so w_md = -1 + k/2
# At radiation-dominated era: H*t = 1/2, so w_rd = -1 + 2k/3
# At de Sitter: H*t -> infinity, w -> -1
# At present (LCDM-like): H_0 * t_0 ~ 0.96, so w_now = -1 + k/(3*0.96)

# Find H*t(z) properly via Friedmann + integration, but for cascade
# dynamical reading, we use ANALYTIC continuity (which is exact for any
# rho_Lambda(t) form provided H is known).
#
# Approximate H(z) using LCDM with self-consistent rho_Lambda(t):
# H^2(a) = H_0^2 [Omega_m a^-3 + Omega_r a^-4 + Omega_L (t_0/t)^k]
# We need t(a) self-consistently.  Use parametric scan.

def integrate_friedmann(k_param, n_steps=10000):
    """Integrate Friedmann from early universe to a=1, return t(a) and H(a)."""
    # Find t_0 self-consistently such that a(t_0) = 1
    # In units where H_0 = 1, t in units of t_H = 1/H_0
    # rho_Lambda(t) = Omega_L (t_0 / t)^k

    # Approach: forward integration with a as evolution variable
    # Step in da, compute H(a) which depends on t(a), update t.
    # To bootstrap: start at a small with H matching matter+radiation domination

    a_start = 1e-4
    # At matter domination (small a): H^2 ~ Omega_M a^-3
    # t ~ (2/3) a^{3/2} / sqrt(Omega_M) in units of t_H
    t_start = (2.0 / 3.0) * a_start ** 1.5 / math.sqrt(OMEGA_M)

    # We don't know t_0 yet.  Iterate.
    t_0_guess = 0.96  # LCDM-ish

    for iteration in range(15):
        # Forward integrate
        a_arr = []
        t_arr = []
        H_arr = []
        a = a_start
        t = t_start
        a_arr.append(a)
        t_arr.append(t)
        # H at start
        rho = OMEGA_M * a**-3 + OMEGA_R * a**-4
        if k_param == 0:
            rho_L = OMEGA_L
        else:
            rho_L = OMEGA_L * (t_0_guess / max(t, 1e-10)) ** k_param
        rho += rho_L
        H = math.sqrt(rho)
        H_arr.append(H)

        # Step forward in log a
        log_a_max = 1.0  # corresponds to a = e ~ 2.7, plenty
        log_a_steps = n_steps
        d_log_a = (log_a_max - math.log(a_start)) / log_a_steps

        for _ in range(log_a_steps):
            # dt/da = 1/(a H), so dt = d_log_a / H
            dt = d_log_a / H
            t += dt
            a *= math.exp(d_log_a)
            rho = OMEGA_M * a**-3 + OMEGA_R * a**-4
            if k_param == 0:
                rho_L = OMEGA_L
            else:
                rho_L = OMEGA_L * (t_0_guess / max(t, 1e-10)) ** k_param
            rho += rho_L
            H = math.sqrt(rho) if rho > 0 else 0
            a_arr.append(a)
            t_arr.append(t)
            H_arr.append(H)
            if a > 2:
                break

        # Find t at a = 1
        for i in range(len(a_arr) - 1):
            if a_arr[i] <= 1 <= a_arr[i+1]:
                # Linear interp
                frac = (1 - a_arr[i]) / (a_arr[i+1] - a_arr[i])
                t_at_a_1 = t_arr[i] + frac * (t_arr[i+1] - t_arr[i])
                break
        else:
            t_at_a_1 = t_arr[-1]

        # Update t_0
        new_t_0 = t_at_a_1
        if abs(new_t_0 - t_0_guess) / t_0_guess < 1e-4:
            t_0_guess = new_t_0
            break
        t_0_guess = new_t_0

    return a_arr, t_arr, H_arr, t_0_guess


def w_at_z(k_param, z, a_arr, t_arr, H_arr, t_0):
    """Get w(z) by interpolation."""
    a_target = 1 / (1 + z)
    for i in range(len(a_arr) - 1):
        if a_arr[i] <= a_target <= a_arr[i+1]:
            frac = (a_target - a_arr[i]) / (a_arr[i+1] - a_arr[i])
            t = t_arr[i] + frac * (t_arr[i+1] - t_arr[i])
            H = H_arr[i] + frac * (H_arr[i+1] - H_arr[i])
            break
    else:
        t = t_arr[-1]
        H = H_arr[-1]
    if k_param == 0:
        return -1.0, t, H
    w = -1 + k_param / (3 * H * t)
    return w, t, H


def main() -> None:
    print("Cascade dynamical-tick w(z): testing rho_Lambda(N) ~ N^-k")
    print()
    print(f"Cosmic age: t_0 = {T_NOW:.3e} s = {N_0:.3e} Planck ticks")
    print(f"H_0 t_0 (LCDM-ish): ~ 0.96")
    print()
    print(f"DESI 2024 best fit (CPL):  w_0 = -0.76, w_a = -0.55")
    print(f"LCDM / cascade static:     w_0 = -1.00, w_a = 0.00")
    print()
    print(f"{'k':>6} {'w(z=0)':>10} {'w(z=0.5)':>10} {'w(z=1)':>10} {'w(z=2)':>10} {'t_0/t_H':>10} {'evolution':>14}")
    print("-" * 80)

    z_values = [0, 0.5, 1.0, 2.0]
    for k in [0, 0.25, 0.5, 0.72, 1.0, 1.5, 2.0]:
        a_arr, t_arr, H_arr, t_0 = integrate_friedmann(k)
        w_at_zs = []
        for z in z_values:
            w, t, H = w_at_z(k, z, a_arr, t_arr, H_arr, t_0)
            w_at_zs.append(w)
        # Determine direction of evolution
        if abs(w_at_zs[0] - w_at_zs[3]) < 0.01:
            evol = "static"
        elif w_at_zs[0] < w_at_zs[3]:
            evol = "more neg now"
        else:
            evol = "more neg past"
        print(f"{k:>6.2f} {w_at_zs[0]:>10.4f} {w_at_zs[1]:>10.4f} {w_at_zs[2]:>10.4f} {w_at_zs[3]:>10.4f} {t_0:>10.4f} {evol:>14}")

    print()
    print("=" * 78)
    print("ANALYSIS")
    print("=" * 78)
    print()
    print("Closed-form: w(t) = -1 + k/(3 H t)")
    print()
    print("Key observations:")
    print()
    print("1. For k > 0 (rho_Lambda decreasing with cosmic time):")
    print("   w(z=0) > -1 (LESS negative than -1 today)")
    print("   w(z->infinity) -> matter/radiation era values, MORE negative deviations")
    print("   Direction: w STARTS near matter-era value (w ~ 0 + correction), and")
    print("              EVOLVES toward -1 as cosmic time grows.")
    print("   In other words: w more negative NOW, less negative in PAST.")
    print()
    print("2. DESI's apparent signal: w_0 = -0.76, w_a = -0.55.")
    print("   w(z=0) = -0.76, w(z=0.5) = -0.94, w(z=1) = -1.03.")
    print("   Direction: w less negative NOW, more negative in PAST.")
    print()
    print("3. CASCADE DYNAMICAL-TICK READING (rho_Lambda ~ 1/N^k) gives the")
    print("   OPPOSITE direction from DESI.")
    print()
    print("4. To match DESI's signal would require rho_Lambda INCREASING with")
    print("   cosmic time -- not what the residual-measure-decreasing intuition")
    print("   supplies.")
    print()
    print("INTERPRETATION")
    print("-" * 78)
    print()
    print("The simple cascade dynamical-tick ansatz rho_Lambda ~ 1/N^k does NOT")
    print("reproduce DESI's apparent w(z) signal.  Three resolutions:")
    print()
    print("  (a) Cascade STATIC w = -1 is correct.  DESI's signal is parameterization-")
    print("      dependent / systematic.  Several recent analyses do find LCDM still")
    print("      acceptable; the CPL parameterization is one specific choice.  This")
    print("      is the simplest reading consistent with cascade Part III's structural")
    print("      theorem.")
    print()
    print("  (b) Cascade DYNAMICAL reading needs a different rho_Lambda(N) form.")
    print("      The residual-measure argument gives 1/N^k decreasing; DESI requires")
    print("      something INCREASING with cosmic time.  No simple cascade-natural")
    print("      ansatz tested here matches.  Maybe rho_Lambda has structural")
    print("      dependence on which cascade layer is currently 'active' in some")
    print("      sense, with non-monotonic time dependence.")
    print()
    print("  (c) Cosmic w(z) is exactly -1 cascade-internally; DESI's apparent")
    print("      signal is from something OTHER than evolving dark energy --")
    print("      e.g., neutrino mass effects, modified ruler at different epochs,")
    print("      or genuine new physics not captured by either reading.")
    print()
    print("HONEST FINDING: the user's cascade dynamical-tick proposal CANNOT")
    print("trivially close DESI's signal in the form rho_Lambda ~ 1/N^k.  The")
    print("simplest dynamical-tick reading predicts the OPPOSITE w(z) evolution")
    print("from what DESI observes.")
    print()
    print("This is itself useful:")
    print("  - If DESI's signal is real and persists: cascade must explain it via")
    print("    a different mechanism, NOT dynamical rho_Lambda decay.")
    print("  - If DESI's signal is parameterization artifact: cascade STATIC w=-1")
    print("    holds.")
    print()
    print("Either way, the dynamical-tick reading does NOT obviously close the DESI")
    print("question, and the user's earlier hope that it might be a cascade signature")
    print("is not supported by this calculation.")


if __name__ == "__main__":
    main()
