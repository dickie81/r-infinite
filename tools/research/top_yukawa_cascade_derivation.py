#!/usr/bin/env python3
"""
Cascade derivation of the top Yukawa coupling (research script).

Background
----------
SM top: m_t = 172.76 GeV (PDG, on-shell), v = 246.22 GeV (PDG).
Yukawa: y_t = m_t * sqrt(2) / v = 0.992 -- famously near unity.
MS-bar at m_t scale: m_t(MS-bar) ~ 163 GeV.

Cascade has the LEPTON mass formula (Part 4b Theorem complete-mass):
    m_g = (alpha_s v / sqrt(2)) * exp(-Phi(d_g)) * (2 sqrt(pi))^{-(n_D + 1)}
where:
  alpha_s = 0.1159 (cascade leading)
  v = 240.8 GeV (cascade leading; observed 246.22)
  d_g in {5, 13, 21} = generation layer (tau, mu, e via Bott)
  n_D = number of Dirac obstructions on path
  the "+1" is C's own obstruction (C = alpha_s/(2 sqrt pi) is universal Yukawa).

Lepton table (Part 4b):
  tau: d_g=5,  n_D=1 -> m_tau = 1755 MeV (-1.2%)
  mu:  d_g=13, n_D=2 -> m_mu  = 106.2 MeV (+0.47%)
  e:   d_g=21, n_D=3 -> m_e   = 0.514 MeV (+0.60%)

For top (up-type, gen 3 = same generation as tau), the structural question:
what is the up-type analog of the lepton mass formula?

The (t/b)/(c/s) = N_c pattern (Part 4b line 768) suggests up-type carries
extra factor N_c relative to down-type, "arising from Weyl chirality structure
at d=12".  So one ansatz:
    m_up(d_g, n_D) = m_lep(d_g, n_D) * up_factor

This script explores up-factor ansatzes and tests against m_t.
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


# Cascade primitives
def R(d):
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha(d):
    return R(d) ** 2 / 4


# Cascade leading values (Part 4b)
ALPHA_S = 0.1159          # cascade leading alpha_s(M_Z)
V_CAS = 240.8             # cascade leading EW VEV (GeV)
TWO_SQRT_PI = 2 * math.sqrt(math.pi)  # 2 sqrt(pi) ~ 3.5449
CHI = 2                   # Euler characteristic of S^{2n}
N_C = 3                   # color factor (Adams at d=12)

# Reverse-engineer Phi(d_g) values from the lepton table
# m_lep = (alpha_s v / sqrt(2)) exp(-Phi(d_g)) (2 sqrt pi)^{-(n_D+1)}
# => exp(-Phi(d_g)) = m_lep * sqrt(2) / (alpha_s v) * (2 sqrt pi)^{n_D+1}
def reverse_phi(m_lep_GeV, n_D):
    factor = math.sqrt(2) / (ALPHA_S * V_CAS)
    obstruction = TWO_SQRT_PI ** (n_D + 1)
    return -math.log(m_lep_GeV * factor * obstruction)


PHI_5  = reverse_phi(1.755, 1)   # tau, m=1755 MeV
PHI_13 = reverse_phi(0.1062, 2)  # mu, m=106.2 MeV
PHI_21 = reverse_phi(5.14e-4, 3) # e, m=0.514 MeV


# Observed top mass (and Yukawa)
M_T_OBS_ONSHELL = 172.76      # PDG on-shell
M_T_OBS_MSBAR = 163.0         # MS-bar at m_t scale (rough)
V_OBS = 246.22                # PDG
Y_T_OBS = M_T_OBS_ONSHELL * math.sqrt(2) / V_OBS


def main() -> int:
    print("=" * 78)
    print("TOP YUKAWA CASCADE DERIVATION (research)")
    print("=" * 78)
    print()

    # ----------------------------------------------------------------
    # 1. Reverse-engineered Phi values from the lepton table
    # ----------------------------------------------------------------
    print("Reverse-engineered Phi(d_g) from the lepton mass formula:")
    print(f"  Phi(5)  = {PHI_5:>+8.4f}  (tau anchor)")
    print(f"  Phi(13) = {PHI_13:>+8.4f}  (mu anchor)")
    print(f"  Phi(21) = {PHI_21:>+8.4f}  (e anchor)")
    print()

    # ----------------------------------------------------------------
    # 2. Try various ansatzes for the up-type mass formula at d_g=5 (top)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Top ansatz tests: m_t = (alpha_s v / sqrt(2)) * exp(-Phi(d_g)) * F_up")
    print("-" * 78)
    print()
    print("Top is third-generation up-type fermion.  Per Part IVa Bott periodicity,")
    print("third-gen sits at d_g=5 (same as tau).  We need to find an up-type")
    print("topological factor F_up that gives m_t = ~172 GeV.")
    print()
    print("Required: F_up_required = m_t * sqrt(2) / (alpha_s * v * exp(-Phi(d_g)))")
    print()

    base_factor = ALPHA_S * V_CAS / math.sqrt(2)  # ~ 19.74 GeV scale
    print(f"  Base scale (alpha_s v / sqrt(2)) = {base_factor:.4f} GeV")
    print()

    print(f"{'d_g':>4}  {'exp(-Phi(d_g))':>16}  {'F_up required':>16}  "
          f"{'m_t target':>14}")
    print("-" * 70)
    for d_g, phi in [(5, PHI_5), (13, PHI_13), (21, PHI_21)]:
        exp_phi = math.exp(-phi)
        target_mass = M_T_OBS_ONSHELL  # GeV
        F_up_req = target_mass / (base_factor * exp_phi)
        print(f"{d_g:>4}  {exp_phi:>16.6e}  {F_up_req:>16.6f}  "
              f"{target_mass:>14.4f}")
    print()

    # ----------------------------------------------------------------
    # 3. Test specific structural ansatzes for F_up
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Structural ansatzes for F_up:")
    print("-" * 78)
    print()

    candidates = []
    # n integer powers of (2 sqrt pi)
    for n in [-2, -1, 0, 1, 2, 3, 4, 5, 6]:
        candidates.append(
            (f"(2 sqrt pi)^{n}", TWO_SQRT_PI ** n)
        )
    # N_c-related factors
    candidates.extend([
        ("N_c", N_C),
        ("N_c^2", N_C ** 2),
        ("N_c^3", N_C ** 3),
        ("N_c * (2 sqrt pi)", N_C * TWO_SQRT_PI),
        ("N_c * (2 sqrt pi)^2", N_C * TWO_SQRT_PI ** 2),
        ("N_c * (2 sqrt pi)^3", N_C * TWO_SQRT_PI ** 3),
        ("N_c^2 * (2 sqrt pi)", N_C ** 2 * TWO_SQRT_PI),
        ("(2 sqrt pi)^6 / N_c^2", TWO_SQRT_PI ** 6 / N_C ** 2),
        ("64 pi^3", 64 * math.pi ** 3),
        ("1 (Yukawa unity)", 1.0),
        ("v^2 / (alpha_s v base) -- saturation", V_CAS / (ALPHA_S * V_CAS)),
        ("1/(alpha_s)", 1.0 / ALPHA_S),
        ("sqrt(2)/alpha_s", math.sqrt(2) / ALPHA_S),
    ])

    print("Test each F_up candidate at d_g=5 (third-gen layer):")
    print()
    print(f"{'F_up ansatz':>30}  {'F_up value':>14}  {'m_t (GeV)':>12}  "
          f"{'dev. (vs 172.76)':>16}")
    print("-" * 78)
    exp_phi_5 = math.exp(-PHI_5)
    best_match = None
    for name, val in candidates:
        m_t_pred = base_factor * exp_phi_5 * val
        dev = (m_t_pred - M_T_OBS_ONSHELL) / M_T_OBS_ONSHELL
        flag = ""
        if abs(dev) < 0.05:
            flag = " <-- within 5%"
        if best_match is None or abs(dev) < abs(best_match[2]):
            best_match = (name, m_t_pred, dev)
        print(f"{name:>30}  {val:>14.4f}  {m_t_pred:>12.3f}  {dev:>+15.2%}{flag}")
    print()
    print(f"Best match at d_g=5: {best_match[0]}, m_t = {best_match[1]:.2f} GeV, "
          f"dev = {best_match[2]:+.2%}")
    print()

    # ----------------------------------------------------------------
    # 4. Test at d_g=21 (might be where up-type lives)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("Test at d_g=21 (alternative up-type layer, with top observed mass):")
    print("-" * 78)
    print()
    exp_phi_21 = math.exp(-PHI_21)
    print(f"exp(-Phi(21)) = {exp_phi_21:.6e}")
    print()
    print(f"{'F_up ansatz':>30}  {'F_up value':>14}  {'m_t (GeV)':>12}  "
          f"{'dev. (vs 172.76)':>16}")
    print("-" * 78)
    best_match_21 = None
    for name, val in candidates:
        m_t_pred = base_factor * exp_phi_21 * val
        if not (1e-3 < m_t_pred < 1e6):
            continue
        dev = (m_t_pred - M_T_OBS_ONSHELL) / M_T_OBS_ONSHELL
        flag = ""
        if abs(dev) < 0.05:
            flag = " <-- within 5%"
        if best_match_21 is None or abs(dev) < abs(best_match_21[2]):
            best_match_21 = (name, m_t_pred, dev)
        print(f"{name:>30}  {val:>14.4f}  {m_t_pred:>12.3f}  {dev:>+15.2%}{flag}")
    print()
    if best_match_21:
        print(f"Best match at d_g=21: {best_match_21[0]}, m_t = {best_match_21[1]:.2f} "
              f"GeV, dev = {best_match_21[2]:+.2%}")
    print()

    # ----------------------------------------------------------------
    # 5. Direct test: y_t = 1 (Yukawa unity)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("YUKAWA UNITY TEST: y_t = 1 exactly?")
    print("-" * 78)
    print()
    print(f"Observed y_t = m_t sqrt(2) / v = {Y_T_OBS:.6f}  (PDG on-shell values)")
    print()
    print("If y_t = 1 exactly:")
    print(f"  m_t = v / sqrt(2)")
    print(f"  Using cascade leading v = {V_CAS} GeV: m_t = {V_CAS/math.sqrt(2):.2f} GeV")
    print(f"  Using observed v = {V_OBS} GeV: m_t = {V_OBS/math.sqrt(2):.2f} GeV")
    print(f"  vs PDG on-shell m_t = {M_T_OBS_ONSHELL:.2f} GeV")
    print()
    cascade_pred = V_CAS / math.sqrt(2)
    obs_pred = V_OBS / math.sqrt(2)
    cas_dev = (cascade_pred - M_T_OBS_ONSHELL) / M_T_OBS_ONSHELL
    obs_dev = (obs_pred - M_T_OBS_ONSHELL) / M_T_OBS_ONSHELL
    print(f"  Cascade-leading deviation: {cas_dev:+.2%}")
    print(f"  Observed-v deviation: {obs_dev:+.2%}  <-- 0.78% is within Tier 2")
    print()
    print("y_t = 1 (Yukawa unity) is a CASCADE-INTERNAL HYPOTHESIS:")
    print("  - top sits at the EW threshold; m_t saturates v/sqrt(2)")
    print("  - if cascade structure forces y_t = 1, then m_t = v/sqrt(2) is")
    print("    Tier 2 (matches observed to <1%)")
    print()
    print("Required structural derivation: why y_t = 1 from cascade?")
    print()
    print("Candidate cascade structural argument for y_t = 1:")
    print("  - y_t cascade-derived: y_t = alpha_s exp(-Phi(d_g)) (2 sqrt pi)^k")
    print("    for k that gives ~1.0")
    print()
    print(f"  At d_g=5: y_t = {ALPHA_S} * {math.exp(-PHI_5):.4f} * (2 sqrt pi)^k")
    print(f"          = {ALPHA_S * math.exp(-PHI_5):.6f} * (2 sqrt pi)^k")
    print(f"  Need: (2 sqrt pi)^k = 1 / {ALPHA_S * math.exp(-PHI_5):.6f}")
    print(f"                     = {1.0 / (ALPHA_S * math.exp(-PHI_5)):.4f}")
    print(f"  k = log(...)/log(2 sqrt pi) = "
          f"{math.log(1.0 / (ALPHA_S * math.exp(-PHI_5))) / math.log(TWO_SQRT_PI):.4f}")
    print()
    k_top_5 = math.log(1.0 / (ALPHA_S * math.exp(-PHI_5))) / math.log(TWO_SQRT_PI)
    print(f"  At d_g=5: required k = {k_top_5:.4f}  (NOT integer)")
    print()
    k_top_13 = math.log(1.0 / (ALPHA_S * math.exp(-PHI_13))) / math.log(TWO_SQRT_PI)
    print(f"  At d_g=13: required k = {k_top_13:.4f}  (NOT integer)")
    print()
    k_top_21 = math.log(1.0 / (ALPHA_S * math.exp(-PHI_21))) / math.log(TWO_SQRT_PI)
    print(f"  At d_g=21: required k = {k_top_21:.4f}  (NOT integer)")
    print()
    print("None of d_g in {5, 13, 21} gives integer k for y_t = 1 directly.")
    print()

    # ----------------------------------------------------------------
    # 6. Honest summary
    # ----------------------------------------------------------------
    print("=" * 78)
    print("HONEST SUMMARY")
    print("=" * 78)
    print()
    print("The top Yukawa y_t ~ 1 is structurally striking but does not fall")
    print("out of the cascade lepton mass formula via a clean integer-exponent")
    print("up-type analog at any of d_g in {5, 13, 21}.")
    print()
    print("Best non-trivial ansatz tested: F_up = (2 sqrt pi)^k for various k")
    print(f"and N_c factors -- none gives m_t = 172.76 GeV at <5% deviation")
    print(f"with structural reading.")
    print()
    print("Yukawa-unity hypothesis y_t = 1 gives m_t = v/sqrt(2) = "
          f"{V_OBS/math.sqrt(2):.2f} GeV (using observed v),")
    print(f"which matches PDG on-shell m_t = 172.76 to 0.78%.  This is the")
    print("strongest candidate cascade reading -- but requires a structural")
    print("DERIVATION of y_t = 1 from cascade primitives.")
    print()
    print("Status: TIER-4-PATTERN level.  The y_t = 1 'top saturates EW scale'")
    print("reading is suggestive but not yet derived from cascade primitives.")
    print()
    print("Honest verdict: the top Yukawa is NOT cascade-derived in this script.")
    print("Direct application of the lepton mass formula structure does not")
    print("close to a clean structural form.  Further work needed: identify")
    print("the up-type structural factor (analogous to lepton n_D + 1) that")
    print("gives integer-exponent closed-form for y_t.")
    print()
    print("Open: cascade-native derivation of y_t = 1 (or equivalent m_t = v/sqrt(2)).")
    print("Closes: Part IVb 'Derive the full up-type quark mass spectrum' (line 1916)")
    print("partially -- pinpoints the top Yukawa as the structural seed needed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
