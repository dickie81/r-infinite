#!/usr/bin/env python3
"""
Cascade higher Bott layers vs observed neutrino mass scales.

CONTEXT
=======
Question: cascade-formula mass at d=37 came out near 0.7 eV in the
rough survey, but with proper n_D counting it should be much closer to
the active atmospheric neutrino mass scale (~0.05 eV).  Is there a
clean cascade-internal structure where higher Bott layers d=29, 37,
45, ... naturally source neutrino mass eigenstates?

CURRENT CASCADE NEUTRINO FORMULA
================================
Part IVb derives:
    m_nu(Gen g) = m_29 * alpha(d_g) / chi^(29 - d_g),  d_g in {21, 13, 5}

with m_29 = (alpha_s v / sqrt(2)) * exp(-Phi(29)) * (2sqrt(pi))^(-5)
          ~ 543 eV.

Predictions:
    Gen 1: m_29 * alpha(21)/chi^8  = 0.0493 eV  (matches sqrt(Delta m^2_atm) at -1%)
    Gen 2: m_29 * alpha(13)/chi^16 = 3.07e-4 eV (very small)
    Gen 3: m_29 * alpha(5)/chi^24  = 2.93e-6 eV (very small)

PROBLEM: Gen 2 is much too small to give observed solar splitting.
    Observed sqrt(Delta m^2_sol) = 0.0086 eV
    Cascade Gen 2:                  3e-4 eV  (off by ~30x)

ALTERNATIVE READING TO TEST
===========================
What if the cascade has TWO source layers for neutrinos:
    d=29: sources Gen 1 (atmospheric scale)
    d=37: sources Gen 2 (solar scale) directly?

If the cascade-formula at d=37 naturally lands at the solar scale, that
would be a structurally clean two-source cascade prediction.

ALSO TO TEST
============
The user noted: cascade-formula at d=37 might be at the atm scale ~0.05 eV
directly, with d=29 sourcing it only via descent (and m_29 not being a
particle but a structural number).

Compute the higher Bott tower carefully and check.

WHAT THIS SCRIPT DOES
=====================
  1. Computes Phi(d) and cascade-formula mass at each Dirac layer up to
     d=53, with proper n_D counting (n_D = (d-5)/8 + 1).
  2. Compares m_d directly with observed neutrino scales.
  3. Tests whether m_29 -> Gen 1 -> Gen 2 -> Gen 3 (current) matches
     observation worse than alternative readings.
  4. Identifies clean numerical structures (if any) connecting higher
     Bott layers to neutrino mass eigenvalues.
"""

from __future__ import annotations

import math


def R_cascade(d: int) -> float:
    return math.exp(math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0))


def alpha_cascade(d: int) -> float:
    return R_cascade(d) ** 2 / 4.0


def p_cascade(d: int) -> float:
    """p(d) = (1/2) psi((d+1)/2) - (1/2) ln(pi)."""
    a = (d + 1) / 2.0
    if abs(a - round(a)) < 1e-10:
        # Integer
        n = int(round(a))
        gamma = 0.5772156649015329
        psi = -gamma + sum(1.0/k for k in range(1, n))
    else:
        # Half-integer
        n = int(a - 0.5)
        gamma = 0.5772156649015329
        psi = -gamma - 2*math.log(2) + 2*sum(1.0/(2*k+1) for k in range(n))
    return 0.5 * psi - 0.5 * math.log(math.pi)


def Phi_cascade(d_max: int, d_min: int = 5) -> float:
    return sum(p_cascade(d) for d in range(d_min, d_max + 1))


CHI = 2
SQRT_PI = math.sqrt(math.pi)
TWOSQRTPI = 2 * SQRT_PI

ALPHA_S = 0.1179
V_GEV = 246.0
V_EV = V_GEV * 1e9
M_PRE_EV = ALPHA_S * V_EV / math.sqrt(2)


def n_D_for_dirac(d: int) -> int:
    """n_D = number of Dirac layers in descent path from d down to d=4.
    For d=5: n_D=1 (just d=5).  For d=13: n_D=2 (d=13 and d=5).  Etc.
    Pattern: n_D = (d-5)//8 + 1.
    """
    return (d - 5) // 8 + 1


def cascade_mass(d: int) -> float:
    """Cascade fermion mass formula.
    m(d) = (alpha_s v / sqrt(2)) * exp(-Phi(d)) * (2 sqrt(pi))^(-(n_D+1))
    """
    n_D = n_D_for_dirac(d)
    return M_PRE_EV * math.exp(-Phi_cascade(d)) * TWOSQRTPI ** (-(n_D + 1))


def main():
    print("=" * 76)
    print("Cascade higher Bott tower vs neutrino mass scales")
    print("=" * 76)
    print()

    # Step 1: tabulate the tower with proper n_D
    print("STEP 1: cascade Bott tower with proper n_D counting")
    print("-" * 76)
    print(f"  {'d':>3}  {'n_D':>4}  {'Phi(d)':>10}  {'(2sqrt(pi))^(-(n_D+1))':>22}  {'cascade m(d)':>20}")
    masses = {}
    for d in [5, 13, 21, 29, 37, 45, 53, 61, 69]:
        n_D = n_D_for_dirac(d)
        phi = Phi_cascade(d)
        topo = TWOSQRTPI ** (-(n_D + 1))
        m = cascade_mass(d)
        masses[d] = m
        if m > 1e6:
            mass_str = f"{m/1e6:>10.4f} MeV"
        elif m > 1:
            mass_str = f"{m:>10.4e} eV"
        else:
            mass_str = f"{m:>10.4e} eV"
        print(f"  {d:>3}  {n_D:>4}  {phi:>10.4f}  {topo:>22.4e}  {mass_str:>20}")
    print()

    # Sanity check vs known Standard Model masses
    print("STEP 2: sanity check vs known SM masses")
    print("-" * 76)
    print(f"  d=5  cascade: {masses[5]/1e6:>10.4f} MeV   vs  m_tau =  1776.86 MeV  ratio: {masses[5]/1.77686e9:>10.4f}")
    print(f"  d=13 cascade: {masses[13]/1e6:>10.4f} MeV   vs  m_mu  =   105.66 MeV  ratio: {masses[13]/0.10566e9:>10.4f}")
    print(f"  d=21 cascade: {masses[21]/1e6:>10.6f} MeV   vs  m_e   =     0.511 MeV  ratio: {masses[21]/0.510999e6:>10.4f}")
    print()
    print(f"  d=29 cascade: {masses[29]:>10.2f} eV       (paper claims ~543 eV)")
    print(f"  d=37 cascade: {masses[37]:>10.4e} eV")
    print(f"  d=45 cascade: {masses[45]:>10.4e} eV")
    print()

    # Step 3: compare with observed neutrino masses
    print("STEP 3: compare with observed neutrino mass scales")
    print("-" * 76)
    print()
    obs_atm = 0.0495    # sqrt(Delta m^2_atm)
    obs_sol = 0.0086    # sqrt(Delta m^2_sol)
    print(f"  Observed: sqrt(Delta m^2_atm) = {obs_atm:.4f} eV  (atmospheric)")
    print(f"  Observed: sqrt(Delta m^2_sol) = {obs_sol:.4f} eV  (solar)")
    print()
    print(f"  Cascade-formula at higher Bott layers:")
    for d in [29, 37, 45, 53]:
        m = masses[d]
        ratio_atm = m / obs_atm
        ratio_sol = m / obs_sol
        print(f"    m_{d:<2} = {m:>12.4e} eV  | m_{d}/atm = {ratio_atm:>10.4e} | m_{d}/sol = {ratio_sol:>10.4e}")
    print()

    # Step 4: test alternative readings
    print("STEP 4: test alternative cascade neutrino mass assignments")
    print("-" * 76)
    print()
    print("  Reading 1 (current): m_29 sources all three via descent")
    for d_g in [21, 13, 5]:
        m_nu = masses[29] * alpha_cascade(d_g) / (CHI ** (29 - d_g))
        print(f"    Gen at d={d_g}: m = {m_nu:.4e} eV")
    m_29_gen1 = masses[29] * alpha_cascade(21) / (CHI ** 8)
    m_29_gen2 = masses[29] * alpha_cascade(13) / (CHI ** 16)
    m_29_gen3 = masses[29] * alpha_cascade(5)  / (CHI ** 24)
    dm2_atm_R1 = m_29_gen1**2 - m_29_gen2**2
    dm2_sol_R1 = m_29_gen2**2 - m_29_gen3**2
    print(f"    Delta m^2_atm = {dm2_atm_R1:.4e} eV^2  (obs 2.45e-3, ratio {dm2_atm_R1/2.45e-3:.4f})")
    print(f"    Delta m^2_sol = {dm2_sol_R1:.4e} eV^2  (obs 7.5e-5, ratio {dm2_sol_R1/7.5e-5:.4e})")
    print()

    print("  Reading 2 (alternative): m_37 = atmospheric directly")
    print(f"    m_37 = {masses[37]:.4e} eV  (vs observed 0.0495 eV; ratio {masses[37]/obs_atm:.4f})")
    print(f"    With 1/sqrt(2) prefactor: {masses[37]/math.sqrt(2):.4e} eV (ratio {masses[37]/math.sqrt(2)/obs_atm:.4f})")
    print(f"    With 1/(2sqrt(pi)) prefactor: {masses[37]/TWOSQRTPI:.4e} eV (ratio {masses[37]/TWOSQRTPI/obs_atm:.4f})")
    print(f"    With 2sqrt(pi) prefactor: {masses[37]*TWOSQRTPI:.4e} eV (ratio {masses[37]*TWOSQRTPI/obs_atm:.4f})")
    print()
    print("  Reading 3 (also alternative): m_45 = solar splitting scale directly")
    print(f"    m_45 = {masses[45]:.4e} eV  (vs observed sqrt(Delta m^2_sol) = 0.0086 eV; ratio {masses[45]/obs_sol:.4e})")
    print()

    # Step 5: full tower with various conversion factors
    print("STEP 5: cascade tower vs neutrino mass eigenstates -- match search")
    print("-" * 76)
    print()
    candidates = {
        "m_atm = 0.0495 eV (Gen 1, atmospheric)":     0.0495,
        "m_sol = 0.0086 eV (Gen 2, solar splitting)": 0.0086,
        "Sum m_nu < 0.12 eV (Planck cosmology)":      0.12,
        "0nubb m_bb < 0.05 eV (latest)":              0.05,
    }

    for d in [29, 37, 45, 53, 61, 69, 77]:
        m = masses[d]
        if m < 1e-12:
            continue
        print(f"  d={d}, cascade m_{d} = {m:.4e} eV")
        for label, target in candidates.items():
            ratio = m / target
            print(f"    vs {label}:  ratio = {ratio:.4e}  log10 = {math.log10(ratio):>+6.2f}")
        # Various transforms
        transforms = [
            ("m / chi", m / CHI),
            ("m / 2sqrt(pi)", m / TWOSQRTPI),
            ("m / (2pi)", m / (2*math.pi)),
            ("m * alpha(d_avg)", m * alpha_cascade(d - 4)),  # d-4 is heuristic
            ("m * (cascade descent factor)", m * 0.5),  # placeholder
        ]
        # Skip transforms for brevity
        print()


if __name__ == "__main__":
    main()
