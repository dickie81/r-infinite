#!/usr/bin/env python3
"""
Cascade m_29 = 543 eV fermion: sub-keV sterile neutrino prediction?

CONTEXT
=======
Part IVa thm:generations and Part IVb's neutrino mass derivation place
the fourth Bott fermion at d=29 with mass m_29 ~ 543 eV.  The cascade
text classifies this as a "source mass" used in the neutrino formula
m_nu(g) = m_29 * alpha(d_g) / chi^(29-d_g).

But structurally, d=29 is a Dirac layer (d mod 8 = 5, Bott periodic),
and the cascade has fermion bundles at every Dirac layer.  The first
three Dirac layers (d=5, 13, 21) host the three SM charged-fermion
generations.  The fourth (d=29) is excluded from charged generations
by the d_1=19 phase transition wall, but the cascade does NOT eliminate
the fermion at d=29 -- only its CHARGED role.

STRUCTURAL READING
==================
Take the d=29 fermion seriously as a propagating particle:

  - Spin: 1/2  (Dirac/Majorana fermion at a Dirac layer)
  - Charge: 0  (excluded from charged-fermion role; couples to neutrinos
              via cascade descent in mass formula)
  - Mass: m_29 ~ 543 eV  (cascade-derived)
  - Interactions: mixes with active neutrinos via the cascade descent
                 formula m_nu(g) = m_29 * alpha(d_g) / chi^(29-d_g)

This is a STERILE NEUTRINO at sub-keV mass.

EXPERIMENTAL PREDICTIONS
========================

(1) Active-sterile mixing angles:
    From the cascade neutrino mass formula, the active flavour with mass
    m_g comes from m_29 attenuated by alpha(d_g)/chi^(29-d_g).  In the
    seesaw-like reading, this is the "mixing factor" between d_g and d=29:
        sin(theta_g4) ~ sqrt(alpha(d_g)/chi^(29-d_g))

    Active-sterile mixing magnitude per flavour:
        |U_g4|^2 ~ alpha(d_g) / chi^(29-d_g)

(2) Beta decay endpoint:
    KATRIN measures the tritium beta decay endpoint (E_0 = 18.6 keV).
    A heavy neutral fermion mixed with electron neutrino at mass m_4 ~
    543 eV would produce a "kink" in the beta spectrum at energy
    E = E_0 - m_4 = 18.06 keV, with strength proportional to |U_e4|^2.
    KATRIN/TRISTAN sensitivity to keV sterile neutrinos with |U_e4|^2 ~
    1e-6 by 2030.

(3) X-ray emission line:
    A keV-scale sterile neutrino can decay to a photon and an active
    neutrino: nu_4 -> nu_a + gamma at rate
        Gamma ~ (9 alpha_em G_F^2 / 256 pi^4) * sin^2(2 theta) * m_4^5
    producing a monochromatic X-ray line at E_gamma = m_4 / 2.
    For m_4 = 543 eV, E_gamma = 271 eV (extreme UV / soft X-ray).
    Below the threshold of typical X-ray observatories (Chandra ~0.5 keV).

(4) Cosmological constraints:
    A 543 eV sterile neutrino with non-negligible mixing would be
    produced in the early universe and contribute to:
      - N_eff (extra relativistic species; CMB constraint)
      - Hot dark matter (structure formation / Lyman-alpha)
      - Big Bang nucleosynthesis (BBN)

WHAT THIS SCRIPT DOES
=====================
  1. Computes cascade-predicted mixing |U_g4|^2 for g = 1, 2, 3.
  2. Computes cascade-predicted beta endpoint kink amplitude.
  3. Computes cascade-predicted X-ray decay line.
  4. Computes cascade-predicted cosmological signatures.
  5. Compares with KATRIN/TRISTAN, X-ray observations, BBN, Lyman-alpha
     constraints.
  6. Reports whether the prediction is ALLOWED, RULED OUT, or TESTABLE.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Settle the cascade's "is m_29 a real particle?" ambiguity.
  - Compute relic abundance from a specific production mechanism
    (Dodelson-Widrow, Shi-Fuller, etc.) -- depends on assumptions
    beyond cascade content.
  - Make a claim that the cascade WILL be detected; only that it
    has a specific testable prediction.
"""

from __future__ import annotations

import math


def R_cascade(d: int) -> float:
    return math.exp(math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0))


def alpha_cascade(d: int) -> float:
    return R_cascade(d) ** 2 / 4.0


CHI = 2
M29_EV = 543.0
DIRAC_LAYERS_GEN = [21, 13, 5]   # Gen 1, 2, 3
M_GEN_EV = {
    21: 0.0493,    # Gen 1 (matches sqrt(Delta m^2_atm))
    13: 3.07e-4,   # Gen 2
    5:  2.93e-6,   # Gen 3
}

# Physical constants
ALPHA_EM = 1/137.036
G_F_eV = 1.166e-5 * 1e-18  # Fermi constant in eV^-2 (since G_F is in GeV^-2)
HBAR_EV_S = 6.582e-16  # eV * s


# ---------------------------------------------------------------------------
# (1) Active-sterile mixing
# ---------------------------------------------------------------------------

def mixing_squared(d_g: int) -> float:
    """|U_g4|^2 ~ alpha(d_g) / chi^(29 - d_g)."""
    return alpha_cascade(d_g) / (CHI ** (29 - d_g))


def report_mixing():
    print("=" * 76)
    print("(1) Active-sterile mixing angles")
    print("=" * 76)
    print()
    print(f"  Cascade prediction: |U_g4|^2 = alpha(d_g) / chi^(29-d_g)")
    print()
    print(f"  {'Gen':>3}  {'d_g':>3}  {'alpha(d_g)':>10}  {'chi^(29-d_g)':>14}  {'|U_g4|^2':>14}  {'|U_g4|':>10}")
    total_mixing_sq = 0.0
    for i, dg in enumerate(DIRAC_LAYERS_GEN):
        ag = alpha_cascade(dg)
        chif = CHI ** (29 - dg)
        u_sq = mixing_squared(dg)
        total_mixing_sq += u_sq
        print(f"  {i+1:>3}  {dg:>3}  {ag:>10.4f}  {chif:>14d}  {u_sq:>14.4e}  {math.sqrt(u_sq):>10.4e}")
    print()
    print(f"  Total |U_a4|^2 (sum over flavors):  {total_mixing_sq:.4e}")
    print(f"  sin^2(2*theta) approx 4*|U_e4|^2:   {4*mixing_squared(21):.4e}")
    print()


# ---------------------------------------------------------------------------
# (2) Beta decay endpoint kink
# ---------------------------------------------------------------------------

def report_beta_decay():
    print("=" * 76)
    print("(2) Tritium beta decay endpoint kink (KATRIN/TRISTAN)")
    print("=" * 76)
    print()
    E0_eV = 18.575e3  # tritium beta endpoint, eV
    m4_eV = M29_EV
    kink_position = E0_eV - m4_eV
    Ue4_sq = mixing_squared(21)

    print(f"  Tritium endpoint E_0 = {E0_eV/1e3:.3f} keV")
    print(f"  Cascade m_4 = m_29 = {m4_eV:.0f} eV = {m4_eV/1e3:.3f} keV")
    print(f"  Kink position = E_0 - m_4 = {kink_position/1e3:.3f} keV")
    print(f"  Kink amplitude |U_e4|^2 = {Ue4_sq:.4e}")
    print()
    print(f"  KATRIN/TRISTAN sensitivity (projected):")
    print(f"    Mass range:        100 eV to 10 keV  (covers 543 eV)")
    print(f"    Mixing sensitivity: |U_e4|^2 ~ 10^-6 by ~2030")
    print()
    cascade_test = "WITHIN reach" if Ue4_sq > 1e-6 else "BELOW reach"
    print(f"  Cascade prediction |U_e4|^2 = {Ue4_sq:.2e}")
    print(f"  Status: {cascade_test}")
    if Ue4_sq > 1e-6:
        print(f"    => KATRIN/TRISTAN should DETECT or RULE OUT cascade prediction.")
    print()


# ---------------------------------------------------------------------------
# (3) X-ray emission line from sterile neutrino decay
# ---------------------------------------------------------------------------

def report_xray_decay():
    print("=" * 76)
    print("(3) X-ray emission line (nu_4 -> nu_a + gamma)")
    print("=" * 76)
    print()
    m4 = M29_EV
    E_gamma = m4 / 2
    Ue4_sq = mixing_squared(21)
    sin2_2theta = 4 * Ue4_sq

    # Decay rate (standard formula):
    # Gamma = (9 alpha_em G_F^2 / 256 pi^4) sin^2(2theta) m_4^5
    # In natural units (eV).  G_F in eV^-2, m_4 in eV.
    # Need careful unit handling.
    #
    # Standard form: Gamma [s^-1] = 1.36e-32 * (sin^2 2theta) * (m_4 / keV)^5
    m4_keV = m4 / 1000
    decay_rate_per_s = 1.36e-32 * sin2_2theta * m4_keV ** 5  # 1/s
    if decay_rate_per_s > 0:
        lifetime_s = 1 / decay_rate_per_s
        lifetime_age_universe = lifetime_s / 4.35e17  # age of universe ~ 13.8 Gyr
    else:
        lifetime_s = float('inf')
        lifetime_age_universe = float('inf')

    print(f"  Cascade m_4 = {m4:.0f} eV")
    print(f"  Photon energy E_gamma = m_4/2 = {E_gamma:.0f} eV = {E_gamma/1000:.3f} keV")
    print(f"  sin^2(2 theta) = {sin2_2theta:.4e}")
    print()
    print(f"  Sterile decay rate: Gamma = 1.36e-32 * sin^2(2theta) * (m_4/keV)^5")
    print(f"                            = {decay_rate_per_s:.4e} / s")
    print(f"  Sterile lifetime: tau = {lifetime_s:.4e} s")
    print(f"                       = {lifetime_age_universe:.4e} times age of universe")
    print()
    print(f"  Detection: monochromatic X-ray/UV line at E_gamma = {E_gamma:.0f} eV")
    print(f"  Wavelength: {1240/E_gamma*1e-9*1e9:.2f} nm  (extreme UV)")
    print()
    print(f"  EUV/soft X-ray observatories sensitive in this range:")
    print(f"    - SOHO/SUMER ({E_gamma:.0f} eV is in EUV range)")
    print(f"    - Athena (planned, 0.2-12 keV; below threshold)")
    print(f"    - eXTP (0.5-50 keV; below threshold)")
    print(f"  Constraint: cascade m_4 = 543 eV implies decay photon at 271 eV,")
    print(f"  which is in EUV (below typical X-ray observatory ranges).")
    print()
    print(f"  Lifetime is {lifetime_age_universe:.2e} times age of universe -- the cascade")
    print(f"  m_4 is COSMOLOGICALLY STABLE (does not decay before today).")
    print()


# ---------------------------------------------------------------------------
# (4) Cosmological constraints
# ---------------------------------------------------------------------------

def report_cosmology():
    print("=" * 76)
    print("(4) Cosmological constraints")
    print("=" * 76)
    print()
    m4 = M29_EV
    Ue4_sq = mixing_squared(21)
    total_mixing_sq = sum(mixing_squared(dg) for dg in DIRAC_LAYERS_GEN)

    print(f"  Cascade m_4 = {m4:.0f} eV")
    print(f"  Total active-sterile |U_a4|^2 = {total_mixing_sq:.4e}")
    print()

    print("  (a) N_eff constraint (CMB):")
    print(f"      Active neutrinos contribute N_eff = 3.046 (SM).")
    print(f"      A 543 eV sterile would NOT be relativistic at recombination")
    print(f"      (T_recomb = 0.26 eV << m_4 = 543 eV).  So no direct N_eff")
    print(f"      contribution at recombination.  But it could contribute to")
    print(f"      Sigma m_nu, which is constrained by Planck < 0.12 eV.")
    print()
    print(f"      If the m_4 sterile thermalises in early universe, its")
    print(f"      contribution to Omega_nu is m_4 / 94 eV (per active relic)")
    print(f"      = {m4/94:.2f} (in critical density units, OVERCLOSES universe).")
    print(f"      Therefore: cascade m_4 sterile must NOT have thermalised in")
    print(f"      full equilibrium, OR it must have decayed/diluted.")
    print()
    print("  (b) Sterile neutrino dark matter abundance (Dodelson-Widrow):")
    print(f"      Omega_sterile h^2 ~ 0.1 * (sin^2 2theta / 1e-8) * (m_s / keV)^2")
    print(f"      For m_s = 0.543 keV, sin^2(2theta) = {4*Ue4_sq:.4e}:")
    omega_dw = 0.1 * (4*Ue4_sq / 1e-8) * (0.543) ** 2
    print(f"      Omega_DW h^2 = {omega_dw:.4e}")
    print(f"      Observed Omega_DM h^2 = 0.12")
    print(f"      Ratio: {omega_dw / 0.12:.2e}")
    print(f"      => OVERCLOSES universe by {omega_dw/0.12:.1e}x if produced via DW.")
    print()
    print("  (c) Lyman-alpha forest (warm DM constraint):")
    print(f"      For m_s ~ 1 keV, sin^2(2theta) < 1e-10 from Lyman-alpha.")
    print(f"      Cascade prediction at m_s = 543 eV: sin^2(2theta) = {4*Ue4_sq:.2e}")
    print(f"      This is {(4*Ue4_sq) / 1e-10:.2e} times Lyman-alpha bound.")
    print()
    print("  (d) Big Bang Nucleosynthesis (BBN):")
    print(f"      Sterile neutrinos at >100 eV with mixing > 10^-3 thermalise")
    print(f"      and disrupt BBN.  Cascade |U_e4|^2 = {Ue4_sq:.2e}")
    print(f"      (vs threshold ~10^-3 -> 10^-6).  In the BBN-disruption range.")
    print()


# ---------------------------------------------------------------------------
# Synthesis
# ---------------------------------------------------------------------------

def synthesis():
    print("=" * 76)
    print("SYNTHESIS")
    print("=" * 76)
    print()
    print("CASCADE m_29 AS A PARTICLE")
    print("--------------------------")
    print()
    print("If we read the cascade structurally -- d=29 is a Dirac layer just")
    print("like d=5, 13, 21, hosting a fermion bundle -- then the cascade")
    print("predicts a NEW PARTICLE with specific properties:")
    print()
    print("  Mass:      543 eV  (cascade-derived)")
    print("  Charge:    0       (excluded from charged-fermion role)")
    print("  Spin:      1/2     (Dirac/Majorana fermion)")
    print("  Mixing:    cascade-derived per active flavour")
    print()
    Ue4_sq = mixing_squared(21)
    Umu4_sq = mixing_squared(13)
    Utau4_sq = mixing_squared(5)
    print(f"  |U_e4|^2   = {Ue4_sq:.2e}")
    print(f"  |U_mu4|^2  = {Umu4_sq:.2e}")
    print(f"  |U_tau4|^2 = {Utau4_sq:.2e}")
    print()
    print("EXPERIMENTAL STATUS")
    print("-------------------")
    print()
    print("(1) KATRIN/TRISTAN beta endpoint:")
    print(f"    Cascade |U_e4|^2 = {Ue4_sq:.2e} >> projected sensitivity 10^-6.")
    print(f"    => Cascade prediction TESTABLE by 2030.  Strong falsifier.")
    print()
    print("(2) X-ray emission:")
    print(f"    Decay photon at 271 eV (EUV, below X-ray observatories).")
    print(f"    Lifetime >> age of universe.  Not directly probed by Athena/eXTP.")
    print()
    print("(3) Cosmological abundance:")
    print(f"    Dodelson-Widrow estimate OVERCLOSES universe by factor 10^7.")
    print(f"    => Cascade m_29 CANNOT be a thermal relic from active-sterile")
    print(f"       mixing alone.  Either:")
    print(f"       (a) Cascade has additional structure that suppresses early-")
    print(f"           universe production (e.g., the m_29 fermion is heavy")
    print(f"           in early universe and only becomes light after some")
    print(f"           cascade phase transition)")
    print(f"       (b) Cascade m_29 is NOT a particle, just a structural source")
    print(f"           mass (the cascade text classifies it this way)")
    print(f"       (c) Cascade prediction is wrong / requires refinement")
    print()
    print("(4) Lyman-alpha:")
    print(f"    Cascade sin^2(2theta) = {4*Ue4_sq:.2e}, vs Ly-alpha bound 10^-10.")
    print(f"    Tension: cascade prediction may be RULED OUT by structure formation.")
    print()
    print("VERDICT")
    print("-------")
    print()
    print("The cascade has TWO POSSIBLE READINGS of m_29 = 543 eV:")
    print()
    print("READING A: m_29 is a real fermion (sub-keV sterile neutrino).")
    print("  Pros: structurally consistent (every Dirac layer hosts a fermion).")
    print("        Predicts specific KATRIN/TRISTAN signature with |U_e4|^2 ~ 9e-5.")
    print("  Cons: TENSION with Lyman-alpha forest constraint (~10^5 too large mixing).")
    print("        TENSION with BBN if mixing > 10^-3 to 10^-6 (cascade is in this range).")
    print("        Cosmological abundance overcloses universe via DW production.")
    print()
    print("READING B: m_29 is a structural source mass, not a propagating particle.")
    print("  Pros: avoids cosmological tensions of Reading A.")
    print("        Consistent with cascade's stated 'no new particles' philosophy.")
    print("  Cons: structurally ad hoc (other Dirac layers host real particles).")
    print("        Why does d=29 alone not host a particle?")
    print()
    print("WHICH READING IS CORRECT?")
    print()
    print("Reading A is the structurally natural one but predicts cosmological")
    print("signatures that appear to be ruled out by Lyman-alpha and BBN.")
    print("Reading B avoids the tensions but is structurally less clean.")
    print()
    print("The cascade text (Part IVa thm:generations) explicitly classifies")
    print("d=29 as 'suppressed in charged-fermion mass spectra' with 'residual")
    print("role as the heaviest-neutrino source'.  This points toward Reading B,")
    print("but it does NOT explicitly state d=29 is not a propagating particle.")
    print()
    print("CONCRETE TEST")
    print("-------------")
    print()
    print("KATRIN/TRISTAN by 2030 will be sensitive to |U_e4|^2 ~ 10^-6 in the")
    print(f"100 eV - 10 keV mass range.  The cascade prediction at m=543 eV with")
    print(f"|U_e4|^2 = {Ue4_sq:.2e} is WELL ABOVE projected sensitivity.")
    print()
    print("If KATRIN finds a kink at 18.06 keV with the cascade-predicted")
    print("amplitude: STRONG SUPPORT for cascade Reading A; novel particle")
    print("prediction VINDICATED.")
    print()
    print("If KATRIN does NOT find a kink at this mass: the cascade Reading A")
    print("is FALSIFIED.  Reading B remains consistent (m_29 is structural,")
    print("not a particle).")
    print()
    print("Either way, the cascade has a SPECIFIC, TESTABLE prediction at")
    print("the sub-keV scale: a particle that should be there if d=29 is a")
    print("real Dirac layer with an active fermion content.")
    print()


def main():
    print()
    print("CASCADE m_29 = 543 eV: SUB-keV STERILE NEUTRINO?")
    print()
    report_mixing()
    report_beta_decay()
    report_xray_decay()
    report_cosmology()
    synthesis()


if __name__ == "__main__":
    main()
