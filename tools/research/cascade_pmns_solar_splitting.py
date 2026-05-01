#!/usr/bin/env python3
"""
Roadmap item 2: cascade PMNS / solar splitting derivation.

CONTEXT
=======
Cascade neutrino diagonal predictions (Part IVb):
    m_g = m_29 * alpha(d_g) / chi^(29-d_g)
with d_g in {21, 13, 5} for Gen 1, 2, 3.

Numerical:
    m_1 = 0.0493 eV  (matches sqrt(Delta m^2_atm) = 0.0495 at -1.0%)  ✓
    m_2 = 3.07e-4 eV  (Gen 2; way smaller than required for solar)
    m_3 = 2.93e-6 eV  (Gen 3; vanishing in cascade diagonal)

Cascade gives:
    Delta m^2_atm = m_1^2 - m_2^2 ≈ m_1^2 = 2.43e-3 eV^2  ✓ (matches 2.45e-3)
    Delta m^2_sol = m_2^2 - m_3^2 ≈ m_2^2 = 9.4e-8 eV^2  ✗ (observed 7.5e-5)

Solar splitting undershoots by FACTOR 800.

OBSERVED PMNS
=============
Mass eigenvalues (NH):
    m_1^obs ≈ sqrt(m_2^2 + Delta m^2_atm) ≈ 0.0503 eV
    m_2^obs = sqrt(Delta m^2_sol + m_3^2) ≈ sqrt(7.5e-5) = 0.0086 eV (if m_3 ≈ 0)
    m_3^obs = small (< 0.05 eV)

Mixing angles:
    sin^2(theta_12) = 0.31  (solar)        — LARGE (~33°)
    sin^2(theta_23) = 0.55  (atmospheric)  — LARGE (~45°)
    sin^2(theta_13) = 0.022 (reactor)      — SMALL (~8.6°)

Compare to CKM (quark mixing, also handled by cascade):
    Cabibbo theta_C ≈ 13°  — SMALL
    All CKM angles small.

WHY ARE NEUTRINO ANGLES LARGE BUT CKM ANGLES SMALL?
====================================================
This is one of the cascade-native questions Roadmap item 2 implicitly asks.

Cascade Cabibbo formula (Theorem cabibbo-amplitude):
    tan(theta_C) = exp(-p(13)/2)
giving small angle from geometric mean of two diagonal amplitudes 1 and exp(-p(13)).

For neutrinos, this geometric-mean form gives SMALL angles too:
    tan(theta_PMNS_12) = exp(-(Phi(21) - Phi(13))/2) ≈ exp(-2.5) ≈ 0.08
    theta = 4.7°  — much smaller than observed 33°

So the cascade's CKM-style geometric-mean rule does NOT extend to neutrinos.

CASCADE-NATIVE MECHANISMS AVAILABLE
====================================
Per CLAUDE.md Check 7, semiclassical mechanisms (Green's functions on
cascade spheres, KK mode integration) are out of bounds.  Available
cascade-native ingredients for inter-generation mixing:

  (M1) Gram correction (Part 0 Supplement): cumulative path Gram deficit
       sum_{adj} (1 - C^2_{d, d+1}) along generation-layer descent.
  (M2) Path-tensor structure (Part IVa rem:path-tensor):
       V_12 (x) V_13 (x) V_14 matter content.
  (M3) Cascade chirality theorem (Theorem chirality-factorisation):
       chi=2 basins per Dirac layer; mixing across basins is
       structurally distinct from open-line chirality filtering.
  (M4) Multi-source cascade descent: each generation could be sourced
       from a different higher Bott layer (d=29 -> Gen 1, d=37 -> Gen 2, etc.)
       — but this conflicts with the structural reading that
       d>=29 is suppressed (Part IVa thm:generations).
  (M5) Cascade scalar action overlap (Remark action-uniqueness):
       inter-layer scalar field overlap.

This script tests several candidate combinations.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Close the OQ.  No clean cascade-native mechanism for solar
    splitting falls out structurally from these tests.
  - Invoke semiclassical mixing (Bogoliubov, KK reduction).
  - Force a fit: only structural cascade combinations are tested.

If all tests fail (negative), the cascade has a genuine open structural
piece for neutrino mixing that requires NEW cascade machinery (most
likely a cascade-native PMNS analog, structurally distinct from the
geometric-mean Cabibbo rule).
"""

from __future__ import annotations

import math


def R_cascade(d: int) -> float:
    return math.exp(math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0))


def alpha_cascade(d: int) -> float:
    return R_cascade(d) ** 2 / 4.0


def p_cascade(d: int) -> float:
    a = (d + 1) / 2.0
    if abs(a - round(a)) < 1e-10:
        n = int(round(a))
        gamma = 0.5772156649015329
        psi = -gamma + sum(1.0 / k for k in range(1, n))
    else:
        n = int(a - 0.5)
        gamma = 0.5772156649015329
        psi = -gamma - 2 * math.log(2) + 2 * sum(1.0 / (2 * k + 1) for k in range(n))
    return 0.5 * psi - 0.5 * math.log(math.pi)


def Phi_cascade(d: int, d_min: int = 5) -> float:
    return sum(p_cascade(dd) for dd in range(d_min, d + 1))


def gram_C2(d: int) -> float:
    """C^2_{d, d+1} via Beta-function ratio (Part 0 Supplement)."""
    log_B = lambda a, b: math.lgamma(a) + math.lgamma(b) - math.lgamma(a + b)
    return math.exp(2 * log_B(0.5, d + 1.5) - log_B(0.5, d + 1) - log_B(0.5, d + 2))


def gram_path_sum(d_min: int, d_max: int) -> float:
    return sum(1.0 - gram_C2(d) for d in range(d_min, d_max))


CHI = 2
M29_EV = 543.0
DIRAC_LAYERS_GEN = [21, 13, 5]  # Gen 1, 2, 3

# Observed values (NuFIT 2024)
DM2_ATM = 2.45e-3   # eV^2
DM2_SOL = 7.5e-5    # eV^2
SQRT_DM2_ATM = math.sqrt(DM2_ATM)
SQRT_DM2_SOL = math.sqrt(DM2_SOL)
SIN2_THETA_12 = 0.31
SIN2_THETA_23 = 0.55
SIN2_THETA_13 = 0.022

# Cascade diagonal masses
def cascade_m_diag(d_g: int) -> float:
    return M29_EV * alpha_cascade(d_g) / (CHI ** (29 - d_g))


def main():
    print("=" * 78)
    print("Roadmap item 2: cascade PMNS / solar splitting candidate mechanisms")
    print("=" * 78)
    print()

    # ---- Step 0: cascade diagonal vs observed ----
    print("STEP 0: cascade diagonal vs observed neutrino spectrum")
    print("-" * 78)
    print(f"  {'Gen':>4}  {'d_g':>4}  {'cascade m_diag (eV)':>20}  {'observed m (eV)':>16}")
    for i, dg in enumerate(DIRAC_LAYERS_GEN):
        m = cascade_m_diag(dg)
        if i == 0:
            obs = SQRT_DM2_ATM
        elif i == 1:
            obs = SQRT_DM2_SOL
        else:
            obs = 0.0  # m_3 unconstrained from below in NH
        print(f"  {i+1:>4}  {dg:>4}  {m:>20.4e}  {obs:>16.4e}")
    print()
    m1, m2, m3 = [cascade_m_diag(d) for d in DIRAC_LAYERS_GEN]
    dm2_atm_cas = m1**2 - m2**2
    dm2_sol_cas = m2**2 - m3**2
    print(f"  Cascade Delta m^2_atm = {dm2_atm_cas:.4e} eV^2  (obs {DM2_ATM:.4e}, {dm2_atm_cas/DM2_ATM*100-100:+.2f}%)")
    print(f"  Cascade Delta m^2_sol = {dm2_sol_cas:.4e} eV^2  (obs {DM2_SOL:.4e}, ratio {dm2_sol_cas/DM2_SOL:.2e})")
    print()
    print(f"  Solar splitting MISMATCH: cascade undershoots by factor {DM2_SOL/dm2_sol_cas:.0f}.")
    print()

    # ---- Step 1: try cascade Cabibbo geometric-mean rule ----
    print("STEP 1: Cabibbo-style geometric-mean rule for PMNS_12")
    print("-" * 78)
    print(f"  Cascade Cabibbo (Theorem cabibbo-amplitude):")
    print(f"    tan(theta_C) = exp(-p(13)/2), p(13) = {p_cascade(13):.4f}")
    print(f"    theta_C = {math.degrees(math.atan(math.exp(-p_cascade(13)/2))):.2f} deg")
    print()
    print(f"  Generalised to PMNS_12 (Gen 1 <-> Gen 2):")
    delta_phi_12 = Phi_cascade(21) - Phi_cascade(13)
    tan_theta = math.exp(-delta_phi_12 / 2)
    theta_deg = math.degrees(math.atan(tan_theta))
    print(f"    tan(theta_12) = exp(-(Phi(21)-Phi(13))/2)")
    print(f"                  = exp(-{delta_phi_12:.4f}/2) = {tan_theta:.4f}")
    print(f"    theta_12 = {theta_deg:.2f} deg")
    print()
    print(f"  Observed solar mixing: theta_12 ≈ 33.4°  (sin^2 = 0.31)")
    print(f"  Cabibbo geometric-mean form gives theta_12 ≈ {theta_deg:.1f}° -- WAY TOO SMALL")
    print()
    print(f"  CONCLUSION: cascade Cabibbo rule does NOT extend to neutrino solar mixing.")
    print(f"  CKM angles small + PMNS angles large means cascade has DIFFERENT mechanism")
    print(f"  for the two sectors.  Identifying the cascade-native PMNS mechanism is the")
    print(f"  remaining structural piece.")
    print()

    # ---- Step 2: Gram-overlap mixing ----
    print("STEP 2: Gram-overlap inter-generation mixing")
    print("-" * 78)
    gram_path_13_21 = gram_path_sum(13, 21)
    print(f"  Cumulative Gram deficit along d=13..21: {gram_path_13_21:.6f}")
    print()
    print(f"  Tested candidate: M_12 (off-diagonal mass) = m_1 * gram_path_13_21")
    M_12_test = m1 * gram_path_13_21
    print(f"    = {m1:.4e} * {gram_path_13_21:.6f} = {M_12_test:.4e} eV")
    print()
    M_12_required = DM2_SOL / (2 * m1)  # small-mixing approximation
    print(f"  Required M_12 (small-mixing): Delta m^2_sol / (2 m_1) = {M_12_required:.4e} eV")
    print(f"  Cascade Gram-overlap M_12 / required: {M_12_test/M_12_required:.4f}")
    print()
    print(f"  Cascade Gram path-overlap is factor {M_12_required/M_12_test:.1f} TOO SMALL.")
    print(f"  Plus: this is small-mixing approximation; observed solar mixing is LARGE")
    print(f"  (33°), invalidating the small-mixing setup entirely.")
    print()

    # ---- Step 3: chirality basin mixing ----
    print("STEP 3: chirality-basin mixing (cascade chirality theorem)")
    print("-" * 78)
    print(f"  Hypothesis: large PMNS angles come from chi=2 basin mixing at Dirac layers.")
    print(f"  In CKM, gauge selects ONE chirality basin -> small mixing.")
    print(f"  In PMNS, neutrinos couple to BOTH basins -> large mixing.")
    print()
    print(f"  Maximal mixing from a 2-basin structure: theta = 45° (sin^2 = 0.5)")
    print(f"  Observed theta_12 = 33.4° (sin^2 = 0.31) — close to bimaximal but not quite.")
    print(f"  Observed theta_23 = 45° (sin^2 = 0.55)  — bimaximal.")
    print(f"  Observed theta_13 = 8.6° (sin^2 = 0.022) — SMALL, unlike other two.")
    print()
    print(f"  STRUCTURE: theta_23 ≈ maximal (chirality-symmetric mixing), theta_13 small.")
    print(f"  This is qualitatively the right pattern for a chirality-basin mechanism")
    print(f"  with one suppressed direction.")
    print()
    print(f"  Quantitative cascade derivation: NOT YET ARTICULATED.  The cascade chirality")
    print(f"  theorem gives factor 1/chi for OPEN-LINE filters, not directly mixing angles.")
    print(f"  Open: cascade-native bridge between chirality theorem and PMNS angle structure.")
    print()

    # ---- Step 4: m_2 mass — what cascade descent gives observed? ----
    print("STEP 4: what cascade descent would give observed m_2 = 0.0086 eV?")
    print("-" * 78)
    target = SQRT_DM2_SOL
    print(f"  Target: m_2 = {target:.4f} eV")
    print(f"  Cascade form m_29 * alpha(d) / chi^k = {target}")
    print()
    print(f"  m_29 * alpha(13) / chi^k:")
    for k in range(8, 16):
        val = M29_EV * alpha_cascade(13) / (CHI ** k)
        dev = (val - target) / target * 100
        print(f"    k={k}: {val:.4e} eV  (dev {dev:+.2f}%)")
    print()
    print(f"  Cascade descent factors don't naturally give 0.0086 eV at integer chi^k.")
    print(f"  Closest: alpha(13)/chi^11 = 0.037/2048 ~ 1.8e-5; m_29 * = 9.8e-3 (14% off)")
    print(f"  But k=11 isn't a Bott-period multiple (= chi^8).  Non-structural.")
    print()

    # ---- Step 5: status ----
    print("STATUS")
    print("-" * 78)
    print()
    print(f"  No clean cascade-native mechanism tested here closes the solar splitting:")
    print(f"  - Cabibbo geometric-mean rule: too small (~5° vs 33°)")
    print(f"  - Gram-overlap mixing: too small (factor 4)")
    print(f"  - Chirality-basin mixing: qualitatively right (theta_23 ≈ max), but no")
    print(f"    quantitative cascade-native bridge to PMNS angle structure")
    print(f"  - Modified m_2 cascade descent: no integer chi^k matches observation")
    print()
    print(f"  THE OPEN STRUCTURAL PIECE:")
    print(f"  The cascade lacks a derivation for neutrino-sector mixing that gives")
    print(f"  - Large theta_12, theta_23 (chirality-basin scale)")
    print(f"  - Small theta_13 (one suppressed direction)")
    print(f"  - Solar splitting magnitude Delta m^2_sol = 7.5e-5 eV^2")
    print()
    print(f"  Per CLAUDE.md Check 7, semiclassical procedures (Bogoliubov mixing, KK")
    print(f"  reduction over compactified dimensions) are out of bounds; the resolution")
    print(f"  must come from cascade-internal structure (chirality theorem extensions,")
    print(f"  cascade scalar action's inter-layer overlap, or path-tensor matrices).")
    print()
    print(f"  This is a GENUINE open question — Roadmap item 2 stands open at the")
    print(f"  cascade-native level; no simple closure available from existing")
    print(f"  cascade ingredients.")
    print()


if __name__ == "__main__":
    main()
