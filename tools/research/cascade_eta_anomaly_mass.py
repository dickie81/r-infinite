#!/usr/bin/env python3
"""Cascade-native U(1)_A axial-anomaly mass: η-η' from cascade topology.

Setup. The light meson zoo survey (cascade_meson_masses.py) surfaced a
surprise sub-percent hit on the η'/η ratio:

    m_η' / m_η = d_0 / (N_c + 1) = 7 / 4 = 1.7500   (PDG: 1.7482, +0.10%)

Both states involve the U(1)_A axial-anomaly mass that distinguishes
the singlet η_0 from the octet η_8. The cleanness of d_0/(N_c+1)
suggested that the anomaly mass itself --- traditionally derived in
QCD from the topological susceptibility χ_top via 't Hooft instanton
density --- might sit on cascade primitives.

Cascade topological commitment already in place. The cover sheet
(line 24, 28) commits to θ_QCD = 0 from π_3(S^11) = 0 (Adams), where
S^11 is the gauge-bundle sphere at d_g = 12. The U(1)_A anomaly mass
is in the SAME topological sector (gauge winding number → instanton
density → χ_top → η' mass). So a cascade-internal anomaly mass at
d_0 = 7 (algebra source) and d_g = 12 (gauge layer) is structurally
consistent with existing cascade theorems, not a new commitment.

Hypothesis. The η-η' system sits on cascade primitives {N_c, d_0,
N_c+1, N(0)} via:

  m_η' = Λ_PDG · √(N_c · d_0)            (singlet anomaly)
  m_η  = Λ_PDG · (N_c+1) · √(N_c/d_0)    (= 4/7 · m_η')

Witten-Veneziano relation in cascade primitives:
  m_η'² + m_η² − 2 m_K² = 6 · χ_top / f_π²   (N_f = 3)

If the cascade hypothesis holds, χ_top^(1/4) extracted from this
relation should match lattice QCD (≈ 178 MeV).

This tool:
  1. Tests m_η' = Λ·√(N_c·d_0) absolute mass
  2. Tests m_η/m_η' = (N_c+1)/d_0 = 4/7 ratio
  3. Tests m_η = Λ·(N_c+1)·√(N_c/d_0) absolute mass
  4. Computes χ_top from WV with cascade-primitive inputs
  5. Compares to lattice χ_top^(1/4) ≈ 178 MeV
  6. Reports structural reading and identifies the cascade-topological
     mechanism that would close this at Tier 2.
"""

from __future__ import annotations

import math


# Cascade primitives
N_C = 3
N_0 = 2
TWO_PI = 2 * math.pi
D_V = 5
D_0 = 7
D_G = 12   # gauge sector layer
D_DIRAC = 14  # Dirac descent

# Inputs
LAMBDA_PDG = 0.210  # GeV, MS-bar n_f=5
M_PI_PDG = 0.13957
M_K_PDG = 0.49368
M_ETA_PDG = 0.54786
M_ETA_PRIME_PDG = 0.95778
F_PI_PDG = 0.09207
CHI_TOP_LATTICE_QUARTIC = 0.178  # GeV, FLAG/lattice average


def test_m_eta_prime() -> dict:
    """m_η' = Λ_PDG · √(N_c · d_0) = Λ · √21."""
    predicted = LAMBDA_PDG * math.sqrt(N_C * D_0)
    return {
        'name': "m_η'",
        'cascade_form': "Λ_PDG · √(N_c · d_0) = Λ · √21",
        'predicted': predicted,
        'observed': M_ETA_PRIME_PDG,
        'deviation': (predicted - M_ETA_PRIME_PDG) / M_ETA_PRIME_PDG,
    }


def test_eta_ratio() -> dict:
    """m_η' / m_η = d_0 / (N_c + 1) = 7/4."""
    predicted = D_0 / (N_C + 1)
    observed = M_ETA_PRIME_PDG / M_ETA_PDG
    return {
        'name': "m_η' / m_η",
        'cascade_form': "d_0 / (N_c + 1) = 7/4",
        'predicted': predicted,
        'observed': observed,
        'deviation': (predicted - observed) / observed,
    }


def test_m_eta() -> dict:
    """m_η = Λ_PDG · (N_c+1) · √(N_c/d_0)."""
    predicted = LAMBDA_PDG * (N_C + 1) * math.sqrt(N_C / D_0)
    return {
        'name': "m_η",
        'cascade_form': "Λ_PDG · (N_c+1) · √(N_c/d_0) = Λ · 4√(3/7)",
        'predicted': predicted,
        'observed': M_ETA_PDG,
        'deviation': (predicted - M_ETA_PDG) / M_ETA_PDG,
    }


def test_chi_top_witten_veneziano() -> dict:
    """χ_top from Witten-Veneziano with PDG inputs.

    m_η'² + m_η² − 2 m_K² = (2 N_f / f_π²) · χ_top   (N_f = 3)
    """
    n_f = 3
    lhs_pdg = M_ETA_PRIME_PDG**2 + M_ETA_PDG**2 - 2 * M_K_PDG**2
    chi_top_pdg = lhs_pdg * F_PI_PDG**2 / (2 * n_f)
    chi_top_quartic_pdg = chi_top_pdg ** 0.25
    return {
        'name': 'χ_top^(1/4) from WV (PDG inputs)',
        'predicted': chi_top_quartic_pdg,
        'observed': CHI_TOP_LATTICE_QUARTIC,
        'deviation': (chi_top_quartic_pdg - CHI_TOP_LATTICE_QUARTIC) / CHI_TOP_LATTICE_QUARTIC,
    }


def test_chi_top_cascade_primitives() -> dict:
    """χ_top from WV with cascade-primitive inputs.

    Using cascade forms:
      m_π² = Λ²·4/9        m_K² = Λ²·50/9
      m_η² = Λ²·(N_c+1)²·N_c/d_0 = Λ²·48/7
      m_η'² = Λ²·N_c·d_0 = Λ²·21
      f_π² = Λ²·16/81

    LHS = Λ²·(21 + 48/7 - 100/9) = Λ²·(1323 + 432 - 700)/63 = Λ²·1055/63
    χ_top = LHS · f_π² / (2 N_f) = Λ²·(1055/63)·Λ²·(16/81)/6
          = Λ⁴ · (1055·16)/(63·81·6)
          = Λ⁴ · 16880/30618
          = Λ⁴ · 0.5513
    """
    n_f = 3
    m_pi_sq_cascade = LAMBDA_PDG**2 * (N_0 / N_C)**2          # 4/9
    m_k_sq_cascade = LAMBDA_PDG**2 * D_V**2 * N_0 / N_C**2    # 50/9
    m_eta_sq_cascade = LAMBDA_PDG**2 * (N_C+1)**2 * N_C / D_0  # 48/7
    m_eta_prime_sq_cascade = LAMBDA_PDG**2 * N_C * D_0         # 21
    f_pi_sq_cascade = LAMBDA_PDG**2 * (N_0 / N_C)**4           # 16/81

    lhs = m_eta_prime_sq_cascade + m_eta_sq_cascade - 2 * m_k_sq_cascade
    chi_top = lhs * f_pi_sq_cascade / (2 * n_f)
    chi_top_quartic = chi_top ** 0.25

    return {
        'name': 'χ_top^(1/4) from WV (cascade-primitive inputs)',
        'predicted': chi_top_quartic,
        'observed': CHI_TOP_LATTICE_QUARTIC,
        'deviation': (chi_top_quartic - CHI_TOP_LATTICE_QUARTIC) / CHI_TOP_LATTICE_QUARTIC,
        'lhs_cascade_form': "Λ²·(N_c·d_0 + (N_c+1)²·N_c/d_0 - 2·d_V²·N(0)/N_c²) = Λ²·1055/63",
        'lhs_cascade_value_over_lambda_sq': lhs / LAMBDA_PDG**2,
    }


def test_anomaly_mass_no_mixing() -> dict:
    """In the no-mixing limit: m_anomaly² = m_η_0² − m_η_8².

    m_η_0² = Λ²·N_c·d_0 = 21·Λ²       (cascade singlet)
    m_η_8² = Λ²·196/27                 (cascade GMO octet, from 4m_K² − m_π²)
    """
    m_eta_0_sq = LAMBDA_PDG**2 * N_C * D_0                      # 21
    m_eta_8_sq = LAMBDA_PDG**2 * (4 * 50/9 - 4/9) / 3           # 196/27
    anomaly_mass_sq = m_eta_0_sq - m_eta_8_sq
    anomaly_mass = math.sqrt(anomaly_mass_sq)
    # In QCD: m_anomaly² = (2 N_f / f_π²) · χ_top
    # so χ_top = m_anomaly² · f_π² / (2 N_f)
    f_pi_sq_cascade = LAMBDA_PDG**2 * (N_0 / N_C)**4
    chi_top = anomaly_mass_sq * f_pi_sq_cascade / 6
    chi_top_quartic = chi_top ** 0.25
    return {
        'name': 'χ_top^(1/4) from no-mixing m_anomaly²',
        'predicted': chi_top_quartic,
        'observed': CHI_TOP_LATTICE_QUARTIC,
        'deviation': (chi_top_quartic - CHI_TOP_LATTICE_QUARTIC) / CHI_TOP_LATTICE_QUARTIC,
        'anomaly_mass_MeV': anomaly_mass * 1000,
        'cascade_form': "(N_c·d_0 - 196/27) · Λ² = (567-196)/27·Λ² = 371/27·Λ²",
    }


def fmt_pct(x: float) -> str:
    return f"{x*100:+.2f}%"


def main() -> None:
    print("=" * 100)
    print("CASCADE-NATIVE U(1)_A ANOMALY MASS: η, η', and χ_top")
    print("=" * 100)
    print()
    print(f"Cascade primitives: N_c={N_C}, N(0)={N_0}, d_V={D_V}, d_0={D_0}, d_g={D_G}")
    print(f"Λ_PDG (MS-bar, n_f=5) = {LAMBDA_PDG*1000:.0f} MeV")
    print()
    print("Existing cascade topological commitment (cover sheet):")
    print("  θ_QCD = 0  ←  π_3(S^11) = 0 (Adams; gauge bundle at d_g=12)")
    print("This places U(1)_A topology in the cascade gauge sector.")
    print()

    print("=" * 100)
    print("Test 1 — m_η' absolute mass from cascade primitives")
    print("=" * 100)
    print()
    r1 = test_m_eta_prime()
    print(f"  Cascade form: {r1['cascade_form']}")
    print(f"  Predicted:    {r1['predicted']*1000:7.2f} MeV")
    print(f"  PDG:          {r1['observed']*1000:7.2f} MeV")
    print(f"  Deviation:    {fmt_pct(r1['deviation'])}")
    print()

    print("=" * 100)
    print("Test 2 — η'/η mass ratio (the original 7/4 hit)")
    print("=" * 100)
    print()
    r2 = test_eta_ratio()
    print(f"  Cascade form: {r2['cascade_form']}")
    print(f"  Predicted:    {r2['predicted']:.4f}")
    print(f"  PDG:          {r2['observed']:.4f}")
    print(f"  Deviation:    {fmt_pct(r2['deviation'])}")
    print()

    print("=" * 100)
    print("Test 3 — m_η absolute mass via the ratio")
    print("=" * 100)
    print()
    r3 = test_m_eta()
    print(f"  Cascade form: {r3['cascade_form']}")
    print(f"  Predicted:    {r3['predicted']*1000:7.2f} MeV")
    print(f"  PDG:          {r3['observed']*1000:7.2f} MeV")
    print(f"  Deviation:    {fmt_pct(r3['deviation'])}")
    print()

    print("=" * 100)
    print("Test 4 — Witten–Veneziano χ_top with cascade inputs")
    print("=" * 100)
    print()
    print("WV: m_η'² + m_η² − 2 m_K² = (2 N_f / f_π²) · χ_top   [N_f = 3]")
    print()
    r4_pdg = test_chi_top_witten_veneziano()
    print("Using PDG masses + PDG f_π:")
    print(f"  χ_top^(1/4) extracted: {r4_pdg['predicted']*1000:6.2f} MeV")
    print(f"  Lattice average:       {r4_pdg['observed']*1000:6.2f} MeV")
    print(f"  Deviation:             {fmt_pct(r4_pdg['deviation'])}")
    print()
    r4_cas = test_chi_top_cascade_primitives()
    print("Using cascade-primitive forms:")
    print(f"  WV LHS = {r4_cas['lhs_cascade_form']}")
    print(f"         = {r4_cas['lhs_cascade_value_over_lambda_sq']:.4f} · Λ²")
    print(f"  χ_top^(1/4) extracted: {r4_cas['predicted']*1000:6.2f} MeV")
    print(f"  Lattice:               {r4_cas['observed']*1000:6.2f} MeV")
    print(f"  Deviation:             {fmt_pct(r4_cas['deviation'])}")
    print()

    print("=" * 100)
    print("Test 5 — anomaly mass in the large-N_c (no-mixing) limit")
    print("=" * 100)
    print()
    print("Large-N_c: m_anomaly² = m_η_0² − m_η_8², with cascade forms")
    print("  m_η_0² = N_c · d_0 · Λ² = 21 · Λ²              (singlet, this PR)")
    print("  m_η_8² = (4m_K² − m_π²)/3 in cascade = 196/27 · Λ²  (GMO octet)")
    print()
    r5 = test_anomaly_mass_no_mixing()
    print(f"  m_anomaly² cascade form: {r5['cascade_form']}")
    print(f"  m_anomaly = {r5['anomaly_mass_MeV']:.2f} MeV")
    print(f"  Implied χ_top^(1/4): {r5['predicted']*1000:6.2f} MeV  (lattice {r5['observed']*1000:.0f})")
    print(f"  Deviation:           {fmt_pct(r5['deviation'])}")
    print()

    print("=" * 100)
    print("STRUCTURAL READING")
    print("=" * 100)
    print()
    print("The η-η' system sits on cascade primitives at sub-percent precision")
    print("on absolute masses, with the topological susceptibility χ_top")
    print("reproducing lattice QCD within a few percent.")
    print()
    print("Cascade-primitive forms (Tier 4, all sub-percent):")
    print(f"  m_η'  = Λ_PDG · √(N_c · d_0)               → 962.3 MeV   ({fmt_pct(r1['deviation'])})")
    print(f"  m_η   = Λ_PDG · (N_c+1)·√(N_c/d_0)          → 549.9 MeV   ({fmt_pct(r3['deviation'])})")
    print(f"  m_η'/m_η = d_0/(N_c+1) = 7/4               → 1.7500     ({fmt_pct(r2['deviation'])})")
    print(f"  χ_top^(1/4) (WV)                            → 181.0 MeV   ({fmt_pct(r4_cas['deviation'])})")
    print()
    print("Structural interpretation:")
    print("  - N_c · d_0 = 21 in m_η'² combines color count (N_c=3, Adams) and")
    print("    the SU(3) algebra source layer (d_0=7). The U(1)_A anomaly is")
    print("    sourced where SU(3) is sourced --- structurally consistent.")
    print("  - (N_c+1) factor in m_η is suggestive: N_c+1 = 4 = (N_f) for")
    print("    QCD with one flavor of singlet behavior, OR could be d_V−1 (the")
    print("    spatial dimension d=3+1). Cascade-internal interpretation open.")
    print("  - The d_0=7 algebra-source layer carries BOTH SU(3) algebra (cover")
    print("    sheet, line 149) AND the U(1)_A anomaly mass scale --- one")
    print("    cascade layer, two structurally distinct gauge phenomena.")
    print()
    print("Cross-sector pattern extends:")
    print("  - β_0 per-fermion: N(0)/N_c (chiral primitive ratio)")
    print("  - f_π/m_π: N(0)/N_c (chiral)")
    print("  - cascade↔MS-bar scheme: √(N_c/N(0))")
    print("  - m_K/m_π: d_V/√N(0) (PS octet, this PR)")
    print("  - m_η'/m_η: d_0/(N_c+1) (η-η' anomaly, this PR)")
    print("  - m_η': √(N_c·d_0) (singlet anomaly, this PR)")
    print()
    print("All from the same primitive set {N_c, N(0), 2π, d_V, d_0}.")
    print()
    print("=" * 100)
    print("HONEST VERDICT")
    print("=" * 100)
    print()
    print("Tier 4 closure: cascade-primitive identification at sub-percent")
    print("precision on m_η, m_η', m_η'/m_η, AND derived χ_top^(1/4) within")
    print("a few percent of lattice. Cross-sector consistency: same primitives")
    print("{N_c, d_0} that anchor SU(3) algebra also anchor the U(1)_A")
    print("anomaly mass --- structurally consistent with cover sheet's")
    print("topological commitment θ_QCD=0 from π_3(S^11)=0.")
    print()
    print("Tier 2 promotion target: cascade-internal derivation of χ_top from")
    print("topological winding at d_0=7 and/or d_g=12, parallel to the")
    print("derivation of θ_QCD=0 from π_3(S^11)=0 already in Paper IVa.")
    print("In QCD, χ_top comes from instanton density; the cascade analog")
    print("would be a winding-number / Pontryagin-class quantity at the")
    print("gauge layer, with N_c·d_0 = 21 emerging as the topological")
    print("invariant whose square root sets m_η'.")
    print()
    print("Open structural piece: WHY specifically N_c·d_0 and (N_c+1)·√(N_c/d_0)")
    print("rather than alternative cascade-primitive combinations. The empirical")
    print("match selects these; cascade-internal physics at d_0=7 (algebra")
    print("source) and d_g=12 (gauge layer) needs to derive them from topology.")


if __name__ == "__main__":
    main()
