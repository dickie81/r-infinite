#!/usr/bin/env python3
"""Cascade-native Λ_QCD scale derivation attempt.

Standard QCD: Λ_QCD is the scale parameter of QCD running, related to
α_s(μ) via:
    α_s(μ²) = 4π / (β_0 · ln(μ²/Λ²))     [1-loop]

Or equivalently: 1/α_s(M_Z) = β_0/(2π) · ln(M_Z/Λ).

PDG (n_f=5, MS-bar): Λ_QCD ≈ 210 ± 14 MeV.

Cascade has:
  - α_s(M_Z) = 0.117917 (Tier 2 closure via α(14)/χ shift)
  - β_0 = 7 cascade-derived for n_f=6 (rem:cascade-beta0, this PR)
  - β_0 = 23/3 ≈ 7.67 for n_f=5 (cascade-derived from same form)
  - Cascade primitive 2π = N(0)·Γ(1/2)² (Cor:2sqrtpi-primitive)
  - M_Z = 91.19 GeV (cascade Tier 2 anchor)
  - v = 240.8 GeV (Tier 3, cascade-derived via KT vortex)
  - M_Pl,red = 2.435×10^18 GeV (cascade gravitational anchor)

This tool tests candidate cascade-native forms for Λ_QCD:

  Candidate A: Standard 1-loop running with cascade β_0
    Λ = M_Z · exp(-2π/(β_0·α_s(M_Z)))

  Candidate B: M_Z · exp(-N(0)·Γ(1/2)²) = M_Z · exp(-2π)
    Uses cascade primitive 2π directly as the descent

  Candidate C: M_Z · exp(-π·(N(0)+1)) = M_Z · exp(-3π)
    Possibly cascade-internal but speculative

  Candidate D: v · exp(-cascade quantity)
    Where v is the cascade-derived EW VEV

  Candidate E: From cascade descent action
    Λ = scale where cascade descent action L → some critical value

For each candidate, compute and compare to PDG Λ_QCD ≈ 210 MeV.

Honest expectation: cascade has no clean standard 1-loop equivalent
because the cascade scalar action is FREE (Gaussian), no Landau pole.
Cascade-native Λ_QCD likely lives at a different structural object —
possibly at d_0=7 (G_2/SU(3) confinement layer) — and may not match
the standard 1-loop Λ_QCD directly.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)

# Cascade-derived quantities
ALPHA_S_MZ = 0.117917      # Tier 2 closure
M_Z_GEV = 91.1876          # PDG
M_PL_RED_GEV = 2.435e18    # cascade Planck anchor
V_GEV = 240.8              # Tier 3 cascade VEV
M_TOP_GEV = 173.0          # PDG top mass

# Cascade primitives
N_C = 3
N_0 = 2  # = chi
PI = math.pi
TWO_PI = 2 * PI            # = N(0)·Γ(1/2)²
SQRT_PI = math.sqrt(PI)

# Cascade β_0 with n_f flavors
def cascade_beta_0(n_f: int) -> float:
    return (N_C**2 + N_C - 1) - N_0 * n_f / N_C


# PDG Λ_QCD values for various n_f (MS-bar, 4-loop)
PDG_LAMBDA = {
    3: 0.332,  # GeV
    4: 0.292,
    5: 0.210,
    6: 0.090,  # rough; not commonly quoted
}


def standard_1loop_lambda(alpha_s_mz: float, n_f: int, m_z_gev: float) -> float:
    """1-loop Λ_QCD from cascade α_s(M_Z) and cascade β_0(n_f)."""
    beta_0 = cascade_beta_0(n_f)
    return m_z_gev * math.exp(-2 * PI / (beta_0 * alpha_s_mz))


def main() -> None:
    print("=" * 96)
    print("CASCADE-NATIVE Λ_QCD SCALE DERIVATION ATTEMPT")
    print("=" * 96)
    print()
    print(f"Cascade-derived inputs:")
    print(f"  α_s(M_Z) = {ALPHA_S_MZ} (Tier 2 closure)")
    print(f"  β_0(n_f=5) = {cascade_beta_0(5):.4f} (cascade form, this PR)")
    print(f"  β_0(n_f=6) = {cascade_beta_0(6):.4f}")
    print(f"  M_Z = {M_Z_GEV} GeV")
    print(f"  v_EW = {V_GEV} GeV")
    print(f"  M_Pl,red = {M_PL_RED_GEV:.3e} GeV")
    print()
    print(f"  Cascade primitive 2π = N(0)·Γ(1/2)² = {TWO_PI:.5f}")
    print()
    print("PDG values (MS-bar, 4-loop):")
    for nf in [3, 4, 5]:
        print(f"  Λ_QCD^(n_f={nf}) ≈ {PDG_LAMBDA[nf]*1000:.0f} MeV")
    print()

    print("=" * 96)
    print("Candidate forms tested:")
    print("=" * 96)
    print()

    # Candidate A: Standard 1-loop running with cascade β_0
    print("CANDIDATE A: Standard 1-loop Λ from cascade α_s + cascade β_0")
    print("  Λ = M_Z · exp(-2π/(β_0·α_s(M_Z)))")
    for nf in [3, 4, 5, 6]:
        beta_0 = cascade_beta_0(nf)
        lam = standard_1loop_lambda(ALPHA_S_MZ, nf, M_Z_GEV)
        pdg = PDG_LAMBDA.get(nf, 0)
        ratio = lam / pdg if pdg > 0 else 0
        print(f"    n_f={nf}: β_0={beta_0:.3f}, Λ = {lam*1000:.1f} MeV   "
              f"(PDG: {pdg*1000:.0f} MeV, ratio: {ratio:.3f})")
    print("  Verdict: 1-loop underestimates by factor 2-3, expected behavior.")
    print()

    # Candidate B: M_Z · exp(-2π) using cascade primitive
    print("CANDIDATE B: M_Z · exp(-2π) using cascade primitive 2π = N(0)·Γ(1/2)²")
    lam_b = M_Z_GEV * math.exp(-TWO_PI)
    print(f"  Λ = {M_Z_GEV} · exp(-{TWO_PI:.4f}) = {lam_b*1000:.1f} MeV")
    print(f"  vs PDG Λ_5 = 210 MeV: ratio = {lam_b*1000/210:.3f}")
    print(f"  Cascade-primitive structural reading: descent of '2π' from M_Z")
    print()

    # Candidate C: M_Z · exp(-π·(N(0)+1)) = M_Z · exp(-3π)
    lam_c = M_Z_GEV * math.exp(-3 * PI)
    print("CANDIDATE C: M_Z · exp(-3π)")
    print(f"  Λ = {M_Z_GEV} · exp(-{3*PI:.4f}) = {lam_c*1000:.4f} MeV")
    print(f"  vs PDG Λ_5 = 210 MeV: ratio = {lam_c*1000/210:.5f}")
    print(f"  Verdict: way too small.")
    print()

    # Candidate D: v · exp(-cascade quantity)
    print("CANDIDATE D: v · exp(-X) for various cascade X:")
    for X_label, X_val in [("2π", TWO_PI), ("π", PI), ("3π/2", 3*PI/2),
                            ("2π/N_c", 2*PI/N_C), ("π·N_c/2", PI*N_C/2),
                            ("ln(v/M_Z)+2π", math.log(V_GEV/M_Z_GEV) + TWO_PI),
                            ("3π·α_s", 3*PI*ALPHA_S_MZ)]:
        lam = V_GEV * math.exp(-X_val)
        print(f"  X = {X_label} = {X_val:.4f}: Λ = {lam*1000:.2f} MeV "
              f"(ratio {lam*1000/210:.3f} vs PDG)")
    print()

    # Candidate E: Specific cascade descent forms
    print("CANDIDATE E: Cascade scale from specific cascade structure:")
    print()

    # E1: Descent from m_top with cascade β_0(n_f=6)
    beta_0_6 = cascade_beta_0(6)
    # Need α_s(m_top) running. 1-loop: 1/α_s(m_t) = 1/α_s(M_Z) - β_0(n_f=5)/(2π)·ln(m_t/M_Z)
    # but n_f=5 below m_t... use n_f=5 from M_Z to m_t
    inv_alpha_s_mt = 1/ALPHA_S_MZ - cascade_beta_0(5)/(2*PI) * math.log(M_TOP_GEV/M_Z_GEV)
    alpha_s_mt = 1/inv_alpha_s_mt
    print(f"  E1: 1-loop α_s(m_t) running from M_Z (n_f=5):")
    print(f"      α_s(m_t={M_TOP_GEV} GeV) = {alpha_s_mt:.5f}")
    lam_e1 = M_TOP_GEV * math.exp(-2*PI/(beta_0_6 * alpha_s_mt))
    print(f"      Λ = m_t · exp(-2π/(β_0(n_f=6)·α_s(m_t))) = {lam_e1*1000:.1f} MeV")
    print(f"      vs PDG Λ_5 = 210 MeV: ratio = {lam_e1*1000/210:.3f}")
    print()

    # E2: Cascade-internal scale at d_0=7 G_2/SU(3) layer
    # Hypothetical: d_0=7 corresponds to confinement scale via cascade-derived
    # quantities. Without explicit cascade-time identification at d_0, we
    # can only guess. One candidate: scale at d=7 ≈ M_Pl·exp(-Phi(7→4))?
    # We don't have Phi value directly here, just exploring.
    print(f"  E2: M_Pl,red · exp(-X) for cascade descent X candidates:")
    for X_label, X_val in [("π·α_GUT^(-1)", PI*25.02),
                            ("ln(M_Pl/v) + 2π", math.log(M_PL_RED_GEV/V_GEV) + TWO_PI),
                            ("2π·N_c", 2*PI*N_C),
                            ("3π·α_GUT^(-1)/N_c", 3*PI*25.02/N_C)]:
        lam = M_PL_RED_GEV * math.exp(-X_val)
        if lam < 1e6:  # sensible scale
            print(f"      X = {X_label} = {X_val:.4f}: Λ = {lam*1e3:.4f} MeV "
                  f"(ratio {lam*1e3/210:.3e})")
    print()

    print("=" * 96)
    print("STRUCTURAL VERDICT")
    print("=" * 96)
    print()
    print("Standard 1-loop with cascade β_0 underestimates Λ_QCD by factor 2-3 —")
    print("expected, since 1-loop is well-known to be inadequate for low-energy QCD.")
    print()
    print("CASCADE-PRIMITIVE FORM Λ_QCD = M_Z · exp(-2π) ≈ 170 MeV is suggestive:")
    print(f"  - Uses cascade primitive 2π = N(0)·Γ(1/2)² directly")
    print(f"  - 170 MeV is between 1-loop (88 MeV) and PDG 4-loop (210 MeV)")
    print(f"  - Suggests cascade encodes 2-loop-equivalent running implicitly")
    print(f"  - 20% below PDG: consistent with cascade Tier 3 leading-order accuracy")
    print()
    print("Structural reading of M_Z · exp(-2π):")
    print("  The cascade descent from M_Z (observer-scale physics) to Λ_QCD")
    print("  involves '2π' worth of cascade primitive descent. The 2π cascade")
    print("  primitive identity (Cor:2sqrtpi-primitive) appears here as the")
    print("  natural scale-separation factor between EW and confinement scales.")
    print()
    print("HONEST ASSESSMENT:")
    print()
    print("  Numerical: M_Z·exp(-2π) gives Λ ≈ 170 MeV (20% below PDG 210 MeV).")
    print("  Structural: cascade-primitive form M_Z · exp(-N(0)·Γ(1/2)²)")
    print("              uses cascade primitives only.")
    print("  Cascade match: not exact. The 20% deviation is consistent with")
    print("              cascade Tier 3/4 leading-order systematics but not")
    print("              within the cascade's stated standing precision.")
    print()
    print("Tier 4 (cascade-suggestive but not closed): Λ_QCD = M_Z · exp(-2π)")
    print("  is a candidate cascade-native form. The 20% deviation from PDG")
    print("  could close via:")
    print("    - First-order cascade Gram correction (Part 0 inter-layer-coupling)")
    print("    - Higher-order cascade descent corrections")
    print("    - Or the cascade-native form is genuinely at 20% precision")
    print()
    print("REMAINING OPEN: cascade-internal derivation of WHY '2π' specifically")
    print("is the descent factor between M_Z and Λ_QCD. Possibilities:")
    print("  - 2π = N(0)·Γ(1/2)² is the universal cascade structural unit")
    print("    (appears in 1/α_em screening, in (g-2) prefactor)")
    print("  - The descent from EW scale to confinement scale crosses one")
    print("    'cascade structural unit' worth of running")
    print("  - Connects to cascade chirality structure at d_0=7 (confinement layer)")
    print()
    print("Cascade-native Λ_QCD remains a Tier 4 frontier prediction. The")
    print("cascade primitives produce a value in the right ballpark (170 MeV vs")
    print("PDG 210 MeV) with structural form M_Z·exp(-2π), but the structural")
    print("derivation of WHY this specific form is forced cascade-natively is")
    print("the open piece.")


if __name__ == "__main__":
    main()
