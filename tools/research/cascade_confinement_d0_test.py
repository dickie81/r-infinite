#!/usr/bin/env python3
"""Test: is d_0=7 cascade-natively the QCD confinement layer?

Cascade structural commitments:
  - SU(3) at d_g=12 (gauge-window, Part IVa Theorem adams-unique)
  - SU(3) at d_0=7 via G_2/SU(3) on S^6 (Part IVa rem:su3-d7-algebra)
  - Cascade Λ_QCD candidate: M_Z · exp(-2π) ≈ 170 MeV (this PR's
    rem:cascade-beta0)

The conjecture: d_0=7 is the cascade's confinement layer. Standard
QCD has Λ_QCD as the scale where α_s diverges (1-loop Landau pole)
or non-perturbative effects dominate. The cascade has SU(3) sourced
structurally at d_0=7 via G_2/SU(3). If d_0=7 corresponds to the
confinement scale Λ_QCD, then:

  cascade descent from M_Z (at d ≈ 4 effectively) to d_0=7 should
  correspond to the 2π factor in Λ_QCD = M_Z · exp(-2π)

Test setup:
  Compute cascade descent action Φ(d_a, d_b) between key layers:
  - Φ(d_g=12, d_0=7): gauge-window to algebra-source (cascade
    SU(3) running between its two layers)
  - Φ(d_g=12, d=4): descent through observer (used in α_s closure)
  - Φ(d_0=7, d=4): from algebra source to observer
  - Φ(d_g=12, d=4) - Φ(d_0=7, d=4) = Φ(d_g=12, d_0=7)

If any of these descent actions ≈ 2π, that's structural support
for d_0=7 as confinement layer at "one cascade structural unit
below M_Z" (where 2π = N(0)·Γ(1/2)² is the cascade structural unit).

Also test: cascade SU(3) running from d=12 to d=7 with cascade
β_0 and α_s(M_Z) as starting point. Does α_s reach a "confinement
value" (e.g., α_s = 1) at d_0=7?

Honest expectation: the cascade descent action between layers is
specific cascade-derived value. Whether it lands at 2π or some
other structurally-identifiable value will determine if the
"d_0=7 = confinement layer" conjecture has cascade-internal support.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, THIS_DIR)

from cascade_gram_bott_tower import Phi_cascade, alpha_cascade  # noqa: E402

# Cascade primitives
PI = math.pi
TWO_PI = 2 * PI

# Cascade-derived values
ALPHA_S_MZ = 0.117917
M_Z_GEV = 91.1876
N_C = 3
N_0 = 2
ALPHA_GUT_INV = 25.02
ALPHA_GUT = 1.0 / ALPHA_GUT_INV

# Distinguished cascade layers
D_OBS = 4         # Observer
D_V = 5           # Volume max
D_0 = 7           # Area max / G_2/SU(3) algebra source
D_GW = 14         # Gauge window (U(1) layer, upper boundary)
D_SU3_GW = 12     # SU(3) layer in gauge window
D_1 = 19          # Phase transition
D_DIRAC_FERMION = [5, 13, 21]  # Active particle-host segment

# Cascade β_0 with n_f flavors
def beta_0(n_f: int) -> float:
    return (N_C**2 + N_C - 1) - N_0 * n_f / N_C


def cascade_descent(d_high: int, d_low: int) -> float:
    """Cascade descent action from d_high down to d_low.

    Using the convention Phi_cascade(d) = sum p(k) for k in [5, d].
    Descent from d_high to d_low: Phi(d_high) - Phi(d_low).
    """
    if d_low < 5 or d_high < 5:
        # Adjust: Phi_cascade default starts at d_min=5
        # For d < 5, use direct sum or define differently
        # Just use Phi_cascade(d, d_min) form
        return Phi_cascade(d_high, d_low + 1) if d_high >= d_low + 1 else 0
    return Phi_cascade(d_high) - Phi_cascade(d_low)


def main() -> None:
    print("=" * 96)
    print("TEST: IS d_0=7 THE CASCADE QCD CONFINEMENT LAYER?")
    print("=" * 96)
    print()
    print(f"Cascade primitives: 2π = N(0)·Γ(1/2)² = {TWO_PI:.5f}")
    print(f"                    π = {PI:.5f}")
    print(f"                    α_s(M_Z) = {ALPHA_S_MZ}")
    print(f"                    α_GUT^(-1) = {ALPHA_GUT_INV} → α_GUT = {ALPHA_GUT:.5f}")
    print()

    # Compute cascade descent actions between key layers
    print("Cascade descent actions Φ(d_high → d_low):")
    print()

    pairs = [
        (D_SU3_GW, D_OBS, "gauge-window SU(3) → observer"),
        (D_0, D_OBS, "d_0=7 (algebra source) → observer"),
        (D_SU3_GW, D_0, "gauge-window → d_0 (between SU(3) layers)"),
        (D_GW, D_0, "U(1) layer → d_0"),
        (D_1, D_0, "phase transition → d_0"),
        (D_GW, D_OBS, "U(1) layer → observer"),
        (D_1, D_OBS, "phase transition → observer"),
    ]

    print(f"{'pair':>40}  {'Φ value':>10}  {'2π/Φ':>8}  notes")
    print("-" * 96)
    for d_h, d_l, label in pairs:
        phi = cascade_descent(d_h, d_l)
        ratio_2pi = TWO_PI / phi if phi != 0 else float('inf')
        notes = ""
        if 0.95 < phi/TWO_PI < 1.05:
            notes = "<<< CLOSE TO 2π"
        elif 0.90 < phi/PI < 1.10:
            notes = "<<< close to π"
        print(f"{label:>40}  {phi:>10.5f}  {ratio_2pi:>8.3f}  {notes}")
    print()

    # Specific test: does Φ(d=12 → d_0=7) ≈ 2π?
    phi_gw_to_d0 = cascade_descent(D_SU3_GW, D_0)
    print(f"KEY: Φ(d_gw_SU3=12 → d_0=7) = {phi_gw_to_d0:.5f}")
    print(f"     2π = {TWO_PI:.5f}")
    print(f"     ratio Φ/2π = {phi_gw_to_d0/TWO_PI:.4f}")
    print()

    # Also: cascade running from d=12 to d_0=7
    print("=" * 96)
    print("Cascade α_s running from d=12 to d_0=7:")
    print("=" * 96)
    print()
    # If cascade α_s(M_Z) = α(12)·exp(L) with L=Φ(12→4)+α(14)/χ ≈ 1.080
    # at d_0=7, the "running" would use Phi(7→4) instead
    # α_s_at_d0 ~ α(12)·exp(Phi(12→7)) for cascade SU(3) descent
    # But α(12) is the d=12 coupling, α(7) at d_0=7
    print(f"  α(12) = {alpha_cascade(D_SU3_GW):.5f}, 1/α(12) = {1/alpha_cascade(D_SU3_GW):.3f}")
    print(f"  α(7)  = {alpha_cascade(D_0):.5f}, 1/α(7)  = {1/alpha_cascade(D_0):.3f}")
    print()
    # Cascade running between SU(3) layers
    print("If cascade SU(3) is 'free' at d=12 (gauge-window) and 'closed' at d_0=7,")
    print("the cascade descent factor exp(-Φ(12→7)) measures the 'running between")
    print("the two SU(3) layers':")
    factor = math.exp(-phi_gw_to_d0)
    print(f"  exp(-Φ(12→7)) = exp(-{phi_gw_to_d0:.4f}) = {factor:.5f}")
    print()
    # Compare to standard 1-loop running with cascade β_0
    # If the descent from d=12 to d=7 corresponds to physical scale change
    # M_high → M_low, with M_low/M_high = exp(-Φ(12→7)), then:
    # 1/α_s(M_low) = 1/α(12) - β_0/(2π) · ln(M_high/M_low)·(-1) (standard)
    # i.e., 1/α_s(M_low) = 1/α(12) + β_0/(2π) · Φ(12→7)
    inv_alpha_s_d0 = 1/alpha_cascade(D_SU3_GW) + beta_0(6)/(2*PI) * phi_gw_to_d0
    alpha_s_d0_running = 1.0 / inv_alpha_s_d0 if inv_alpha_s_d0 > 0 else float('inf')
    print(f"  Standard 1-loop running: 1/α_s at d_0=7 = 1/α(12) + β_0/(2π)·Φ(12→7)")
    print(f"  = {1/alpha_cascade(D_SU3_GW):.3f} + {beta_0(6):.3f}/(2π)·{phi_gw_to_d0:.3f}")
    print(f"  = {1/alpha_cascade(D_SU3_GW):.3f} + {beta_0(6)*phi_gw_to_d0/(2*PI):.3f}")
    print(f"  = {inv_alpha_s_d0:.4f}")
    print(f"  Implied α_s at scale of d_0=7: {alpha_s_d0_running:.5f}")
    print()
    # Actually for asymptotic freedom, going DOWN in scale (d=12 → d=7 is going up
    # in d, which is opposite direction in cascade — hmm this is sign-dependent)
    # Let me redo. Going DOWN in physical scale (toward Λ_QCD) means going DOWN in d.
    # d=4 (observer) is the lowest, so we go from d=12 DOWN to d=4 with the cascade descent.
    # d=7 is between d=4 and d=12. So d=7 is at HIGHER physical scale than d=4 but LOWER
    # than d=12.

    # If the cascade physical scale at d corresponds to some μ(d) with μ(12)=M_GUT,
    # μ(4)=M_obs ≈ M_Z, then μ(7) is between M_Z and M_GUT. NOT confinement scale.

    # This contradicts the "d_0=7 = confinement layer" conjecture.

    print("=" * 96)
    print("RECONSIDERATION: d_0=7 BETWEEN OBSERVER AND GAUGE WINDOW")
    print("=" * 96)
    print()
    print("If physical scale increases with d (d=4 = observer = M_Z scale,")
    print("d=12 = M_GUT scale), then d_0=7 is BETWEEN M_Z and M_GUT, not")
    print("BELOW M_Z. d_0=7 cannot be Λ_QCD ≈ 170 MeV.")
    print()
    print("So the 'd_0=7 = confinement layer' conjecture as direct scale")
    print("identification FAILS.")
    print()
    print("Alternative reading: d_0=7 is the cascade STRUCTURAL layer where")
    print("SU(3) ALGEBRA closes (G_2/SU(3) homogeneous space), NOT a")
    print("specific physical-scale identification. The confinement scale")
    print("Λ_QCD ≈ 170 MeV is a DIFFERENT cascade quantity, possibly emerging")
    print("from cascade descent BELOW the observer (which the cascade has")
    print("but isn't fully developed in the existing series).")
    print()

    # Examine cascade descent action below the observer
    print("Cascade descent BELOW observer (d=4):")
    # Use Phi_cascade(4, d_min) for d_min < 4
    # Actually Phi_cascade default has d_min=5, so values for d<5 not directly available
    # Need to extend
    # Cascade has structure d=0, 1, 2, 3 — the observer is at d=4
    # p(d) for d=0,1,2,3:
    # digamma(1/2) ≈ -1.964, p(0) ≈ 0.5·(-1.964) - 0.572 = -0.982 - 0.572 = -1.554
    # digamma(1) ≈ -0.577, p(1) ≈ -0.289 - 0.572 = -0.861
    # digamma(3/2) ≈ 0.036, p(2) ≈ 0.018 - 0.572 = -0.554
    # digamma(2) ≈ 0.423, p(3) ≈ 0.211 - 0.572 = -0.361
    # p(4) ≈ -0.221 (computed)
    # Sum p(0) + p(1) + p(2) + p(3) + p(4) = -1.554 + (-0.861) + (-0.554) + (-0.361) + (-0.221) = -3.551

    # Approximate values for descent below d=4
    approx_p_low_d = {0: -1.554, 1: -0.861, 2: -0.554, 3: -0.361, 4: -0.221}
    # Cumulative descent from d=4 to d=0
    print(f"{'d':>3}  {'p(d)':>10}  {'sum p(d) from d to 4':>22}")
    print("-" * 96)
    cum = 0.0
    for d in range(4, -1, -1):
        cum += approx_p_low_d[d]
        print(f"{d:>3}  {approx_p_low_d[d]:>10.4f}  {cum:>22.4f}")
    print()
    print("Cumulative descent from d=4 (observer) to d=0 (cascade origin):")
    print(f"  Sum p(d) for d=0..4 ≈ -3.551")
    print()
    print("If observer is at d=4 and cascade origin is at d=0, descent from")
    print("M_Z (d=4) to lower scales would go BELOW d=4. But cascade physics")
    print("at d<4 is cascade-internal (pre-observer).")
    print()
    print("Scale at d=0 with cascade-internal exponential descent:")
    print(f"  scale(d=0) ~ M_Z · exp(-3.551) = {M_Z_GEV * math.exp(-3.551)*1000:.2f} MeV")
    print(f"  vs PDG Λ_QCD = 210 MeV: ratio {M_Z_GEV * math.exp(-3.551)*1000 / 210:.3f}")
    print()
    print(f"  Hmm, M_Z · exp(-3.551) ≈ {M_Z_GEV * math.exp(-3.551)*1000:.1f} MeV")
    print(f"  That's around 2.6 GeV, not 170 MeV. Doesn't match Λ_QCD candidate.")
    print()

    print("=" * 96)
    print("STRUCTURAL VERDICT")
    print("=" * 96)
    print()
    print("Direct cascade-descent identification of d_0=7 with Λ_QCD ≈ 170 MeV")
    print("FAILS: d_0=7 is BETWEEN observer and gauge-window in cascade scale,")
    print("not BELOW observer where Λ_QCD lives.")
    print()
    print("ALTERNATIVE STRUCTURAL READING (more nuanced):")
    print()
    print("d_0=7 is the cascade SU(3) ALGEBRA SOURCE (G_2/SU(3) on S^6), not")
    print("a direct physical scale. Its role in cascade confinement is")
    print("STRUCTURAL: cascade SU(3) algebra is closed/non-perturbative at d_0=7")
    print("because S^6 = G_2/SU(3) makes SU(3) the stabilizer of a global G_2")
    print("symmetry — not a freely-acting Lie algebra.")
    print()
    print("Confinement reading: cascade SU(3) at d_0=7 is 'algebra-locked' —")
    print("the SU(3) gauge symmetry is preserved as the stabilizer subgroup of")
    print("G_2, but free SU(3) quanta (gluons) cannot exist as global degrees")
    print("of freedom because the G_2/SU(3) coset structure forces all SU(3)")
    print("excitations to be in the homogeneous space, not in the stabilizer.")
    print()
    print("Color-singlet projection: physical states are G_2-singlets that")
    print("project to SU(3)-singlets via the G_2/SU(3) coset. Quarks (SU(3)")
    print("fundamentals) cannot be G_2-singlets unless paired into SU(3)-singlets")
    print("(mesons, baryons).")
    print()
    print("This is a CASCADE-STRUCTURAL reading of confinement that doesn't")
    print("require d_0=7 to be a specific physical scale. The confinement")
    print("scale Λ_QCD is a DERIVED quantity from cascade descent + cascade β_0,")
    print("while d_0=7 is the STRUCTURAL cause of confinement (algebra-locking).")
    print()
    print("OPEN STRUCTURAL DERIVATION:")
    print()
    print(" (i) Formal derivation that G_2/SU(3) coset structure forces")
    print("     color-singlet projection on physical states.")
    print()
    print(" (ii) Cascade-internal connection between d_0=7's algebra-locking")
    print("      and the dynamical confinement scale Λ_QCD ≈ 170 MeV.")
    print()
    print(" (iii) Whether the cascade SU(3) at d_0=7 'freezes' running of α_s")
    print("       at one cascade structural unit (2π) below M_Z, giving")
    print("       Λ_QCD = M_Z·exp(-2π) ≈ 170 MeV cascade-natively.")
    print()
    print("The cascade has ingredients for confinement (G_2/SU(3) algebra-")
    print("locking at d_0=7, cascade Λ_QCD ≈ 170 MeV, cascade β_0 = 7) but the")
    print("structural derivation tying them into a confinement THEOREM cascade-")
    print("natively is the open piece. This is parallel to how the cascade has")
    print("ingredients for QED dynamics (Tier 1 unitary evolution + spinor rep")
    print("+ chirality structure) and required this session's substantial work")
    print("to assemble them into a Dirac-equation theorem.")


if __name__ == "__main__":
    main()
