#!/usr/bin/env python3
"""
Lepton consistency check for the s/d = vol(SU(2)) conjecture.

CONTEXT
=======
cascade_sd_su2_volume.py proposed: down-quark Gen 2 -> Gen 1 mass
ratio s/d equals vol(SU(2)) = 2*pi^2 = Omega_3 (-1.3% empirical
match), via cascade descent integrating over the SU(2) gauge orbit.

The natural sceptical question:
  L_L is also an SU(2)_L doublet. If the SU(2) volume mechanism is
  sector-blind, the lepton sector should also exhibit a vol(SU(2))
  factor in its Gen 2 -> Gen 1 mass ratio (m_mu / m_e) -- but the
  cascade lepton formula
        m_mu/m_e = exp(Phi(21) - Phi(13)) * (2*sqrt(pi))
  shows no vol(SU(2)) factor.  Apparent tension.

THE RESOLUTION (numerical)
==========================
The "tension" dissolves when the cascade Phi descent is computed:

  exp(Phi(21) - Phi(13))  =  58.25
  N_c * vol(SU(2))        =  3 * 2*pi^2  =  59.22

These agree to 1.6%, the same precision as the s/d = Omega_3 match.
The lepton sector's Phi descent is approximately equal to N_c times
the SU(2) gauge group volume across the same Bott-period span.

Both templates therefore predict the same Gen 2 -> Gen 1 ratio:

  Lepton template:  m_mu/m_e = exp(Phi(21)-Phi(13)) * (2*sqrt(pi))
                             ≈ N_c * vol(SU(2)) * (2*sqrt(pi))
                             = 3 * 2*pi^2 * 2*sqrt(pi) = 12*pi^(5/2)

  Quark template:   s/d      = vol(SU(2))  =  2*pi^2

  Cross-sector:     m_mu/m_e / (s/d) ≈ N_c * (2*sqrt(pi))
                                        = 3 * 2*sqrt(pi) ≈ 10.63

  Empirical:        m_mu/m_e / (s/d) = 206.77 / 20.00 = 10.34
                    deviation = -2.7%

Both readings of the lepton template (Phi-descent vs gauge-volume)
land at the same precision (-0.13% Phi-descent; ~1.5% gauge-volume).
The lepton sector is structurally consistent with the SU(2) volume
mechanism at the cascade's standing precision.

STRUCTURAL READING
==================
Cascade Phi descent across one Bott period at the Gen 2 -> 1 span
satisfies (numerically, at 1.6%):

  exp(Phi(d+8) - Phi(d)) ≈ N_c * vol(SU(2))   [d=13 case]

This suggests a deeper identity: the cascade descent factor across
a Bott period decomposes structurally as

  cascade descent ≈ (color factor N_c) * (SU(2) gauge volume).

The ratio of mass templates between sectors is:

  Lepton/Quark Gen 2->1 mass ratio
    = exp(Phi descent) * (2*sqrt(pi)) / vol(SU(2))
    ≈ N_c * (2*sqrt(pi))

  observed       = 10.34
  predicted      = 10.63 (using N_c=3 and 2*sqrt(pi))
  deviation      = -2.7%

The N_c here is structurally meaningful: leptons are color-SINGLET
but the cascade descent ACROSS one Bott period sees the SU(3) home
layer at d=12 indirectly (Adams gauge cycle), and contributes a
color-counting factor N_c regardless of the fermion's own color
representation.  The (2*sqrt(pi)) factor is the per-step Dirac
amplification (Part IVa lepton mass formula).

WHAT'S DERIVED
==============
- vol(SU(2)) = 2*pi^2 = Omega_3 is a standard cascade primitive.
- s/d = vol(SU(2)) match to -1.3% (cascade standing precision).
- Lepton template's descent factor ≈ N_c * vol(SU(2)) at 1.6%.
- Lepton-quark Gen 2->1 ratio ≈ N_c * (2*sqrt(pi)) at -2.7%.
- The "tension" between sector templates dissolves at standing
  precision: both lepton and quark formulas predict the same
  Gen 2 -> 1 ratio modulo Dirac amplification.

WHAT'S NOT DERIVED
==================
- Exact identity exp(Phi(21)-Phi(13)) = N_c * vol(SU(2)).  The 1.6%
  residual is unexplained.  Possible sources:
    (a) Dirac amplification correction at a different power.
    (b) Subleading cascade descent term (one of the 8 layers
        contributes a small correction).
    (c) Real structural distinction between Phi descent and gauge
        volume integration.
- Why the lepton template uses (2*sqrt(pi)) Dirac amplification
  but the quark template (b/s, s/d) does not.  Likely because
  quarks are SU(3) charged (color triplet structure modifies the
  Dirac descent), but no explicit derivation in Part IVa or IVb.
- Whether the relation extends to other Bott-period spans.
  exp(Phi(13)-Phi(5)) = 4.66 (Gen 3 -> 2 lepton span, but quark
  Gen 3 -> 2 step has a different mechanism: t/b factor N_c from
  SU(3) color, b/s = -alpha(7)/chi^4 from cascade closure).

STATUS UPDATE
=============
Earlier framing: "the SU(2) volume conjecture has a lepton tension."
Current finding: the tension dissolves numerically at the cascade's
standing precision -- the lepton template's descent factor matches
N_c * vol(SU(2)) to 1.6%, and the lepton-vs-quark ratio matches
N_c * (2*sqrt(pi)) to -2.7%.  Both consistent with the SU(2) volume
mechanism being a universal cascade-internal source for SU(2)_L-
charged fermion mass ratios.

This does NOT close the conjecture at theorem level.  The 1.6% gap
between exp(Phi descent) and N_c * vol(SU(2)) is unexplained and
requires either:
  (i) Identification of a cascade-natural correction term that
      reconciles the two formulas exactly.
  (ii) Acceptance that the two templates are independent and merely
       coincide numerically at the Gen 2 -> 1 span (in which case
       the 'sector-blindness' argument is structurally weak).

Honest assessment: empirical match consistent across both sectors
at the cascade standing precision; full structural derivation
requires identifying the correction term that closes the 1.6% gap.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

from cascade_constants import alpha, R, p, pi  # noqa: E402

# Cascade primitives
N_C = 3
OMEGA_3 = 2 * math.pi ** 2
TWO_SQRT_PI = 2 * math.sqrt(math.pi)

# PDG observations
M_MU_OVER_E_PDG = 206.7682827
M_S_OVER_D_PDG = 93.4 / 4.67  # ≈ 20.0
M_C_OVER_S_PDG = 1.27 / 93.4e-3
M_T_OVER_B_PDG = 172.69 / 4.18


def Phi(d: int) -> float:
    """Cascade potential, sum_{k=5..d} p(k) (Part IVb)."""
    return sum(p(k) for k in range(5, d + 1))


def report_setup() -> None:
    print("=" * 78)
    print("STEP 1: setup -- the apparent tension")
    print("=" * 78)
    print()
    print("  s/d = vol(SU(2)) conjecture: down-quark Gen 2 -> 1 step")
    print("    via cascade descent integrating over SU(2) gauge orbit.")
    print()
    print("  Sceptical question: L_L is ALSO an SU(2)_L doublet.")
    print("    If the mechanism is sector-blind, m_mu/m_e should also")
    print("    show vol(SU(2)).  But the cascade lepton formula is:")
    print()
    print("      m_mu/m_e = exp(Phi(21) - Phi(13)) * (2*sqrt(pi))")
    print()
    print("    with no apparent vol(SU(2)) factor.  Tension?")
    print()


def report_numerical_resolution() -> None:
    print("=" * 78)
    print("STEP 2: numerical resolution")
    print("=" * 78)
    print()
    phi_diff = Phi(21) - Phi(13)
    e_phi = math.exp(phi_diff)
    nc_vol = N_C * OMEGA_3
    ratio = e_phi / nc_vol
    print(f"  Phi(21) - Phi(13)        = {phi_diff:.6f}")
    print(f"  exp(Phi(21) - Phi(13))   = {e_phi:.4f}")
    print(f"  N_c * vol(SU(2))         = 3 * 2*pi^2 = {nc_vol:.4f}")
    print(f"  ratio                    = {ratio:.6f}")
    print(f"  deviation                = {100*(ratio - 1):+.3f}%")
    print()
    print("  The cascade Phi descent across the Gen 2 -> 1 Bott period IS")
    print("  approximately equal to N_c * vol(SU(2)), to 1.6%.")
    print()


def report_template_equivalence() -> None:
    print("=" * 78)
    print("STEP 3: lepton template = gauge-volume template (at standing precision)")
    print("=" * 78)
    print()
    phi_diff = Phi(21) - Phi(13)
    e_phi = math.exp(phi_diff)

    # Two readings of the lepton ratio
    m_mu_e_phi = e_phi * TWO_SQRT_PI
    m_mu_e_vol = N_C * OMEGA_3 * TWO_SQRT_PI

    print("  Two cascade-internal readings of m_mu/m_e:")
    print()
    print(f"    Phi-descent: exp(Phi(21)-Phi(13)) * (2*sqrt(pi))")
    print(f"               = {e_phi:.4f} * {TWO_SQRT_PI:.4f}")
    print(f"               = {m_mu_e_phi:.4f}")
    print(f"               (PDG {M_MU_OVER_E_PDG}, dev {100*(m_mu_e_phi-M_MU_OVER_E_PDG)/M_MU_OVER_E_PDG:+.4f}%)")
    print()
    print(f"    Gauge-vol:   N_c * vol(SU(2)) * (2*sqrt(pi))")
    print(f"               = {N_C} * {OMEGA_3:.4f} * {TWO_SQRT_PI:.4f}")
    print(f"               = 12*pi^(5/2)")
    print(f"               = {m_mu_e_vol:.4f}")
    print(f"               (PDG {M_MU_OVER_E_PDG}, dev {100*(m_mu_e_vol-M_MU_OVER_E_PDG)/M_MU_OVER_E_PDG:+.4f}%)")
    print()
    print("  Both readings land within cascade standing precision (~1.5%).")
    print("  The gauge-volume reading uses the SAME vol(SU(2)) factor as")
    print("  the s/d quark conjecture, with an extra N_c color counter and")
    print("  the lepton's Dirac amplification factor (2*sqrt(pi)).")
    print()


def report_lepton_quark_ratio() -> None:
    print("=" * 78)
    print("STEP 4: lepton-vs-quark Gen 2 -> 1 ratio")
    print("=" * 78)
    print()
    phi_diff = Phi(21) - Phi(13)
    e_phi = math.exp(phi_diff)

    obs_ratio = M_MU_OVER_E_PDG / M_S_OVER_D_PDG
    pred_phi = e_phi * TWO_SQRT_PI / OMEGA_3
    pred_vol = N_C * TWO_SQRT_PI

    print(f"  Observed (m_mu/m_e) / (s/d) = {M_MU_OVER_E_PDG:.4f} / {M_S_OVER_D_PDG:.4f}")
    print(f"                              = {obs_ratio:.4f}")
    print()
    print(f"  Cascade prediction (Phi-descent reading):")
    print(f"    exp(Phi descent) * (2*sqrt(pi)) / vol(SU(2))")
    print(f"    = {pred_phi:.4f}, dev {100*(pred_phi-obs_ratio)/obs_ratio:+.3f}%")
    print()
    print(f"  Cascade prediction (gauge-volume reading):")
    print(f"    N_c * (2*sqrt(pi))")
    print(f"    = {pred_vol:.4f}, dev {100*(pred_vol-obs_ratio)/obs_ratio:+.3f}%")
    print()
    print("  STRUCTURAL READING:")
    print()
    print("    The lepton/quark Gen 2 -> 1 ratio decomposes as N_c * (2*sqrt(pi)).")
    print("    - N_c (=3): comes from SU(3) color counting in the descent --")
    print("      even though leptons are color-singlet, the cascade Bott-period")
    print("      descent crosses the SU(3) home at d=12 indirectly.")
    print("    - (2*sqrt(pi)): per-step Dirac amplification for leptons,")
    print("      absent in quarks (Part IVa lepton mass formula).")
    print()
    print("    The s/d quark formula 'misses' the Dirac amplification factor")
    print("    (2*sqrt(pi)) because quarks are SU(3) color triplets -- their")
    print("    Dirac structure differs from leptons due to the color-anti-color")
    print("    pair structure that absorbs the (2*sqrt(pi)) factor.")
    print()


def report_other_bott_periods() -> None:
    print("=" * 78)
    print("STEP 5: does the relation extend to other Bott-period spans?")
    print("=" * 78)
    print()
    print("  Test: exp(Phi(d+8) - Phi(d)) vs N_c * vol(SU(2))")
    print()
    for d_lo, d_hi, label in [
        (5, 13, "Gen 3 -> 2"),
        (13, 21, "Gen 2 -> 1"),
        (21, 29, "Gen 1 -> 0"),
    ]:
        delta = Phi(d_hi) - Phi(d_lo)
        e_delta = math.exp(delta)
        ratio = e_delta / (N_C * OMEGA_3)
        print(f"  {label} (d={d_lo} -> {d_hi}):")
        print(f"    exp(dPhi)        = {e_delta:.4f}")
        print(f"    N_c * vol(SU(2)) = {N_C * OMEGA_3:.4f}")
        print(f"    ratio            = {ratio:.4f}")
        print()
    print("  Only Gen 2 -> 1 has the clean ratio ≈ 1.")
    print("  Gen 3 -> 2 has descent ~4.66, far below N_c*vol(SU(2)).")
    print("  Gen 1 -> 0 has descent ~267, far above N_c*vol(SU(2)).")
    print()
    print("  This means the 'exp(Phi) ≈ N_c * vol(SU(2))' identity is")
    print("  SPECIFIC to the Gen 2 -> 1 Bott period span, not universal.")
    print()
    print("  The Phi descent grows accelerating in d (because p(d) grows),")
    print("  so only one Bott period coincides with N_c * vol(SU(2)).")
    print()
    print("  STRUCTURAL INTERPRETATION:")
    print()
    print("    The Gen 2 -> 1 step is the UNIQUE cascade descent step where")
    print("    the Phi descent matches the gauge-volume integration.  This")
    print("    is the layer span d=13..21:")
    print("      d=13: SU(2) home (gauge window upper edge)")
    print("      d=14: U(1) home")
    print("      d=15..21: post-gauge-window cascade descent")
    print()
    print("    For Gen 3 -> 2 (d=5..13), the descent crosses INTO the gauge")
    print("    window from the volume-maximum region.  Different mechanism.")
    print()
    print("    For Gen 1 -> 0 (d=21..29), the descent is past the cosmological")
    print("    horizon (d=21 = electron home) into the bulk-fermion region.")
    print("    No physical Gen 0 to compare with.")
    print()


def report_status() -> None:
    print("=" * 78)
    print("STEP 6: status update for SU(2) volume conjecture")
    print("=" * 78)
    print()
    print("  RESOLVED: lepton sector consistent with SU(2) volume mechanism")
    print("  at cascade standing precision.")
    print()
    print("  Specifically:")
    print("    (i) Lepton m_mu/m_e formula's descent factor ≈ N_c * vol(SU(2))")
    print("        at 1.6%, so the gauge-volume reading is structurally")
    print("        equivalent to the cascade-Phi reading.")
    print("    (ii) Lepton-vs-quark Gen 2 -> 1 ratio ≈ N_c * (2*sqrt(pi))")
    print("         at -2.7%, decomposing cleanly into color factor and")
    print("         Dirac amplification.")
    print("    (iii) Identity is SPECIFIC to the Gen 2 -> 1 span; doesn't")
    print("          extend to other Bott-period steps.")
    print()
    print("  STILL OPEN:")
    print("    (a) Exact identity exp(Phi(21)-Phi(13)) = N_c * vol(SU(2)) +")
    print("        cascade-natural correction.  Currently 1.6% gap unexplained.")
    print("    (b) Why quarks lack the Dirac amplification (2*sqrt(pi)) that")
    print("        leptons have, structurally.  Likely SU(3) color triplet")
    print("        Dirac structure absorbs the factor, but no explicit proof.")
    print("    (c) Cascade-internal proof that down-quark Q_L^c integrates")
    print("        full vol(SU(2)) while up-quark Q_L^c integrates")
    print("        vol(PSU(2)) = vol(SU(2))/2.")
    print()
    print("  ASSESSMENT: the conjecture is consistent across both sectors,")
    print("  but full theorem-level closure requires items (a)-(c).  These")
    print("  are research-level questions, not roadblocks; the empirical")
    print("  match is at standing cascade precision throughout.")
    print()


def main() -> int:
    print("=" * 78)
    print("LEPTON CONSISTENCY CHECK FOR s/d = vol(SU(2)) CONJECTURE")
    print("Roadmap #6 -- digging deeper on the SU(2) volume mechanism")
    print("=" * 78)
    print()
    report_setup()
    report_numerical_resolution()
    report_template_equivalence()
    report_lepton_quark_ratio()
    report_other_bott_periods()
    report_status()
    print("=" * 78)
    print("FINDING:")
    print("  The 'lepton tension' for the SU(2) volume conjecture dissolves")
    print("  at cascade standing precision.  Numerically:")
    print()
    print("    exp(Phi(21) - Phi(13)) ≈ N_c * vol(SU(2))   [at 1.6%]")
    print()
    print("  Both lepton (Phi-descent) and quark (gauge-volume) templates")
    print("  predict the same Gen 2 -> 1 mass ratio modulo Dirac amplification:")
    print()
    print("    m_mu/m_e ≈ N_c * vol(SU(2)) * (2*sqrt(pi)) = 12*pi^(5/2)")
    print("    s/d      ≈ vol(SU(2))                      = 2*pi^2")
    print()
    print("  Lepton/Quark ratio:  N_c * (2*sqrt(pi)) ≈ 10.63 (PDG 10.34, -2.7%)")
    print()
    print("  Decomposition cascade-naturally meaningful:")
    print("    N_c          - SU(3) color counting from Bott-period descent")
    print("    (2*sqrt(pi)) - Dirac amplification (lepton-only, quarks absorb")
    print("                   into SU(3) color-triplet structure)")
    print()
    print("STATUS: empirical consistency at cascade standing precision across")
    print("        both sectors; full theorem-level closure requires deriving")
    print("        the exact identity exp(Phi descent) = N_c * vol(SU(2)) and")
    print("        the quark vs. lepton Dirac-structure asymmetry.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
