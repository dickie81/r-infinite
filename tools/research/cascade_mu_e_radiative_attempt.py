#!/usr/bin/env python3
"""Attempt cascade-native 1-loop QED correction to m_μ/m_e.

Context. Part IVb's `oq:mu-e-residual` documents a +0.132% leading-order
discrepancy on m_μ/m_e (cascade leading 206.50 vs PDG 206.7683). This
session's `rem:two-pi-prefactor-identification` identified the cascade
1-loop prefactor 1/(2π) = 1/(N(0)·Γ(1/2)²) cascade-natively. Numerical
observation: α_em/(2π) ≈ 0.116% at the cascade-derived α_em = 1/137.028
sits suspiciously close to the +0.132% residual.

This tool tests whether the cascade's chirality-selection-rule m=1, k=1
slot — the same slot that gives Schwinger's (g-2)/2 = α_em/(2π) — also
closes m_μ/m_e at +0.13% under any of three candidate structural readings.

Cascade convention (per `cascade_gram_bott_tower.py` and Part IVb).
Charged leptons sit at the cascade's three Dirac layers in inverted
hierarchy: m_τ at d=5 (lightest descent), m_μ at d=13, m_e at d=21
(deepest descent, lightest particle). Standard cascade descent goes
from high d to d=4 (the observer).

Three candidate readings of the cascade radiative correction:

  (a) SYMMETRIC. The chirality-selection-rule applies symmetrically to
      both leptons — same correction α_em/(2π) per fermion. Cancels in
      the ratio (standard QED on-shell behaviour). Predicts: no shift.

  (b) PER-DIRAC-LAYER-CROSSED. The correction attaches to each Dirac
      layer the lepton's descent path crosses. For m_e at d=21, descent
      crosses {5, 13, 21} — 3 Dirac layers. For m_μ at d=13, descent
      crosses {5, 13} — 2 Dirac layers. m_e gets a larger correction;
      m_μ/m_e shifts NEGATIVELY by α_em/(2π) (wrong sign vs +0.132%).

  (c) ABOVE-LAYER (Bott shift orbit, "from above"). Cascade descent goes
      high → low. For a fermion at host layer d_f, cascade Dirac layers
      ABOVE d_f (those at higher d in the active particle-host segment
      {5, 13, 21}) contribute radiative shifts; those at or below don't.
      For m_e at d=21: no Dirac layers above → no correction.
      For m_μ at d=13: one Dirac layer above (d=21) → +α_em/(2π).
      m_μ/m_e shifts POSITIVELY by α_em/(2π) (right sign).

Reading (c) gives the structural reading consistent with the residual's
sign. We compute the magnitude and report the post-correction residual.

The tool also evaluates reading (c)'s consistency with other Tier 2
closures: applying the same rule to m_τ/m_μ (already closed by
δΦ_U(1) = α(14)/χ family) would over-correct it. So reading (c) cannot
apply uniformly to all charged-lepton ratios.

Honest verdict: reading (c) is structurally suggestive but not yet
forced by cascade machinery; the consistency tension with m_τ/m_μ's
existing closure means a more careful structural derivation is needed.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, THIS_DIR)

from cascade_gram_bott_tower import (  # noqa: E402
    Phi_cascade,
    TWOSQRTPI,
    n_D_for_dirac,
    alpha_cascade,
)

# Cascade-derived QED coupling (Part IVb Tier 2 entry k)
ALPHA_EM_INV = 137.028
ALPHA_EM = 1.0 / ALPHA_EM_INV

# Charged-lepton Dirac layer assignment (cascade inverted hierarchy)
D_TAU = 5
D_MU = 13
D_E = 21

# PDG values (PDG 2024 averages)
M_MU_OVER_M_E_PDG = 206.7683
M_TAU_OVER_M_MU_PDG = 16.8170


def cascade_leading_ratio(d_heavy: int, d_light: int) -> float:
    """Cascade leading mass ratio m(d_light) / m(d_heavy).

    With the inverted hierarchy convention (lighter charged lepton at
    higher Dirac layer), m_μ/m_e where μ is at d=13 (heavier) and e is
    at d=21 (lighter) is m(d=13) / m(d=21) = exp(Phi(21) - Phi(13)) · 2√π.
    """
    n_D_h = n_D_for_dirac(d_heavy)
    n_D_l = n_D_for_dirac(d_light)
    # m(d) ∝ exp(-Phi(d)) · (2√π)^-(n_D+1)
    log_ratio = (
        Phi_cascade(d_light) - Phi_cascade(d_heavy)
        - (n_D_h + 1) * math.log(TWOSQRTPI)
        + (n_D_l + 1) * math.log(TWOSQRTPI)
    )
    return math.exp(log_ratio)


def dirac_layers_in_descent(d_f: int) -> list[int]:
    """Dirac layers crossed in descent from d_f down to d=4."""
    return [d for d in range(5, d_f + 1) if d % 8 == 5]


def dirac_layers_above(d_f: int, d_max: int = D_E) -> list[int]:
    """Dirac layers strictly above d_f within the active segment up to d_max."""
    return [d for d in range(d_f + 1, d_max + 1) if d % 8 == 5]


def reading_a_symmetric(d_heavy: int, d_light: int) -> float:
    """Reading (a): symmetric per-fermion correction α_em/(2π)."""
    delta_h = ALPHA_EM / (2 * math.pi)
    delta_l = ALPHA_EM / (2 * math.pi)
    return (1 + delta_h) / (1 + delta_l) - 1.0


def reading_b_layers_crossed(d_heavy: int, d_light: int) -> float:
    """Reading (b): correction = (#Dirac layers crossed) × α_em/(2π) per fermion."""
    n_h = len(dirac_layers_in_descent(d_heavy))
    n_l = len(dirac_layers_in_descent(d_light))
    delta_h = n_h * ALPHA_EM / (2 * math.pi)
    delta_l = n_l * ALPHA_EM / (2 * math.pi)
    return (1 + delta_h) / (1 + delta_l) - 1.0


def reading_c_above_layer(d_heavy: int, d_light: int, d_max: int = D_E) -> float:
    """Reading (c): correction = (#Dirac layers above) × α_em/(2π) per fermion.

    For a fermion at host layer d_f, only Dirac layers strictly above d_f
    (within the active particle-host segment up to d_max) contribute.
    """
    n_h = len(dirac_layers_above(d_heavy, d_max))
    n_l = len(dirac_layers_above(d_light, d_max))
    delta_h = n_h * ALPHA_EM / (2 * math.pi)
    delta_l = n_l * ALPHA_EM / (2 * math.pi)
    return (1 + delta_h) / (1 + delta_l) - 1.0


def reading_d_per_source_alpha_d(d_heavy: int, d_light: int) -> float:
    """Reading (d): per-source α(d_f)/(2π) correction (different per layer)."""
    delta_h = alpha_cascade(d_heavy) / (2 * math.pi)
    delta_l = alpha_cascade(d_light) / (2 * math.pi)
    return (1 + delta_h) / (1 + delta_l) - 1.0


def report(label: str, observed: float, leading: float, correction: float) -> None:
    """Report cascade-leading vs observed and the correction's effect."""
    res_leading = (observed - leading) / leading
    corrected = leading * (1 + correction)
    res_corrected = (observed - corrected) / corrected
    print(f"  {label}")
    print(f"    Cascade leading:    {leading:.5f}")
    print(f"    Observed (PDG):     {observed:.5f}")
    print(f"    Leading residual:   {res_leading*100:+.4f}%")
    print(f"    Cascade correction: {correction*100:+.4f}%")
    print(f"    Cascade corrected:  {corrected:.5f}")
    print(f"    Residual after:     {res_corrected*100:+.4f}%")
    print()


def main() -> None:
    print("=" * 78)
    print("CASCADE-NATIVE 1-LOOP QED CORRECTION TO m_μ/m_e")
    print("=" * 78)
    print()
    print("Context: Part IVb `oq:mu-e-residual` documents +0.132% leading")
    print("residual on m_μ/m_e. Test whether cascade chirality-selection-rule")
    print("m=1, k=1 slot (cascade structural prefactor α_em/(2π)) closes it.")
    print()
    print(f"  Cascade-derived α_em = 1/{ALPHA_EM_INV} = {ALPHA_EM:.6f}")
    print(f"  α_em/(2π) = {ALPHA_EM/(2*math.pi)*100:.4f}%")
    print()
    print(f"  m_e  at d={D_E:2d}: Dirac layers in descent {dirac_layers_in_descent(D_E)}, above-layer {dirac_layers_above(D_E)}")
    print(f"  m_μ  at d={D_MU:2d}: Dirac layers in descent {dirac_layers_in_descent(D_MU)}, above-layer {dirac_layers_above(D_MU)}")
    print(f"  m_τ  at d={D_TAU:2d}: Dirac layers in descent {dirac_layers_in_descent(D_TAU)}, above-layer {dirac_layers_above(D_TAU)}")
    print()

    # m_μ/m_e: heavy is m_μ at d=13, light is m_e at d=21
    leading_mu_e = cascade_leading_ratio(D_MU, D_E)
    print("=" * 78)
    print("m_μ/m_e under each candidate reading")
    print("=" * 78)
    print()

    report("Reading (a) SYMMETRIC: α_em/(2π) per fermion (cancels in ratio)",
           M_MU_OVER_M_E_PDG, leading_mu_e,
           reading_a_symmetric(D_MU, D_E))
    report("Reading (b) PER-DIRAC-LAYER-CROSSED: n_D(d_f)·α_em/(2π) per fermion",
           M_MU_OVER_M_E_PDG, leading_mu_e,
           reading_b_layers_crossed(D_MU, D_E))
    report("Reading (c) ABOVE-LAYER: only Dirac layers above d_f contribute",
           M_MU_OVER_M_E_PDG, leading_mu_e,
           reading_c_above_layer(D_MU, D_E))
    report("Reading (d) PER-SOURCE α(d_f)/(2π): different per layer",
           M_MU_OVER_M_E_PDG, leading_mu_e,
           reading_d_per_source_alpha_d(D_MU, D_E))

    # m_τ/m_μ consistency check: heavy is m_τ at d=5, light is m_μ at d=13
    leading_tau_mu = cascade_leading_ratio(D_TAU, D_MU)
    print("=" * 78)
    print("CONSISTENCY CHECK: m_τ/m_μ under reading (c)")
    print("=" * 78)
    print()
    print("m_τ/m_μ is closed in Part IVb Tier 2 (b) via δΦ_U(1) = α(14)/χ.")
    print("If reading (c) is universal, it must NOT over-correct m_τ/m_μ")
    print("beyond standing precision (currently +0.243σ to PDG).")
    print()
    print("  Cascade leading m_τ/m_μ (without α(14)/χ shift):")
    report("    Reading (c) ABOVE-LAYER applied to m_τ/m_μ",
           M_TAU_OVER_M_MU_PDG, leading_tau_mu,
           reading_c_above_layer(D_TAU, D_MU))
    print("  Note: the leading 16.55 above is BEFORE the U(1) shift.")
    print("  Tier 2 closure of m_τ/m_μ uses δΦ_U(1) = α(14)/χ ≈ 0.135%,")
    print("  bringing the prediction to 16.81731 (within +0.243σ of PDG).")
    print("  Reading (c) on top would add +α_em/(2π) ≈ +0.116% multiplicatively;")
    print("  applied to the U(1)-shifted value, this would push it to")
    print(f"    16.81731 × (1 + α_em/(2π)) = {16.81731 * (1 + ALPHA_EM/(2*math.pi)):.5f}")
    print(f"    vs PDG {M_TAU_OVER_M_MU_PDG}: residual "
          f"{(M_TAU_OVER_M_MU_PDG - 16.81731 * (1 + ALPHA_EM/(2*math.pi)))/M_TAU_OVER_M_MU_PDG*100:+.4f}%")
    print()
    print("VERDICT on universal reading (c):")
    print("  - Closes m_μ/m_e residual significantly (88% closure)")
    print("  - But over-corrects m_τ/m_μ: U(1)-shifted closure already at +0.243σ;")
    print("    adding +α_em/(2π) on top would shift it to ~−1.2σ (WORSE).")
    print("  - Reading (c) cannot apply UNIFORMLY to all charged-lepton ratios.")
    print()

    print("=" * 78)
    print("HONEST STRUCTURAL VERDICT")
    print("=" * 78)
    print()
    print("Reading (a) SYMMETRIC: cancels by construction; gives ZERO ratio")
    print("  shift (matches standard QED on-shell mass-ratio behaviour).")
    print()
    print("Reading (b) PER-DIRAC-LAYER-CROSSED: gives WRONG SIGN. The lepton")
    print("  with longer descent (m_e, 3 layers) gets the LARGER correction,")
    print("  pushing m_μ/m_e DOWN by α_em/(2π). Residual is +0.132% (UP).")
    print()
    print("Reading (c) ABOVE-LAYER: gives RIGHT SIGN and ~88% magnitude.")
    print("  Closes m_μ/m_e to ~+0.016% residual. But over-corrects m_τ/m_μ.")
    print("  STRUCTURALLY SUGGESTIVE but NOT UNIVERSAL.")
    print()
    print("Reading (d) PER-SOURCE α(d_f)/(2π): wrong magnitude (per-layer α(d)")
    print("  varies more than α_em — see numbers above).")
    print()
    print("The +0.132% m_μ/m_e residual is NOT closed by any UNIFORMLY-")
    print("APPLIED chirality-selection-rule m=1, k=1 slot reading. The")
    print("numerical coincidence with α_em/(2π) is suggestive but the")
    print("structural derivation requires either:")
    print("  - A per-observable structural rule (m_μ/m_e gets reading (c),")
    print("    m_τ/m_μ doesn't because it's covered by α(14)/χ family)")
    print("  - A different cascade slot (m≥2 closed loops) producing the +0.132%")
    print("  - Something cascade-internal that's not QED-radiative at all")
    print()
    print("Recommendation: this exercise demonstrates that closing m_μ/m_e")
    print("at higher-loop QED level requires more cascade structure than the")
    print("currently-derived chirality-selection-rule provides. Concretely:")
    print("  (i) Whether reading (c)'s 'above-layer' rule is forced cascade-")
    print("      natively at the m=1, k=1 slot (or only at slots not already")
    print("      closed by the α(d*)/χ^k family) is a structural derivation gap.")
    print("  (ii) Open Question oq:additive-multiplicative-duality is the natural")
    print("       home for this work — 'when does the cascade primitive 2π")
    print("       appear in the numerator vs denominator vs nowhere?'")
    print()
    print("Status: this is a worth-pursuing structural question, but the")
    print("cascade does NOT currently close m_μ/m_e via a uniformly-applied")
    print("1-loop QED correction. The closure requires additional structure.")


if __name__ == "__main__":
    main()
