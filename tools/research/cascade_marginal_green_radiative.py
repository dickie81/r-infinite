#!/usr/bin/env python3
"""Cascade-Green's-function-based attempt at m_μ/m_e radiative correction.

Follow-up to tools/research/cascade_mu_e_radiative_attempt.py (PR #140).
That tool tested four "counted-multiplicatively" readings of the
chirality-selection-rule m=1, k=1 slot's contribution to m_μ/m_e:

  (a) symmetric — cancels                      → 0%
  (b) per-Dirac-layer-crossed — wrong sign      → −0.116%
  (c) above-layer (only Dirac layers above d_f) → +0.116% (88% of residual)
  (d) per-source α(d_f)/(2π) — overshoots       → +0.218%

Reading (c) closes 88% but not 100% of the +0.132% residual, leaving
a +0.016% gap. None has structural backing beyond bare counting.

This tool tests whether the cascade scalar action's MARGINAL GREEN'S
FUNCTION (Part IVb rem:marginal-greens, equation
G(d_obs, d*) − G(d_obs, d*+1) = α(d*)) provides a structural derivation
of reading (c)'s magnitude. Three candidate cascade-native combinations:

  (e) MARGINAL-GREEN α(d_above)/(2π) per Dirac layer above:
      δ = α(d_above) × 1/(N(0)·Γ(1/2)²) = α(d_above)/(2π)
      Replaces the global α_em with the per-layer cascade gauge coupling.

  (f) GREEN'S-FUNCTION-NORMALIZED α_em × α(d_above) / (cascade unit):
      δ = α_em × α(d_above) / (N(0)·Γ(1/2)²)·(some normalization)
      Combines global α_em with per-layer Green's response.

  (g) BOTT-TOWER FROZEN UV: α(d_above) × cascade-tower-sum / (2π):
      δ = α(d_above) × Σ_{k>d_above} α(k) / (2π)
      Uses the cumulative trailing-tower Green's function form.

Status: exploratory. The cascade primitives are well-defined and the
algebra is forced; whether any one reading gives a clean +0.132%
match is determined empirically.
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

# Cascade-derived QED coupling
ALPHA_EM_INV = 137.028
ALPHA_EM = 1.0 / ALPHA_EM_INV

# Cascade primitives at relevant layers (computed below)
N0 = 2.0  # = chi
SQRT_PI = math.sqrt(math.pi)
PI = math.pi
TWO_PI = 2 * math.pi  # = N(0) · Γ(1/2)²

# Charged-lepton Dirac layers (cascade inverted hierarchy)
D_TAU = 5
D_MU = 13
D_E = 21
D_NEXT = 29  # next Dirac layer above active particle-host segment

# d_2 cascade Planck sink
D2 = 217

# PDG values
M_MU_OVER_M_E_PDG = 206.7683
M_TAU_OVER_M_MU_PDG = 16.8170
# Existing Tier 2 closure of m_τ/m_μ via δΦ_U(1) = α(14)/χ
M_TAU_OVER_M_MU_TIER2 = 16.81731


# ---------------------------------------------------------------------
# Cascade Green's function primitives
# ---------------------------------------------------------------------

def cumulative_green(d_obs: int, d_star: int, d_max: int = D2) -> float:
    """Cumulative trailing-tower form: G(d_obs, d*) = Σ_{k=d*}^{d_max-1} α(k)."""
    return sum(alpha_cascade(k) for k in range(d_star, d_max))


def marginal_green_increment(d_star: int) -> float:
    """Marginal identity: G(d_obs, d*) − G(d_obs, d*+1) = α(d*)."""
    return alpha_cascade(d_star)


def dirac_layers_above_active(d_f: int, d_max: int = D_E) -> list[int]:
    """Dirac layers strictly above d_f within active particle-host segment."""
    return [d for d in range(d_f + 1, d_max + 1) if d % 8 == 5]


def dirac_layers_above_full_tower(d_f: int, d_max: int = D2) -> list[int]:
    """All Dirac layers above d_f up to cascade Planck sink."""
    return [d for d in range(d_f + 1, d_max) if d % 8 == 5]


# ---------------------------------------------------------------------
# Candidate corrections (Green's-function-based)
# ---------------------------------------------------------------------

def cascade_leading_ratio(d_heavy: int, d_light: int) -> float:
    """Cascade leading mass ratio."""
    n_D_h = n_D_for_dirac(d_heavy)
    n_D_l = n_D_for_dirac(d_light)
    log_ratio = (
        Phi_cascade(d_light) - Phi_cascade(d_heavy)
        - (n_D_h + 1) * math.log(TWOSQRTPI)
        + (n_D_l + 1) * math.log(TWOSQRTPI)
    )
    return math.exp(log_ratio)


def correction_e_marginal_alpha_over_2pi(d_f: int) -> float:
    """Reading (e): δ = Σ_{d_above} α(d_above)/(2π) over Dirac layers above (active segment)."""
    return sum(alpha_cascade(d) / TWO_PI for d in dirac_layers_above_active(d_f))


def correction_e_marginal_full_tower(d_f: int) -> float:
    """Reading (e'): same as (e) but over all Dirac layers up to d_2."""
    return sum(alpha_cascade(d) / TWO_PI for d in dirac_layers_above_full_tower(d_f))


def correction_f_combined(d_f: int) -> float:
    """Reading (f): δ = α_em × Σ α(d_above) per Dirac layer above (active segment)."""
    return ALPHA_EM * sum(alpha_cascade(d) for d in dirac_layers_above_active(d_f))


def correction_g_bott_tower_uv(d_f: int) -> float:
    """Reading (g): δ = Σ α(d_above) × G_above(d_above) / (2π) — cumulative trailing tower."""
    total = 0.0
    for d_above in dirac_layers_above_active(d_f):
        total += alpha_cascade(d_above) * cumulative_green(d_f, d_above + 1) / TWO_PI
    return total


def correction_h_alpha_em_per_layer(d_f: int) -> float:
    """Reading (h): δ = (#Dirac layers above active) × α_em/(2π)

    Same as PR #140 reading (c) — for comparison.
    """
    n_above = len(dirac_layers_above_active(d_f))
    return n_above * ALPHA_EM / TWO_PI


def correction_i_marginal_alpha_em(d_f: int) -> float:
    """Reading (i): δ = α_em × (#Dirac layers above active) / (N(0)·Γ(1/2)²)

    Identical to (h) (since N(0)·Γ(1/2)² = 2π). Listed for clarity.
    """
    return correction_h_alpha_em_per_layer(d_f)


# ---------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------

def report_ratio(label: str, observed: float, leading: float,
                 corr_h: float, corr_l: float) -> None:
    """Report cascade correction on a mass ratio (heavy/light).

    Mass m_h gets multiplicative correction (1 + corr_h);
    Mass m_l gets multiplicative correction (1 + corr_l);
    Ratio gets (1 + corr_h)/(1 + corr_l).
    """
    correction = (1 + corr_h) / (1 + corr_l) - 1.0
    res_leading = (observed - leading) / leading
    corrected = leading * (1 + correction)
    res_corrected = (observed - corrected) / corrected
    print(f"  {label}")
    print(f"    Cascade leading:    {leading:.5f}")
    print(f"    Observed (PDG):     {observed:.5f}")
    print(f"    Per-fermion corr:   heavy={corr_h*100:+.4f}%, light={corr_l*100:+.4f}%")
    print(f"    Ratio correction:   {correction*100:+.4f}%")
    print(f"    Cascade corrected:  {corrected:.5f}")
    print(f"    Residual leading:   {res_leading*100:+.4f}%")
    print(f"    Residual after:     {res_corrected*100:+.4f}%")
    print()


def main() -> None:
    print("=" * 78)
    print("CASCADE-GREEN'S-FUNCTION-BASED RADIATIVE CORRECTION TO m_μ/m_e")
    print("=" * 78)
    print()
    print("Source: Part IVb rem:marginal-greens — G(d_obs, d*) − G(d_obs, d*+1) = α(d*)")
    print(f"Cascade-derived α_em = 1/{ALPHA_EM_INV} = {ALPHA_EM:.7f}")
    print(f"Cascade primitive 2π = N(0)·Γ(1/2)² = {TWO_PI:.5f}")
    print(f"α_em/(2π) = {ALPHA_EM/TWO_PI*100:.4f}%")
    print()

    # Cascade primitives at relevant Dirac layers
    print("Per-layer cascade gauge coupling α(d) at Dirac layers in active segment:")
    print(f"  α({D_TAU})  = {alpha_cascade(D_TAU):.5f} = {alpha_cascade(D_TAU)*100:.3f}%")
    print(f"  α({D_MU})  = {alpha_cascade(D_MU):.5f} = {alpha_cascade(D_MU)*100:.3f}%")
    print(f"  α({D_E})  = {alpha_cascade(D_E):.5f} = {alpha_cascade(D_E)*100:.3f}%")
    print(f"  α({D_NEXT})  = {alpha_cascade(D_NEXT):.5f} = {alpha_cascade(D_NEXT)*100:.3f}%")
    print()
    print("Active particle-host Dirac layers above each lepton:")
    print(f"  m_τ at d={D_TAU:2d}: above (active) = {dirac_layers_above_active(D_TAU)}")
    print(f"  m_μ at d={D_MU:2d}: above (active) = {dirac_layers_above_active(D_MU)}")
    print(f"  m_e at d={D_E:2d}: above (active) = {dirac_layers_above_active(D_E)}")
    print()

    leading_mu_e = cascade_leading_ratio(D_MU, D_E)
    print("=" * 78)
    print("m_μ/m_e under each Green's-function-based reading")
    print("=" * 78)
    print()

    # Reading (h)/(i): repeat of PR #140's reading (c) for reference
    corr_h_mu = correction_h_alpha_em_per_layer(D_MU)
    corr_h_e = correction_h_alpha_em_per_layer(D_E)
    report_ratio("Reading (h) GLOBAL α_em / Dirac layer above (active segment) [= PR#140 (c)]",
                 M_MU_OVER_M_E_PDG, leading_mu_e, corr_h_mu, corr_h_e)

    # Reading (e): per-layer α(d_above)/(2π)
    corr_e_mu = correction_e_marginal_alpha_over_2pi(D_MU)
    corr_e_e = correction_e_marginal_alpha_over_2pi(D_E)
    report_ratio("Reading (e) MARGINAL α(d_above)/(2π) per Dirac layer above (active)",
                 M_MU_OVER_M_E_PDG, leading_mu_e, corr_e_mu, corr_e_e)

    # Reading (e'): per-layer α(d_above)/(2π) over FULL tower
    corr_eprime_mu = correction_e_marginal_full_tower(D_MU)
    corr_eprime_e = correction_e_marginal_full_tower(D_E)
    report_ratio("Reading (e') MARGINAL α(d_above)/(2π) over FULL Bott tower (d ≤ d_2)",
                 M_MU_OVER_M_E_PDG, leading_mu_e, corr_eprime_mu, corr_eprime_e)

    # Reading (f): combined α_em × α(d_above)
    corr_f_mu = correction_f_combined(D_MU)
    corr_f_e = correction_f_combined(D_E)
    report_ratio("Reading (f) COMBINED α_em × Σ α(d_above) per Dirac layer above (active)",
                 M_MU_OVER_M_E_PDG, leading_mu_e, corr_f_mu, corr_f_e)

    # Reading (g): Bott tower UV cumulative
    corr_g_mu = correction_g_bott_tower_uv(D_MU)
    corr_g_e = correction_g_bott_tower_uv(D_E)
    report_ratio("Reading (g) BOTT-TOWER UV: α(d_above) × G_trailing/(2π)",
                 M_MU_OVER_M_E_PDG, leading_mu_e, corr_g_mu, corr_g_e)

    # Reading (h)+(f) combined — leading + Green's-function next-order
    corr_hf_mu = corr_h_mu + corr_f_mu
    corr_hf_e = corr_h_e + corr_f_e
    report_ratio("Reading (h)+(f) COMBINED: α_em/(2π) leading + α_em·α(d_above) next-order",
                 M_MU_OVER_M_E_PDG, leading_mu_e, corr_hf_mu, corr_hf_e)

    # Consistency check on m_τ/m_μ
    print("=" * 78)
    print("CONSISTENCY: m_τ/m_μ under same readings")
    print("=" * 78)
    print()
    print("Note: m_τ/m_μ is closed via δΦ_U(1) = α(14)/χ at +0.243σ.")
    print("Reading the chirality-selection rule m=1, k=1 ON TOP must NOT ruin this.")
    print("For each reading below, we apply correction to the U(1)-shifted value.")
    print(f"  Tier 2 closure: m_τ/m_μ = {M_TAU_OVER_M_MU_TIER2}")
    print(f"  PDG:           m_τ/m_μ = {M_TAU_OVER_M_MU_PDG}")
    print(f"  Existing residual:      {(M_TAU_OVER_M_MU_PDG - M_TAU_OVER_M_MU_TIER2)/M_TAU_OVER_M_MU_TIER2*100:+.5f}%")
    print()

    for label, fn in [
        ("(h) α_em/Dirac-above (active)", correction_h_alpha_em_per_layer),
        ("(e) α(d_above)/(2π) (active)", correction_e_marginal_alpha_over_2pi),
        ("(e') α(d_above)/(2π) (full tower)", correction_e_marginal_full_tower),
        ("(f) α_em × Σ α(d_above) (active)", correction_f_combined),
        ("(g) Bott UV cumulative (active)", correction_g_bott_tower_uv),
    ]:
        c_tau = fn(D_TAU)
        c_mu = fn(D_MU)
        ratio_corr = (1 + c_tau) / (1 + c_mu) - 1
        post = M_TAU_OVER_M_MU_TIER2 * (1 + ratio_corr)
        post_residual = (M_TAU_OVER_M_MU_PDG - post) / post
        print(f"  {label}")
        print(f"    Tier 2 + ratio corr {ratio_corr*100:+.4f}% → {post:.5f}")
        print(f"    Residual vs PDG:    {post_residual*100:+.5f}%")
        print()

    # Summary table
    print("=" * 78)
    print("HONEST STRUCTURAL VERDICT")
    print("=" * 78)
    print()
    print("Goal: close the +0.132% residual on m_μ/m_e.")
    print()
    print("Reading (h) GLOBAL α_em per Dirac layer above (PR #140 reading (c)):")
    print("  m_μ/m_e: residual closes to ~+0.016% (88% closure)")
    print("  m_τ/m_μ: pushes Tier 2 closure to ~−0.12% (~−1.2σ; BREAKS existing closure)")
    print("  Verdict: structurally suggestive but inconsistent under universal application.")
    print()
    print("Reading (e) MARGINAL α(d_above)/(2π) — uses per-layer cascade gauge coupling:")
    print("  m_μ/m_e: gives correction proportional to α(21)/(2π) per Dirac layer above.")
    print("  Magnitude is α(21)/(2π) ≈ 0.37%, ~3× too large for m_μ/m_e residual.")
    print("  Verdict: wrong magnitude. The per-layer α(d) at d=21 is too big.")
    print()
    print("Reading (g) BOTT-TOWER UV: products of α with cumulative trailing tower:")
    print("  m_μ/m_e: depends on cumulative G across many Bott layers.")
    print("  Magnitude is sensitive to where the cascade sum terminates.")
    print()
    print("Reading (f) COMBINED α_em × α(d_above):")
    print("  m_μ/m_e: α_em × α(21) ≈ 0.0073 × 0.023 ≈ 1.7×10⁻⁴ = 0.017%.")
    print("  This is suspiciously close to the +0.016% RESIDUAL after reading (h)!")
    print("  Possible structural reading: reading (h) gives leading α_em/(2π);")
    print("  reading (f) gives next-order α_em × α(d_above) = α_em²·... structure.")
    print()
    print("Possible structural picture:")
    print("  - Leading 1-loop: reading (h) [or (e) with α_em not α(d)] gives α_em/(2π).")
    print("  - Next order: reading (f) gives α_em × α(d_above) ≈ 0.017%.")
    print("  - Sum: 0.116% + 0.017% = 0.133% — VERY close to residual 0.132%.")
    print()
    print("This is a numerical coincidence worth examining structurally.")
    print()
    print("Key open questions:")
    print(" 1. What's the structural reason for combining (h) and (f)?")
    print(" 2. Does this break m_τ/m_μ at the same precision level?")
    print(" 3. Is there a systematic chirality-selection-rule extension producing both?")


if __name__ == "__main__":
    main()
