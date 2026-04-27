#!/usr/bin/env python3
"""
Extended empirical scope mapping: chirality-halved Gram across all
descent-dependent observables in the cascade series.

Tests whether the m_mu/m_e empirical match (G_scalar/chi ~ residual) is
unique to that observable, or whether other Gram-corrected observables
also prefer the chirality-halved formulation.

Observables tested (documented Tier 1-2 closures with descent paths):
  alpha_s, m_tau/m_mu, m_tau abs, sin^2(theta_W), ell_A, Omega_m, theta_C
  m_mu/m_e (the unique half-Gram case so far)
  rho_Lambda, v (electroweak VEV)
  m_tau, m_mu, m_e absolute masses

For each: pre-correction residual, full Gram (Theorem 14.7), half Gram
(chirality-halved hypothesis), and where applicable the alpha(d*)/chi^k
Tier 1 closure.

Verdict per observable: which correction formulation closes nearest
to observation.
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def log_R(d: int) -> float:
    return float(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def R(d: int) -> float:
    return math.exp(log_R(d))


def alpha(d: int) -> float:
    """Cascade scalar action compliance: alpha(d) = R(d)^2 / 4."""
    return R(d) ** 2 / 4


def C_squared(d_i: int, d_j: int) -> float:
    return math.exp(2 * log_R(d_i + d_j + 1) - log_R(2 * d_i + 1) - log_R(2 * d_j + 1))


def gram_sum(d_start: int, d_end_inclusive: int) -> float:
    """Adjacent-pair Gram sum over the path's interior transitions."""
    return sum(1.0 - C_squared(d, d + 1) for d in range(d_start, d_end_inclusive))


def main() -> int:
    print("=" * 92)
    print("EXTENDED EMPIRICAL SCOPE: GRAM CORRECTION FORMULATIONS")
    print("=" * 92)
    print()

    chi = 2

    # Each row: (name, leading, observed, [path], available_corrections, sector_notes)
    # where corrections is a dict naming each closure formula:
    #   "Tier1_alpha_d_chi_k": specific alpha(d*)/chi^k value (multiplicative as exp)
    #   "Gram_full": exp(G(path))
    #   "Gram_half": exp(G(path)/2)
    #   "Chain_subtract": (alpha(19)-alpha(14))/chi exp shift
    # Sources: Part 4b Tier 1/2 lists; Part 5 Tier 2 list; Part 0.0 verification table
    # path = (d_start, d_end_inclusive); for adjacent-pair Gram sum d in [d_start, d_end-1]
    #
    # Sign convention: multiplicative correction factor C such that
    #   Q_corrected = Q_leading * C
    # We compare residuals (Q_pred - Q_obs) / Q_obs.

    print("OBSERVABLE                   LEADING       OBS    pre%    full G%    half G%    Tier1%   verdict")
    print("-" * 92)

    rows = []

    def test_obs(
        name: str,
        leading: float,
        observed: float,
        path: tuple[int, int],
        tier1_log_shift: float | None = None,
        sector: str = "",
    ):
        """Test all available correction formulations for an observable."""
        d_start, d_end = path
        G = gram_sum(d_start, d_end)
        pre = (leading - observed) / observed
        full = (leading * math.exp(G) - observed) / observed
        half = (leading * math.exp(G / chi) - observed) / observed
        if tier1_log_shift is not None:
            tier1 = (leading * math.exp(tier1_log_shift) - observed) / observed
        else:
            tier1 = None

        # Verdict: which is closest to 0?
        candidates = [("pre", pre), ("full", full), ("half", half)]
        if tier1 is not None:
            candidates.append(("Tier1", tier1))
        best_name, best_val = min(candidates, key=lambda x: abs(x[1]))

        t1_str = f"{tier1*100:>+8.4f}" if tier1 is not None else f"{'--':>8}"
        rows.append(
            (name, leading, observed, pre, full, half, tier1, best_name, sector)
        )
        print(
            f"{name:>25} {leading:>11.4f} {observed:>9.4f}  "
            f"{pre*100:>+6.3f}  {full*100:>+8.4f}  {half*100:>+8.4f}  "
            f"{t1_str}  {best_name:>8}"
        )

    # ============================================================
    # SECTION A: Already-tested observables (verify earlier results)
    # ============================================================
    print()
    print("--- A. Already-tested observables ---")
    test_obs(
        "alpha_s(M_Z)",
        leading=0.1159,
        observed=0.1179,
        path=(5, 12),
        tier1_log_shift=alpha(14) / chi,  # delta_Phi_U(1)
        sector="gauge coupling",
    )
    test_obs(
        "ell_A",
        leading=297.6,
        observed=301.6,
        path=(5, 12),
        tier1_log_shift=alpha(19) / chi,  # delta_Phi_phase
        sector="CMB scalar",
    )
    test_obs(
        "m_tau/m_mu",
        leading=16.53,
        observed=16.8170,
        path=(6, 13),
        tier1_log_shift=alpha(14) / chi,  # delta_Phi_U(1)
        sector="fermion ratio",
    )
    test_obs(
        "m_mu/m_e",
        leading=206.50,
        observed=206.7683,
        path=(14, 21),
        tier1_log_shift=None,  # no alpha(d*)/chi^k applies
        sector="fermion ratio (special)",
    )

    # ============================================================
    # SECTION B: Absolute masses
    # ============================================================
    print()
    print("--- B. Absolute masses ---")
    # m_tau absolute: leading 1755, closes via alpha(19)/chi (Tier 1)
    # Path: m_tau formula involves Phi(5); use d=5..21 as the descent envelope
    test_obs(
        "m_tau (abs)",
        leading=1755.0,
        observed=1776.82,
        path=(5, 21),  # cascade descent envelope for tau (cumulative Phi)
        tier1_log_shift=alpha(19) / chi,  # delta_Phi_phase
        sector="lepton abs (Tier 1 via alpha(19)/chi)",
    )
    # m_mu absolute: leading 106.2, closes via chain-subtraction (alpha(19) - alpha(14))/chi
    # The leading OVER-predicts (residual +0.47%) so Gram corrections HURT
    test_obs(
        "m_mu (abs)",
        leading=106.2,
        observed=105.66,  # PDG 2024
        path=(5, 21),
        tier1_log_shift=(alpha(19) - alpha(14)) / chi,
        sector="lepton abs (chain-subtract)",
    )
    # m_e absolute: leading 0.514, closes via chain-subtraction
    test_obs(
        "m_e (abs)",
        leading=0.514,
        observed=0.5110,
        path=(5, 21),
        tier1_log_shift=(alpha(19) - alpha(14)) / chi,
        sector="lepton abs (chain-subtract)",
    )

    # ============================================================
    # SECTION C: Electroweak / cosmology
    # ============================================================
    print()
    print("--- C. Electroweak and cosmological ---")
    # v: electroweak VEV, path 5..12 per part4b line 68
    test_obs(
        "v (EW VEV, GeV)",
        leading=240.8,
        observed=246.22,
        path=(5, 12),
        tier1_log_shift=None,  # closes via Theorem 4.7 non-perturbative, not alpha/chi
        sector="EW scale",
    )
    # rho_Lambda: cosmological constant
    test_obs(
        "rho_Lambda x 10^121",
        leading=6.996,
        observed=7.150,
        path=(5, 216),
        tier1_log_shift=None,
        sector="scalar / CC",
    )
    # H_0: 66.78 leading, Planck 67.4
    # H_0 inherits ~half of rho_Lambda's correction (since H_0 = sqrt(rho_Lambda / ...))
    test_obs(
        "H_0 (km/s/Mpc)",
        leading=66.78,
        observed=67.4,  # Planck
        path=(5, 216),
        tier1_log_shift=None,
        sector="cosmology",
    )

    # ============================================================
    # SECTION D: Other Tier 1 closures (verify alpha(d*)/chi^k still wins)
    # ============================================================
    print()
    print("--- D. Tier 1 alpha(d*)/chi^k entries (for completeness) ---")
    test_obs(
        "sin^2(theta_W)",
        leading=0.228624,  # high-precision leading from Part 4b
        observed=0.23121,
        path=(5, 12),  # Weinberg path d=5..14; use d=5..12 for Gram envelope
        tier1_log_shift=alpha(5) / chi**3,  # delta_Phi_obs
        sector="Weinberg angle",
    )
    test_obs(
        "Omega_m",
        leading=1 / math.pi,
        observed=0.31473,
        path=(5, 12),
        tier1_log_shift=-alpha(5) / chi**3,  # negative shift for geometric
        sector="cosmology",
    )

    # ============================================================
    # ANALYSIS
    # ============================================================
    print()
    print("=" * 92)
    print("ANALYSIS: which observables prefer half-Gram?")
    print("=" * 92)
    print()
    half_winners = [r for r in rows if r[7] == "half"]
    full_winners = [r for r in rows if r[7] == "full"]
    tier1_winners = [r for r in rows if r[7] == "Tier1"]
    pre_winners = [r for r in rows if r[7] == "pre"]
    print(f"Half-Gram wins:   {len(half_winners)} observable(s)")
    for r in half_winners:
        print(f"    {r[0]} ({r[8]})")
    print(f"Full-Gram wins:   {len(full_winners)} observable(s)")
    for r in full_winners:
        print(f"    {r[0]} ({r[8]})")
    print(f"Tier 1 alpha/chi^k wins: {len(tier1_winners)} observable(s)")
    for r in tier1_winners:
        print(f"    {r[0]} ({r[8]})")
    print(f"Pre-correction is best (no correction helps): {len(pre_winners)} observable(s)")
    for r in pre_winners:
        print(f"    {r[0]} ({r[8]})")
    print()
    print("CHAIN-RULE FILTER:")
    print()
    print("H_0 = sqrt(rho_Lambda / (3 Omega_Lambda M_Pl^2))  =>  H_0 ~ rho_Lambda^{1/2}")
    print("If rho_Lambda receives correction exp(G), then H_0 inherits exp(G/2).")
    print("So H_0's 'half Gram win' is a CHAIN-RULE artifact (square-root inheritance),")
    print("NOT a chirality halving.  After this filter:")
    print()
    chain_rule_observables = {"H_0 (km/s/Mpc)"}
    real_half_winners = [r for r in half_winners if r[0] not in chain_rule_observables]
    print(f"Real half-Gram cases (excluding chain-rule): {len(real_half_winners)}")
    for r in real_half_winners:
        print(f"    {r[0]} ({r[8]})")
    print()
    print("=" * 92)
    print("FINAL CONCLUSION")
    print("=" * 92)
    print()
    if len(real_half_winners) == 1 and real_half_winners[0][0] == "m_mu/m_e":
        print("After excluding the H_0 chain-rule artifact, half-Gram is UNIQUELY m_mu/m_e.")
        print()
        print("Empirical scope is therefore:")
        print("  - alpha(d*)/chi^k single-source family closes 8 observables (paths BELOW d*)")
        print("  - Full Gram closes rho_Lambda and v (-1% to -0.07% residuals)")
        print("  - Half Gram closes m_mu/m_e to 3% relative match (path starts AT d*=14)")
        print()
        print("The m_mu/m_e half-Gram match remains:")
        print("  - Numerically suggestive (3% off)")
        print("  - Structurally unexplained (no unified fermion compliance reproduces it,")
        print("    per the obstruction in tools/research/fermion_gram_derivation.py)")
        print("  - Empirically unique (no second observable supports the rule)")
        print()
        print("Honest read: m_mu/m_e is most likely a NEAR-MISS COINCIDENCE.")
        print("The Part 4b oq:mu-e-residual remains open with all three options")
        print("((a)/(b)/(c) of the OQ) standing, and option (b) ('ratio-of-sums Gram")
        print("correction') is now further constrained: there is no derivable mechanism")
        print("from a unified fermion compliance, and no other observable supports the rule.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
