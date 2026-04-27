#!/usr/bin/env python3
"""
Empirical scope mapping for the chirality-halved Gram hypothesis.

Background
----------
The cascade scalar action's compliance generates the per-step Gram
correction:
    log C^2_{d, d+1}  =  -(1/2) Delta^2 log alpha |_{2d+2}    [Cor 14.4]
which gives the path-distributed correction
    delta Q / Q_0  =  sum_{adj} (1 - C^2_{d, d+1}) ::=: G(path)
applied as Q = Q_0 * exp(G).  This is the "full Gram" correction.

Earlier in this session, an empirical observation on m_mu/m_e suggested
that the chirality-halved version
    Q = Q_0 * exp(G / chi),    chi = 2
closes m_mu/m_e to ~ 1e-5 residual.

Hypothesis to test (warm-up A): does chirality-halving work
  (i) only for fermion ratios (chirality-relevant observables),
  (ii) universally (a structural rescaling), or
  (iii) inconsistently across observables?

Method
------
For each documented descent-dependent observable with a known cascade
path, compute:
  - Q_leading: cascade leading prediction
  - Q_full_Gram = Q_leading * exp(G)       [standard formulation]
  - Q_half_Gram = Q_leading * exp(G / 2)   [chirality-halved]
  - Q_observed: experimental value
Report relative residuals (Q_pred - Q_obs) / Q_obs.

The signature pattern:
  - Scalar / cosmological observables (rho_Lambda, omega_m): expect full
    Gram to work, halved to under-correct.
  - Fermion ratios / chirality-coupled (m_mu/m_e): halved should work.
  - In between (mixed sectors): may distinguish universal vs fermion-specific.
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def log_R(d: int) -> float:
    return float(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def R(d: int) -> float:
    return math.exp(log_R(d))


def C_squared(d_i: int, d_j: int) -> float:
    """C^2_{d_i, d_j} = R(d_i + d_j + 1)^2 / [R(2 d_i + 1) R(2 d_j + 1)]."""
    return math.exp(
        2 * log_R(d_i + d_j + 1) - log_R(2 * d_i + 1) - log_R(2 * d_j + 1)
    )


def gram_sum(d_start: int, d_end: int) -> float:
    """Adjacent-pair Gram sum G = sum_{d = d_start..d_end-1} (1 - C^2_{d, d+1})."""
    return sum(1.0 - C_squared(d, d + 1) for d in range(d_start, d_end))


def main() -> int:
    print("=" * 78)
    print("EMPIRICAL SCOPE MAPPING: CHIRALITY-HALVED GRAM ACROSS OBSERVABLES")
    print("=" * 78)
    print()
    print("For each descent-dependent observable with a known cascade path,")
    print("compare Q_leading * exp(G) (full Gram) and Q_leading * exp(G/2)")
    print("(chirality-halved) against experiment.")
    print()

    chi = 2.0  # Euler characteristic of even-sphere layers, S^{2n}, chi = 2

    # --------------------------------------------------------------
    # Observable specifications: (name, path_start, path_end, Q_leading, Q_obs, sector)
    # --------------------------------------------------------------
    # path_end is INCLUSIVE-of-final-layer; gram_sum uses d in [start, end-1] for adjacent pairs.
    # Q_leading is the cascade pre-correction value documented in Part 0.0 / Part 4b.
    # Q_obs is the experimental value.
    #
    # Sources:
    #   alpha_s, ell_A, m_tau/m_mu: Part 0.0 verification table (sec:verification)
    #   m_mu/m_e: Part 4b oq:mu-e-residual (Q_leading = 206.50; Q_obs = 206.7683)
    #   rho_Lambda: Part I Theorem 3.1 + Theorem on observer frame
    #               (Q_leading = 6.996e-121, Q_obs = 7.150e-121)
    # --------------------------------------------------------------
    observables = [
        # (name, d_start, d_end_inclusive, Q_leading, Q_obs, sector)
        ("alpha_s(M_Z)",       5, 12, 0.1159,        0.1179,        "gauge coupling"),
        ("ell_A",              5, 12, 297.6,         301.6,         "CMB scalar"),
        ("m_tau/m_mu",         6, 13, 16.53,         16.82,         "fermion ratio"),
        ("m_mu/m_e",          14, 21, 206.50,        206.7683,      "fermion ratio"),
        # rho_Lambda: very long path; G computed up to 216 (217 layers) -- Part I sums
        # over d=5..216 (adjacent pairs from layers 5..217)
        ("rho_Lambda",         5, 216, 6.996e-121,   7.150e-121,    "scalar / CC"),
    ]

    print(f"{'Observable':>18} {'sector':>18}  {'path':>10}  "
          f"{'pre %':>8}  {'full Gram %':>11}  {'half Gram %':>11}  {'verdict':>20}")
    print("-" * 100)
    for name, d_start, d_end, Q_leading, Q_obs, sector in observables:
        G = gram_sum(d_start, d_end)
        Q_full = Q_leading * math.exp(G)
        Q_half = Q_leading * math.exp(G / chi)
        pre_pct = 100 * (Q_leading - Q_obs) / Q_obs
        full_pct = 100 * (Q_full - Q_obs) / Q_obs
        half_pct = 100 * (Q_half - Q_obs) / Q_obs
        # Verdict: which is closest to 0?
        if abs(full_pct) < abs(half_pct) and abs(full_pct) < abs(pre_pct):
            verdict = "FULL Gram wins"
        elif abs(half_pct) < abs(full_pct) and abs(half_pct) < abs(pre_pct):
            verdict = "HALF Gram wins"
        else:
            verdict = "neither helps"
        print(
            f"{name:>18} {sector:>18}  {f'{d_start}..{d_end+1}':>10}  "
            f"{pre_pct:>+8.3f}  {full_pct:>+11.4f}  {half_pct:>+11.4f}  {verdict:>20}"
        )
    print()

    # --------------------------------------------------------------
    # Detail for each observable: G value + path
    # --------------------------------------------------------------
    print("Detail: Gram sums and chirality factors")
    print("-" * 78)
    for name, d_start, d_end, Q_leading, Q_obs, sector in observables:
        G = gram_sum(d_start, d_end)
        print(f"  {name}: path d={d_start}..{d_end+1}, G = {G:.6e}, G/chi = {G/chi:.6e}")
    print()

    print("=" * 78)
    print("INTERPRETATION")
    print("=" * 78)
    print()
    print("The pattern across observables tells us whether chirality-halving is:")
    print("  - UNIVERSAL: half Gram wins for all (a structural rescaling)")
    print("  - FERMION-SPECIFIC: half wins for fermion ratios, full wins for scalars")
    print("  - NEITHER: both formulations under/over-shoot inconsistently")
    print()
    print("Result above determines which structural derivation to chase next.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
