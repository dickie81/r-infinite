#!/usr/bin/env python3
"""
Test the unified framework: delta Phi = (1/chi^k) sum (1 - C^2) over a path,
for each cascade observable with known leading prediction and observed value.

For each observable:
1. Compute the implied delta Phi = log(observed/leading).
2. Compute the natural Gram path sum.
3. Find the closest integer chirality power k (0, 1, 2, 3).
4. Compare to Part IVb's alpha(d*)/chi^k closure (if applicable).

The hypothesis: every descent-dependent observable closes via either
  (A) Single-source: alpha(d*)/chi^k  (Part IVb's family)
or
  (B) Path-distributed: (1/chi^k) * sum_path (1 - C^2)  (chirality-halved Gram)
with both derived from the cascade scalar action.
"""

import math

import numpy as np
from scipy.special import betaln, gammaln


def beta(a, b):
    return math.exp(betaln(a, b))


def R_func(d):
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha_func(d):
    return R_func(d) ** 2 / 4.0


def gram_C2(d1, d2):
    if d1 == d2:
        return 1.0
    G_11 = beta(0.5, d1 + 1.0)
    G_22 = beta(0.5, d2 + 1.0)
    G_12 = beta(0.5, (d1 + d2) / 2.0 + 1.0)
    return G_12 ** 2 / (G_11 * G_22)


def gram_path_sum(path):
    """Sum of (1 - C^2_{d, d+1}) over consecutive layer pairs in path."""
    return sum(1.0 - gram_C2(path[k], path[k + 1]) for k in range(len(path) - 1))


def fit_chirality_power(needed_correction, gram_sum):
    """Find the chirality power k such that gram_sum / chi^k matches needed."""
    chi = 2.0
    if gram_sum <= 0 or needed_correction <= 0:
        return None
    raw_ratio = gram_sum / needed_correction
    # log_chi(raw_ratio) gives the power
    return math.log(raw_ratio) / math.log(chi)


def main():
    print("=" * 78)
    print("UNIFIED FRAMEWORK TEST: chirality-halved Gram for cascade observables")
    print("=" * 78)
    print()
    print("Hypothesis: delta Phi = (1/chi^k) * sum_path (1 - C^2_{d,d+1})")
    print("            for some integer k >= 0 and natural path.")
    print()

    # Each entry: (name, leading, observed, path, sign, notes)
    # sign = +1 for descent (positive Gram), -1 for geometric (negative)
    observables = [
        # Already closed by Part IVb alpha(d*)/chi^k:
        ("alpha_s",       0.1159,  0.1179,    list(range(5, 13)),  +1, "Closed by alpha(14)/chi"),
        ("m_tau/m_mu",    16.53,   16.82,     list(range(6, 14)),  +1, "Closed by alpha(14)/chi"),
        ("m_tau abs MeV", 1755.0,  1776.86,   list(range(5, 13)),  +1, "Closed by alpha(19)/chi"),

        # Closed by Gram alone (no chirality halving needed):
        ("rho_Lambda",    0.6996, 0.7150,     list(range(5, 218)), +1, "Closed by full Gram (chi^0)"),
        # Note: rho_Lambda values are *10^-120, but ratio is what matters.

        # Open / target:
        ("m_mu/m_e",      206.50,  206.77,    list(range(14, 22)), +1, "OPEN: target for chirality-halved Gram"),

        # Cosmological (use full Gram per Part I):
        ("H_0 km/s/Mpc",  66.78,   67.4,      list(range(5, 218)), +1, "Closed by full Gram via rho_Lambda"),

        # m_b/m_s closed by alpha(7)/chi^4 (Part IVb)
        # b/s leading 44.93, observed 44.75; ratio 0.996 => negative correction
        ("b/s",           44.93,   44.75,     list(range(7, 13)),  -1, "Closed by -alpha(7)/chi^4"),
    ]

    print("-" * 78)
    print("Per-observable analysis")
    print("-" * 78)
    print(f"{'Observable':>16}  {'lead':>10}  {'obs':>10}  {'dev %':>8}  "
          f"{'needed dPhi':>12}  {'path sum':>12}  {'fitted k':>10}")
    print("-" * 78)

    for name, lead, obs, path, sign, note in observables:
        # Multiplicative deviation
        if lead > 0 and obs > 0:
            dev_pct = (obs - lead) / lead * 100.0
            log_ratio = math.log(obs / lead)  # this is the needed delta Phi
            needed = sign * log_ratio  # apply sign convention
        else:
            dev_pct = float("nan")
            log_ratio = float("nan")
            needed = float("nan")

        # Compute path sum
        gs = gram_path_sum(path)

        # Fit the chirality power
        if needed > 0 and gs > 0:
            k_fit = fit_chirality_power(needed, gs)
        else:
            k_fit = None

        if k_fit is not None:
            k_str = f"{k_fit:.3f}"
        else:
            k_str = "n/a"

        print(
            f"{name:>16}  {lead:>10.4g}  {obs:>10.4g}  {dev_pct:>+7.2f}%  "
            f"{needed:>12.6e}  {gs:>12.6e}  {k_str:>10}"
        )

    print()
    print("-" * 78)
    print("Reading: 'fitted k' is the chirality power needed for the ratio")
    print("         (1/chi^k) * gram_path_sum = needed delta Phi.")
    print("-" * 78)
    print()
    print("If fitted k is close to a small integer (0, 1, 2, 3),")
    print("the observable fits the chirality-halved Gram framework.")
    print()

    # ------------------------------------------------------------------
    # Detailed test: m_mu/m_e
    # ------------------------------------------------------------------
    print("-" * 78)
    print("DETAILED: m_mu/m_e (the target)")
    print("-" * 78)
    lead = 206.50
    obs = 206.77
    path = list(range(14, 22))
    gs = gram_path_sum(path)
    dphi = math.log(obs / lead)
    print(f"  Leading: {lead}")
    print(f"  Observed: {obs}")
    print(f"  Needed delta Phi = log(obs/lead) = {dphi:.6e}")
    print(f"  Path d={path[0]}..{path[-1]}, sum (1-C^2) = {gs:.6e}")
    print()
    print(f"  k=0: full Gram, gs/1 = {gs:.6e} (ratio gs/needed = {gs/dphi:.3f})")
    print(f"  k=1: half Gram, gs/2 = {gs/2:.6e} (ratio = {gs/2/dphi:.3f})")
    print(f"  k=2: quarter,   gs/4 = {gs/4:.6e} (ratio = {gs/4/dphi:.3f})")
    print()
    print(f"  Predicted m_mu/m_e under k=1 (chirality halving):")
    pred_k1 = lead * math.exp(gs / 2)
    print(f"    = {lead} * exp({gs/2:.6e}) = {pred_k1:.4f}")
    print(f"    Observed: {obs}")
    print(f"    Residual: ({pred_k1} - {obs})/{obs} = {(pred_k1 - obs)/obs*100:+.4f}%")
    print()

    # ------------------------------------------------------------------
    # Detailed test: rho_Lambda (full Gram, chi^0)
    # ------------------------------------------------------------------
    print("-" * 78)
    print("DETAILED: rho_Lambda (full Gram, chi^0)")
    print("-" * 78)
    lead = 0.6996  # *10^-120
    obs = 0.7150
    path = list(range(5, 218))
    gs = gram_path_sum(path)
    dphi = math.log(obs / lead)
    print(f"  Leading rho_Lambda/M^4 = {lead}e-120")
    print(f"  Observed: {obs}e-120")
    print(f"  Needed delta Phi = log(obs/lead) = {dphi:.6e}")
    print(f"  Path d={path[0]}..{path[-1]}, sum (1-C^2) = {gs:.6e}")
    print()
    print(f"  Predicted under k=0 (no chirality halving):")
    pred_k0 = lead * math.exp(gs)
    print(f"    = {lead} * exp({gs:.6e}) = {pred_k0:.6f}")
    print(f"    Observed: {obs}")
    print(f"    Residual: ({pred_k0} - {obs})/{obs} = {(pred_k0 - obs)/obs*100:+.4f}%")
    print()

    # ------------------------------------------------------------------
    # Pattern recognition: which observables fit chi^k for small k?
    # ------------------------------------------------------------------
    print("-" * 78)
    print("PATTERN: integer chirality powers across observables")
    print("-" * 78)
    print()
    print("Observables that already have alpha(d*)/chi^k closures (Part IVb):")
    print("  alpha_s, m_tau/m_mu: alpha(14)/chi^1   -> chi^1 (single-channel)")
    print("  m_tau abs, ell_A:    alpha(19)/chi^1   -> chi^1 (single-channel)")
    print("  sin^2 theta_W, Omega_m: alpha(5)/chi^3 -> chi^3 (three-channel)")
    print("  theta_C:             alpha(7)/chi^2   -> chi^2 (two-channel mixing)")
    print("  b/s:                 alpha(7)/chi^4   -> chi^4 (more channels)")
    print()
    print("Observables proposed to fit chirality-halved Gram (this work):")
    print("  m_mu/m_e:  chi^1 halving of Gram(d=14..21)  -> single-channel")
    print()
    print("Observables that fit FULL Gram (chi^0):")
    print("  rho_Lambda: full Gram(d=5..217)")
    print("  H_0:        full Gram (inherits from rho_Lambda)")
    print()
    print("The chirality power k mirrors the observable's 'channel count':")
    print("  k=0: cosmological (no chirality structure)")
    print("  k=1: single channel (m_mu/m_e ratio, alpha_s, gauge couplings)")
    print("  k=2: two-channel mixing (Cabibbo)")
    print("  k=3: three-channel integration (Weinberg, matter fraction)")
    print("  k=4: four-channel (b/s)")
    print()

    # ------------------------------------------------------------------
    # The proposal: m_mu/m_e closure
    # ------------------------------------------------------------------
    print("=" * 78)
    print("PROPOSAL: close m_mu/m_e via chirality-halved Gram")
    print("=" * 78)
    print()
    print("delta Phi_{m_mu/m_e} = (1/chi) * sum_{d=14..20} (1 - C^2_{d, d+1})")
    lead = 206.50
    obs = 206.77
    path = list(range(14, 22))
    gs = gram_path_sum(path)
    delta = gs / 2.0
    pred = lead * math.exp(delta)
    print(f"  = (1/2) * {gs:.6e} = {delta:.6e}")
    print()
    print(f"  m_mu/m_e_predicted = {lead} * exp({delta:.6e}) = {pred:.4f}")
    print(f"  m_mu/m_e_observed  = {obs:.4f}")
    print(f"  Residual           = {(pred - obs)/obs*100:+.4f}%")
    print()
    print("If accepted, this:")
    print("  1. Closes Part IVb's m_mu/m_e open question.")
    print("  2. Establishes the chirality-halved Gram pattern.")
    print("  3. Unifies the two correction families (single-source + path-distributed)")
    print("     under the cascade scalar action with shared chirality halving.")
    print()


if __name__ == "__main__":
    main()
