#!/usr/bin/env python3
"""Cascade regime content sums and ratios.

Computes per-regime sphere-area sums (Omega_d) and per-regime
Gram-corrected sums, plus various inter-regime ratios.

Regimes (cascade = descent from infinity to observer's host d_V = 5;
layers below the observer are reported separately for context but are
not part of the cascade descent per Part 1 lines 609-642):

    Growth below observer  : d in {0..4}            (p(d) < 0, below host)
    Growth above observer  : d in {5, 6}             (p(d) < 0, in descent)
    Decay                  : d in {7..19}            (0 < p(d) < c_1)
    Exponential decay      : d in {20..217}          (c_1 < p(d) < c_2)
    Oblivion               : d in {218..}            (p(d) > c_2)

Gram correction (Part 0 Section 9, Part 1 Section 3 lines 609-642):
    Full cascade Gram sum is over pair indices d in {5..216}.
    Pair (d, d+1) is assigned to the regime of its LOWER endpoint d.
    Growth-below and oblivion have no Gram contribution (outside the
    cascade's descent range).

All computations use mpmath (200 digits) so Omega_217 ~ 1e-120 is
exact to ~200 decimals.

Run from the repo root:
    python3 tools/research/cascade_regime_content.py
"""
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

import mpmath
from cascade_constants import mp, D_V, D_0, D_1, D_2

mpmath.mp.dps = 200

mpf = mpmath.mpf
pi = mp.pi


def overlap_deficit(d):
    """1 - C^2_{d,d+1} via Beta function identity (Part 0 Thm overlap).

    C^2_{d,d+1} = B(1/2, d + 3/2)^2 / [B(1/2, d + 1) * B(1/2, d + 2)]
    """
    def B(a, b):
        return mpmath.gamma(a) * mpmath.gamma(b) / mpmath.gamma(a + b)
    half = mpf(1) / 2
    num = B(half, mpf(d) + mpf(3)/2) ** 2
    den = B(half, mpf(d) + 1) * B(half, mpf(d) + 2)
    return 1 - num / den


# Regime definitions: (name, d_low, d_high, gram_pairs_range_or_None)
# gram_pairs_range is the range of pair-indices d such that pair (d, d+1)
# is assigned to this regime (lower endpoint convention).  None means no
# Gram contribution from this regime.
REGIMES = [
    ("Growth below observer",  0,   4,    None),
    ("Growth above observer",  5,   6,    (5,   6)),
    ("Decay",                  7,  19,    (7,  19)),
    ("Exponential decay",     20, 217,    (20, 216)),
    ("Oblivion",              218, 2000,  None),
]


def fmt(x, digits=10):
    """Format mpf, fixed precision."""
    return mpmath.nstr(x, digits)


def main():
    print("=" * 80)
    print("Cascade regime content sums  (uncorrected + Gram-corrected)")
    print("=" * 80)
    print()
    print("Convention: pair (d, d+1) assigned to regime of lower endpoint d.")
    print("Full cascade Gram pairs: d in {5..216}, total 212 pairs.")
    print()

    # Compute each regime
    rows = []
    total_uncorr = mpf(0)
    total_gram_sum = mpf(0)
    total_corr = mpf(0)
    for name, d_lo, d_hi, gram_range in REGIMES:
        n_layers = d_hi - d_lo + 1
        sphere_sum = sum(mp.Omega(d) for d in range(d_lo, d_hi + 1))
        if gram_range is not None:
            g_lo, g_hi = gram_range
            n_pairs = g_hi - g_lo + 1
            gram_sum = sum(overlap_deficit(d) for d in range(g_lo, g_hi + 1))
        else:
            n_pairs = 0
            gram_sum = mpf(0)
        gram_factor = mpmath.exp(gram_sum)
        gram_corrected = sphere_sum * gram_factor
        rows.append((name, n_layers, n_pairs, sphere_sum, gram_sum,
                     gram_factor, gram_corrected))
        total_uncorr += sphere_sum
        total_gram_sum += gram_sum
        total_corr += gram_corrected

    # Header
    print(f"{'Regime':25s} {'Layers':>7s} {'Pairs':>6s}  "
          f"{'Uncorrected sum':>22s}  "
          f"{'Gram sum':>12s}  "
          f"{'Gram factor':>12s}  "
          f"{'Gram-corrected sum':>22s}")
    print("-" * 120)
    for (name, nl, np_, ssum, gsum, gfac, gcorr) in rows:
        if name == "Oblivion":
            ssum_str = mpmath.nstr(ssum, 10)
            gcorr_str = mpmath.nstr(gcorr, 10)
        else:
            ssum_str = mpmath.nstr(ssum, 10)
            gcorr_str = mpmath.nstr(gcorr, 10)
        print(f"{name:25s} {nl:>7d} {np_:>6d}  "
              f"{ssum_str:>22s}  "
              f"{mpmath.nstr(gsum, 8):>12s}  "
              f"{mpmath.nstr(gfac, 10):>12s}  "
              f"{gcorr_str:>22s}")
    print("-" * 120)
    print(f"{'TOTAL':25s} {'':>7s} {'':>6s}  "
          f"{mpmath.nstr(total_uncorr, 10):>22s}  "
          f"{mpmath.nstr(total_gram_sum, 8):>12s}  "
          f"{mpmath.nstr(mpmath.exp(total_gram_sum), 10):>12s}  "
          f"{mpmath.nstr(total_corr, 10):>22s}")
    print()

    # Active cascade (excluding growth-below and oblivion)
    active_uncorr = sum(r[3] for r in rows if r[0] not in
                       ("Growth below observer", "Oblivion"))
    active_corr = sum(r[6] for r in rows if r[0] not in
                     ("Growth below observer", "Oblivion"))
    print(f"  Active cascade (d=5..217), uncorrected:    {fmt(active_uncorr)}")
    print(f"  Active cascade (d=5..217), Gram-corrected: {fmt(active_corr)}")
    print()

    # ------------------------------------------------------------------
    # Frame corrections
    # ------------------------------------------------------------------
    print("-" * 80)
    print("Frame corrections (Part 1)")
    print("-" * 80)
    Omega_2 = mp.Omega(2)
    Omega_3 = mp.Omega(3)
    Omega_5 = mp.Omega(5)
    Omega_7 = mp.Omega(7)
    proj_3d = Omega_2 / Omega_3
    host_2 = (Omega_5 / Omega_7) ** 2
    cc_factor = proj_3d * host_2
    print(f"  3D projection (Omega_2/Omega_3 = 2/pi):  {fmt(proj_3d)}")
    print(f"  Host frame (Omega_5/Omega_7)^2 = 9/pi^2: {fmt(host_2)}")
    print(f"  Combined CC factor (18/pi^3):            {fmt(cc_factor)}")
    print()

    # ------------------------------------------------------------------
    # Cosmological constant (cascade formula)
    # ------------------------------------------------------------------
    print("-" * 80)
    print("Cosmological constant (cascade formula)")
    print("-" * 80)
    Omega_19 = mp.Omega(19)
    Omega_217 = mp.Omega(217)
    bilinear = Omega_19 * Omega_217
    cc_leading = cc_factor * bilinear

    # Full cascade Gram sum: d = 5..216
    gram_full = sum(overlap_deficit(d) for d in range(5, 217))
    gram_exp_full = mpmath.exp(gram_full)
    cc_gram = cc_leading * gram_exp_full

    print(f"  Omega_19                         = {fmt(Omega_19)}")
    print(f"  Omega_217                        = {fmt(Omega_217)}")
    print(f"  Bilinear Omega_19 * Omega_217    = {fmt(bilinear)}")
    print(f"  CC leading (18/pi^3 * bilinear)  = {fmt(cc_leading)}")
    print(f"  Full Gram sum (d=5..216)         = {fmt(gram_full)}")
    print(f"  Gram factor exp(...)             = {fmt(gram_exp_full)}")
    print(f"  CC (Gram-corrected, predicted)   = {fmt(cc_gram)}")
    print(f"  CC observed (Planck): 7.150e-121 +/- 1.9%")
    print()

    # ------------------------------------------------------------------
    # Frame-corrected oblivion
    # ------------------------------------------------------------------
    print("-" * 80)
    print("Frame-corrected oblivion (bilinear scaling, 18/pi^3)")
    print("-" * 80)
    oblivion_row = next(r for r in rows if r[0] == "Oblivion")
    oblivion_uncorr = oblivion_row[3]
    fc_oblivion_full = cc_factor * oblivion_uncorr
    print(f"  Oblivion sum (uncorrected): {fmt(oblivion_uncorr)}")
    print(f"  Frame-corrected (x 18/pi^3): {fmt(fc_oblivion_full)}")
    print(f"  CC / fc_oblivion:            {fmt(cc_gram / fc_oblivion_full)}")
    print()

    # ------------------------------------------------------------------
    # Other ratios of interest
    # ------------------------------------------------------------------
    print("-" * 80)
    print("Inter-regime ratios")
    print("-" * 80)
    growth_below = rows[0][3]
    growth_above = rows[1][3]
    decay = rows[2][3]
    exp_decay = rows[3][3]
    oblivion = rows[4][3]
    print(f"  Growth_below / Active   = {fmt(growth_below/active_uncorr)}")
    print(f"  Growth_above / Decay    = {fmt(growth_above/decay)}")
    print(f"  Decay / Exp_decay       = {fmt(decay/exp_decay)}")
    print(f"  Exp_decay / Oblivion    = {fmt(exp_decay/oblivion)}")
    print(f"  Oblivion / Active       = {fmt(oblivion/active_uncorr)}")

    # Test 85/33 against CC / fc_oblivion ratio
    print()
    target_ratio = cc_gram / fc_oblivion_full
    candidate = mpf(85) / 33
    diff = target_ratio - candidate
    print(f"  CC / fc_oblivion         = {fmt(target_ratio, 20)}")
    print(f"  85/33                    = {fmt(candidate, 20)}")
    print(f"  Difference               = {fmt(diff)}")
    print(f"  Relative                 = {fmt(diff/target_ratio*100)} %")


if __name__ == "__main__":
    main()
