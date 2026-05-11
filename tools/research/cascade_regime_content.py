#!/usr/bin/env python3
"""Cascade regime content sums and ratios.

Computes sum of sphere areas Omega_d in each regime (growth, decay,
exponential decay, oblivion), frame-corrected oblivion content, and
tests candidate closed-form expressions for the ratio CC / fc_oblivion.

All computations use mpmath (200 digits) to handle Omega_217 ~ 1e-120
without precision loss.

Regimes (cascade = descent from infinity to observer's host d_V = 5):
    Growth:    d in {5, 6}            (p(d) < 0)
    Decay:     d in {7, ..., 19}       (0 < p(d) < c_1)
    Exp decay: d in {20, ..., 217}     (c_1 < p(d) < c_2)
    Oblivion:  d in {218, ...}         (p(d) > c_2)

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


def regime_sum(d_lo, d_hi):
    """Sum Omega_d for d in [d_lo, d_hi] inclusive."""
    return sum(mp.Omega(d) for d in range(d_lo, d_hi + 1))


def oblivion_sum(d_start=218, d_end=2000):
    """Sum Omega_d for d >= d_start.  Truncate at d_end (Omega decays so
    fast that 2000 layers is far more than needed)."""
    return sum(mp.Omega(d) for d in range(d_start, d_end + 1))


def fmt(x, digits=6):
    """Format mpf as e-notation, controlled precision."""
    return mpmath.nstr(x, digits)


def main():
    print("=" * 72)
    print("Cascade regime content sums (cascade = d >= 5, observer's host)")
    print("=" * 72)

    growth = regime_sum(5, 6)
    decay = regime_sum(7, 19)
    exp_decay = regime_sum(20, 217)
    oblivion = oblivion_sum(218, 2000)
    total_active = growth + decay + exp_decay

    print(f"  Growth     (d=5..6)   = {fmt(growth)}")
    print(f"  Decay      (d=7..19)  = {fmt(decay)}")
    print(f"  Exp decay  (d=20..217)= {fmt(exp_decay)}")
    print(f"  Oblivion   (d>=218)   = {fmt(oblivion)}")
    print()
    print(f"  Active cascade (non-oblivion) = {fmt(total_active)}")
    print(f"  Total cascade content         = {fmt(total_active + oblivion)}")

    print()
    print("-" * 72)
    print("Regime fractions of active cascade")
    print("-" * 72)
    print(f"  Growth    / active = {fmt(growth/total_active*100)}%")
    print(f"  Decay     / active = {fmt(decay/total_active*100)}%")
    print(f"  Exp decay / active = {fmt(exp_decay/total_active*100)}%")
    print(f"  Oblivion  / active = {fmt(oblivion/total_active)}")

    print()
    print("-" * 72)
    print("Frame corrections (Part 1)")
    print("-" * 72)
    Omega_2 = mp.Omega(2)
    Omega_3 = mp.Omega(3)
    Omega_5 = mp.Omega(5)
    Omega_7 = mp.Omega(7)
    proj_3d = Omega_2 / Omega_3   # 2/pi
    host_2 = (Omega_5 / Omega_7) ** 2   # 9/pi^2
    cc_factor = proj_3d * host_2   # 18/pi^3
    print(f"  3D projection (Omega_2/Omega_3 = 2/pi):        {fmt(proj_3d, 12)}")
    print(f"  Host frame (Omega_5/Omega_7)^2 = 9/pi^2:       {fmt(host_2, 12)}")
    print(f"  Combined CC factor (18/pi^3):                  {fmt(cc_factor, 12)}")

    print()
    print("-" * 72)
    print("Cosmological constant (cascade formula)")
    print("-" * 72)
    Omega_19 = mp.Omega(19)
    Omega_217 = mp.Omega(217)
    bilinear = Omega_19 * Omega_217
    cc_leading = cc_factor * bilinear

    # Gram correction: sum (1 - C^2_{d,d+1}) for d = 5..216
    # C^2_{d,d+1} = B(1/2, d+3/2)^2 / [B(1/2, d+1) * B(1/2, d+2)]
    # Use Beta function form.
    def overlap_deficit(d):
        # B(1/2, x) = sqrt(pi) Gamma(x) / Gamma(x + 1/2)
        # so the ratio simplifies via Gamma identities.
        def B(a, b):
            return mpmath.gamma(a) * mpmath.gamma(b) / mpmath.gamma(a + b)
        half = mpf(1) / 2
        numerator = B(half, mpf(d) + mpf(3)/2) ** 2
        denominator = B(half, mpf(d) + 1) * B(half, mpf(d) + 2)
        return 1 - numerator / denominator

    gram_sum = sum(overlap_deficit(d) for d in range(5, 217))
    gram_exp = mpmath.exp(gram_sum)
    cc_gram = cc_leading * gram_exp

    print(f"  Omega_19           = {fmt(Omega_19)}")
    print(f"  Omega_217          = {fmt(Omega_217)}")
    print(f"  Bilinear           = {fmt(bilinear)}")
    print(f"  CC leading         = {fmt(cc_leading)}")
    print(f"  Gram sum           = {fmt(gram_sum, 12)}")
    print(f"  Gram exp factor    = {fmt(gram_exp, 12)}")
    print(f"  CC (Gram-corrected)= {fmt(cc_gram)}  [predicted]")
    print(f"  CC observed (Planck): 7.150e-121 +/- 1.9%")

    print()
    print("-" * 72)
    print("Frame-corrected oblivion sum")
    print("-" * 72)
    fc_oblivion_full = cc_factor * oblivion        # bilinear-style (18/pi^3)
    fc_oblivion_single = (Omega_5/Omega_7) * proj_3d * oblivion  # single-content
    print(f"  Raw oblivion sum:                    {fmt(oblivion)}")
    print(f"  Frame-corrected (18/pi^3 * oblivion):{fmt(fc_oblivion_full)}")
    print(f"  Frame-corrected (6/pi^2 * oblivion): {fmt(fc_oblivion_single)}")

    print()
    print("-" * 72)
    print("The ratio CC / fc_oblivion")
    print("-" * 72)
    ratio_full = cc_gram / fc_oblivion_full
    ratio_single = cc_gram / fc_oblivion_single
    print(f"  CC / fc_oblivion (bilinear frame): {fmt(ratio_full, 12)}")
    print(f"  CC / fc_oblivion (single frame):   {fmt(ratio_single, 12)}")

    # Note the 18/pi^3 cancels in CC/fc_oblivion_full
    ratio_intrinsic = Omega_19 * Omega_217 * gram_exp / oblivion
    print(f"  Intrinsic ratio Omega_19*Omega_217*Gram/oblivion = "
          f"{fmt(ratio_intrinsic, 12)}")

    print()
    print("-" * 72)
    print("Candidate closed forms for the ratio (bilinear, ~2.574)")
    print("-" * 72)
    target = ratio_full
    candidates = {
        "5 * Omega_19":          5 * Omega_19,
        "d_V * Omega_19":        mpf(D_V) * Omega_19,
        "sqrt(2*pi)":            mpmath.sqrt(2*pi),
        "pi^2 / 4":              pi**2 / 4,
        "e":                     mpmath.e,
        "e^(0.946)":             mpmath.exp(mpf("0.946")),
        "pi - 0.56":             pi - mpf("0.56"),
        "45^(1/4)":              mpf(45) ** (mpf(1)/4),
        "sqrt(109/pi) * Omega_19": mpmath.sqrt(109/pi) * Omega_19,
        "(d_2 - d_1)^(1/12)":    (mpf(D_2 - D_1)) ** (mpf(1)/12),
    }
    print(f"  Target ratio: {fmt(target, 12)}")
    print()
    for name, val in candidates.items():
        diff = (val - target) / target * 100
        print(f"  {name:30s} = {fmt(val, 8):16s}  "
              f"({fmt(diff, 4)}% off)")

    print()
    print("-" * 72)
    print("Other ratios of interest")
    print("-" * 72)
    print(f"  Growth / Decay = {fmt(growth/decay, 8)}")
    print(f"  Decay / Exp_decay = {fmt(decay/exp_decay, 8)}")
    print(f"  Exp_decay / Oblivion = {fmt(exp_decay/oblivion, 6)}")
    print(f"  Oblivion / Active = {fmt(oblivion/total_active, 6)}")
    print(f"  CC * fc_oblivion (bilinear) = {fmt(cc_gram * fc_oblivion_full, 6)}")
    print(f"  Compared to Omega_3 = 2 pi^2 = {fmt(2*pi**2, 8)}")


if __name__ == "__main__":
    main()
