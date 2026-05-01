#!/usr/bin/env python3
"""
(R1b) attack via Gram normalization of U(1)_Y on the path-tensor.

GOAL
====
Derive cascade-natively that the sector-fundamental U(1)_Y unit is
1 / (dim V_12 * dim V_13) for matter in the (V_12, V_13) sector.

THE STRUCTURAL HYPOTHESIS
==========================
For matter in path-tensor V_12 otimes V_13 otimes V_14, the U(1)_Y
action exp(i Y theta) acts on V_14.  The smallest non-zero Y consistent
with cascade structure is set by the Gram-normalized 'effective path-
tensor dimension':

  Y_smallest_for_(V_12, V_13)_sector = 1 / (effective path-tensor dim)

If 'effective path-tensor dim' = dim V_12 * dim V_13, the sector-
fundamental rule holds.

THE GRAM ANGLE
==============
Gram structure (Part 0 Supplement) provides cascade-native overlap
between cascade layers:
  G_{d, d'} = int_{-1}^{1} (1-x^2)^((d+d')/2) dx = B(1/2, (d+d')/2 + 1)
  C^2_{d, d+1} = R(2d+2)^2 / (R(2d+1) * R(2d+3))    (cascade-native form)
  Gram deficit 1 - C^2 > 0 strict (Cauchy-Schwarz).

Gram is cascade-native: built only from Gamma function values via Beta
function identities, no external input.

This script tests whether Gram structure gives:
  effective path-tensor dim = dim V_12 * dim V_13
for the four (V_12, V_13) sectors that appear in SM matter.

WHAT THIS SCRIPT DELIVERS
=========================
1. Computes Gram correlations C^2_{12, 13}, C^2_{13, 14}, C^2_{12, 14}.
2. Computes path-tensor 'effective dim' candidates from Gram identities.
3. Tests against the four SM sectors:
     (3, 2) -> needs 6
     (3, 1) -> needs 3
     (1, 2) -> needs 2
     (1, 1) -> needs 1
4. Reports whether Gram structure pins these values cascade-natively.

EPISTEMIC STATUS
================
Speculative attack.  Three outcomes possible:
  (a) Gram closes (R1b): sector-fundamental rule emerges from Gram
      identities cascade-natively.  Major win.
  (b) Gram doesn't close (R1b) but identifies a structural relation:
      partial progress on the uniqueness theorem.
  (c) Gram doesn't help: rule out Gram as the mechanism for (R1b).

Honest assessment expected; if (c), document and pivot.
"""

from __future__ import annotations

import math
import sys
from fractions import Fraction

import numpy as np
from scipy.special import gammaln, beta as scipy_beta


# ---------------------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------------------

def R_cascade(d):
    """Cascade radius R(d) = Gamma((d+1)/2) / Gamma((d+2)/2)."""
    return float(np.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0)))


def alpha_cascade(d):
    """Cascade gauge coupling alpha(d) = R(d)^2 / 4."""
    return R_cascade(d) ** 2 / 4.0


def gram(d_i, d_j):
    """Gram entry G_{d_i, d_j} = B(1/2, (d_i+d_j)/2 + 1)."""
    return scipy_beta(0.5, (d_i + d_j) / 2 + 1)


def gram_correlation(d, d_prime):
    """Normalized Gram correlation: C^2_{d, d'} = G_{d,d'}^2 / (G_{d,d} * G_{d',d'})."""
    G_dd = gram(d, d)
    G_pp = gram(d_prime, d_prime)
    G_dp = gram(d, d_prime)
    return G_dp ** 2 / (G_dd * G_pp)


def gram_deficit(d, d_prime):
    """1 - C^2_{d, d'}, the Gram first-order deficit."""
    return 1.0 - gram_correlation(d, d_prime)


# ---------------------------------------------------------------------------
# Step 1: Gram correlations at gauge window
# ---------------------------------------------------------------------------

def report_gram_correlations():
    print("=" * 78)
    print("STEP 1: Gram correlations at gauge window layers d in {12, 13, 14}")
    print("=" * 78)
    print()
    print(f"  {'pair':>10s}  {'C^2':>14s}  {'1 - C^2':>14s}  {'1/C^2':>14s}")
    pairs = [(12, 13), (12, 14), (13, 14), (12, 12), (13, 13), (14, 14),
             (5, 12), (5, 13), (5, 14)]
    for d, dp in pairs:
        if d != dp:
            C2 = gram_correlation(d, dp)
            print(f"  ({d:>2d}, {dp:>2d})  {C2:>14.10f}  {1 - C2:>14.10f}  "
                  f"{1.0 / C2:>14.10f}")
        else:
            print(f"  ({d:>2d}, {dp:>2d})  {'1.0 (self)':>14s}")
    print()


# ---------------------------------------------------------------------------
# Step 2: Test whether Gram quantities give sector-fundamental units
# ---------------------------------------------------------------------------

def test_sector_fundamental_units():
    print("=" * 78)
    print("STEP 2: do Gram quantities give sector-fundamental Y units?")
    print("=" * 78)
    print()
    print("Sector-fundamental units (target):")
    print("  (3, 2): 1/6 ≈ 0.16667 = sector unit for Q_L")
    print("  (3, 1): 1/3 ≈ 0.33333 = sector unit for u_R, d_R")
    print("  (1, 2): 1/2  = 0.50000 = sector unit for L_L, H")
    print("  (1, 1): 1                = sector unit for e_R")
    print()
    print("Test: do any cascade Gram-derived quantities at the gauge window")
    print("give these specific values?")
    print()

    # Compute various Gram-derived quantities
    G_12_13 = gram(12, 13)
    G_12_14 = gram(12, 14)
    G_13_14 = gram(13, 14)
    G_12_12 = gram(12, 12)
    G_13_13 = gram(13, 13)
    G_14_14 = gram(14, 14)

    C2_12_13 = G_12_13 ** 2 / (G_12_12 * G_13_13)
    C2_13_14 = G_13_14 ** 2 / (G_13_13 * G_14_14)
    C2_12_14 = G_12_14 ** 2 / (G_12_12 * G_14_14)

    quantities = [
        ("G_12_13",            G_12_13),
        ("G_13_14",            G_13_14),
        ("G_12_14",            G_12_14),
        ("C^2_12_13",          C2_12_13),
        ("C^2_13_14",          C2_13_14),
        ("C^2_12_14",          C2_12_14),
        ("1 - C^2_12_13",      1 - C2_12_13),
        ("1 - C^2_13_14",      1 - C2_13_14),
        ("alpha(12)",          alpha_cascade(12)),
        ("alpha(13)",          alpha_cascade(13)),
        ("alpha(14)",          alpha_cascade(14)),
        ("R(12)/R(13)",        R_cascade(12) / R_cascade(13)),
        ("R(13)/R(14)",        R_cascade(13) / R_cascade(14)),
        ("R(12)*R(13)",        R_cascade(12) * R_cascade(13)),
    ]

    targets = [
        ("(3, 2) -> 1/6", 1.0 / 6),
        ("(3, 1) -> 1/3", 1.0 / 3),
        ("(1, 2) -> 1/2", 1.0 / 2),
        ("(1, 1) -> 1",   1.0),
    ]

    print("Numerical comparison (targets vs Gram quantities):")
    print()
    print(f"  {'quantity':>20s}  {'value':>14s}  closest target?")
    for name, val in quantities:
        # Find closest target
        diffs = [(t_name, t_val, abs(val - t_val) / t_val) for t_name, t_val in targets]
        diffs.sort(key=lambda x: x[2])
        best = diffs[0]
        match_str = ""
        if best[2] < 0.01:
            match_str = f"<- MATCHES {best[0]} (within 1%)"
        elif best[2] < 0.05:
            match_str = f"close to {best[0]} ({best[2]*100:.1f}% off)"
        print(f"  {name:>20s}  {val:>14.6f}  {match_str}")
    print()


# ---------------------------------------------------------------------------
# Step 3: Multi-layer path-tensor Gram product
# ---------------------------------------------------------------------------

def test_path_tensor_gram_product():
    print("=" * 78)
    print("STEP 3: path-tensor Gram product across V_12, V_13, V_14 layers")
    print("=" * 78)
    print()
    print("The path-tensor V_12 ⊗ V_13 ⊗ V_14 spans 3 cascade layers.")
    print("If Gram structure normalizes the U(1)_Y action across the path-")
    print("tensor, the effective normalization might be a Gram product.")
    print()
    print("Test hypothesis: effective path-tensor dim =")
    print("  prod_over_layers (some Gram quantity)")
    print()

    # Try: product of Gram correlations
    C12_13 = gram_correlation(12, 13)
    C13_14 = gram_correlation(13, 14)

    print(f"  C^2_12_13 * C^2_13_14 = {C12_13 * C13_14:.6f}")
    print(f"  (1 - C^2_12_13) * (1 - C^2_13_14) = "
          f"{(1 - C12_13) * (1 - C13_14):.6f}")
    print(f"  1 / (C^2_12_13 * C^2_13_14) = {1 / (C12_13 * C13_14):.6f}")
    print()

    print("None of these naturally give 6 (for sector (3, 2)).")
    print()
    print("The Gram product structure does NOT obviously give the sector-")
    print("fundamental units.  The cascade Gram correlations between gauge-")
    print("window layers are O(1) numbers, not the integer-related normalization")
    print("that the sector-fundamental rule needs (1, 2, 3, 6).")
    print()


# ---------------------------------------------------------------------------
# Step 4: structural reading
# ---------------------------------------------------------------------------

def report_structural_reading():
    print("=" * 78)
    print("STEP 4: structural reading -- where does dim V_12 * dim V_13 come from?")
    print("=" * 78)
    print()
    print("The sector-fundamental unit 1/(dim V_12 * dim V_13) has integer")
    print("values 1, 2, 3, 6 = N_doublet * N_c at the relevant sectors.")
    print()
    print("These are NOT cascade Gram quantities (which are O(1) Beta-function")
    print("ratios).  They ARE cascade-native via:")
    print()
    print("  - dim V_12 = N_c = 3 from Adams' theorem at d=12 (rho(12) - 1 = 3)")
    print("  - dim V_13 = N_doublet = 2 from cascade SU(2) doublet structure")
    print("    at d=13 (right-mult algebra extended trivially)")
    print()
    print("Both are integer counts of cascade gauge structure, not Gram overlaps.")
    print()
    print("HONEST FINDING: Gram structure (per Part 0 Supplement) is cascade-")
    print("native but provides O(1) Beta-function-related corrections, not the")
    print("integer-valued sector dimensions that the sector-fundamental rule")
    print("requires.")
    print()
    print("The sector-fundamental dimensions (3, 2, 6) come from cascade")
    print("REPRESENTATION counting (V_12 dim, V_13 dim) directly, which is")
    print("itself cascade-native via Adams' theorem and cascade SU(2)/SU(3)")
    print("structure -- but this is a DIFFERENT cascade-native source than Gram")
    print("correlations.")
    print()
    print("CASCADE-NATIVE MECHANISM IDENTIFICATION")
    print("=========================================")
    print("The sector-fundamental rule needs cascade structure that:")
    print("  (i) gives the integer 6 = dim V_12 * dim V_13 for (3, 2) sector.")
    print(" (ii) ties this to U(1)_Y unit normalization at d=14.")
    print()
    print("Cascade primitives that DO give integer 6:")
    print("  - dim H^3 / Spin(4) = 12 / 4 = 3 = N_c. (cascade-native, Adams)")
    print("  - 2 = N_doublet from SU(2) right-mult algebra. (cascade-native)")
    print("  - 3 * 2 = 6 = dim path-tensor for (3, 2) sector.")
    print()
    print("These are cascade representation-theoretic, not Gram-correlation-")
    print("based.  Gram structure is the WRONG mechanism for this question.")
    print()
    print("WHAT WOULD CLOSE (R1b)")
    print("=======================")
    print("A cascade theorem stating: 'For matter in V_12 otimes V_13 otimes V_14")
    print("with V_14 = 1-dim, the U(1)_Y action's smallest non-trivial Y is")
    print("1 / (dim V_12 * dim V_13) in cascade-native units.'")
    print()
    print("This is cascade-native via:")
    print("  - dim V_12, dim V_13 from Adams + cascade SU(2)/SU(3) at d=12, 13.")
    print("  - U(1)_Y at d=14 generated by J on R^14 = C^7.")
    print("  - Path-tensor Hilbert space normalization (rem:path-tensor).")
    print()
    print("The mechanism is REPRESENTATION-THEORETIC, not Gram-correction-based.")
    print("Gram is a structurally-distinct cascade-native tool used for")
    print("delta-Phi corrections to observables, not for U(1)_Y unit pinning.")
    print()


# ---------------------------------------------------------------------------
# Step 5: status update
# ---------------------------------------------------------------------------

def report_status():
    print("=" * 78)
    print("STATUS")
    print("=" * 78)
    print()
    print("(R1b) attack via Gram structure: NEGATIVE result.")
    print()
    print("Gram structure (Part 0 Supplement) is genuinely cascade-native and")
    print("provides cascade-internal correction to descent observables. But it")
    print("does NOT supply the integer-valued sector dimensions (1, 2, 3, 6)")
    print("that the sector-fundamental rule requires.  Gram correlations at the")
    print("gauge window are O(1) Beta-function ratios, not integer sector dims.")
    print()
    print("HONEST FINDING")
    print("==============")
    print("The (R1b) sector-fundamental rule is NOT closeable via Gram structure.")
    print("Closing it cascade-natively requires a DIFFERENT cascade theorem:")
    print()
    print("  'For matter in V_12 otimes V_13 otimes V_14 with V_14 = 1-dim, the")
    print("   U(1)_Y action's smallest non-trivial Y is 1 / (dim V_12 * dim V_13)'")
    print()
    print("This is REPRESENTATION-THEORETIC, derived from cascade primitives")
    print("(Adams + SU(2)/SU(3) structure + path-tensor Hilbert normalization)")
    print("but at a structural level distinct from Gram corrections.")
    print()
    print("WHAT THIS DIG EARNS")
    print("===================")
    print("- Rules out Gram structure as the (R1b) closure mechanism.")
    print("- Identifies the correct cascade-internal source: representation-")
    print("  theoretic dimension normalization on path-tensor.")
    print("- Sharpens what's needed: a cascade theorem on path-tensor Hilbert")
    print("  space normalization under U(1)_Y action.")
    print()
    print("THE NEXT STEP")
    print("=============")
    print("Attempt the representation-theoretic derivation: show that the")
    print("U(1)_Y action exp(i Y theta) on the path-tensor V_12 otimes V_13")
    print("otimes V_14 is consistent ONLY if Y is integer multiple of")
    print("1/(dim V_12 * dim V_13) in cascade-native units, by some")
    print("normalization argument on the cascade Hilbert space.")
    print()


def main():
    print("=" * 78)
    print("(R1b) attack via Gram structure: cascade-native sector-fundamental")
    print("=" * 78)
    print()
    report_gram_correlations()
    test_sector_fundamental_units()
    test_path_tensor_gram_product()
    report_structural_reading()
    report_status()
    return 0


if __name__ == "__main__":
    sys.exit(main())
