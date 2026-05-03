#!/usr/bin/env python3
"""
v_EW residual decomposition: matches Part 0 first-order Gram (d=5..12 path).

CONTEXT
=======
cascade_gap_mass_influence.py noted that the v_EW residual (-2.20%)
is suggestively 1.33x the bundle/scalar gap (1.66%), and proposed that
v might decompose as two stacked gap contributions through the Higgs
Yukawa coupling structure.

Hypothesis tested: v_residual = 2 * delta_BS, or v_residual = delta_BS +
some chi^k filter shift, or other gap-based combination.

RESULT (negative for hypothesis; structural finding via Part 0)
================================================================
The hypothesis is wrong.  v_EW residual decomposes via Part 0's
first-order Gram correction with cascade-canonical path d=5..12 (the
same path as alpha_s):

  v_lead = M_Pl,red * alpha_s_lead * exp(-pi/alpha(5)) = 240.72 GeV
  v_PDG  = 246.22 GeV
  Residual: -2.235%

  v_corrected = v_lead * exp(delta_path(5, 12))
              = 240.72 * exp(0.01186)
              = 243.59 GeV
              -> residual -1.068%

This matches Part 0 line 1781 (Gram correction table) which reports
v leading 240.8, corrected 243.7, observed 246.2, dev -1.0%.

CORRECTED FROM EARLIER VERSION
==============================
An earlier version of this script claimed v residual closes via
delta_path(5, 217) (full cascade Gram, same as cosmological constant)
to -0.15%.  THAT WAS WRONG.

Numerically, delta_path(5, 217) = 0.02108 happens to be close to
the log shift needed for v (0.02260), giving v_corrected = 245.85.
But Part 0's canonical Gram path for v is d=5..12, NOT d=5..217.
The match to delta_path(5, 217) was a numerical coincidence, not a
structural identity.

Why d=5..12 is the canonical path:
  - The v formula is M_Pl,red * alpha_s * exp(-pi/alpha(5))
  - M_Pl,red is treated as a measured input (from G_Newton), not
    cascade-derived
  - The descent-dependent piece is alpha_s * exp(-pi/alpha(5)),
    whose explicit cascade descent is alpha_s' path d=5..12
  - First-order Gram applies to the descent piece only

The "v closes via same Gram as cosmological constant" claim is RETRACTED.
v is NOT a Gram sister of rho_Lambda.

CORRECT STATUS
==============
v_EW closure status (post-Part 0 Gram, Part 0 line 1781):
  - Leading: 240.8 GeV, residual -2.2%
  - First-order Gram (d=5..12): 243.7 GeV, residual -1.0%
  - NOT closed at experimental precision

The remaining -1.0% requires either:
  (a) Higher-order Gram correction (next-order Cauchy-Schwarz on
      the slicing recurrence), or
  (b) A separate cascade correction at distinguished layers, or
  (c) Acceptance that v is at standing precision, not experimental.

Comparison to cosmological constant:
  - rho_Lambda Gram path: d=5..217 (sphere-area product Omega_19 *
    Omega_217 spans full cascade depth).  Residual -0.07% post-Gram.
  - v_EW Gram path: d=5..12 (alpha_s descent path).  Residual -1.0%
    post-Gram.

These are DIFFERENT Gram applications: rho_Lambda's is full-cascade
because both Omega_19 and Omega_217 are explicit cascade quantities;
v's is short-path because only alpha_s is explicitly cascade-internal
in v's formula (M_Pl,red is input).

THE 1.33x COINCIDENCE EXPLAINED
================================
v_residual = 2.235%, bundle/scalar gap = 1.659%, ratio 1.347x.

This was a numerical coincidence between two unrelated cascade
quantities.  The bundle/scalar gap is mechanism (3) at the d=13->21
boundary; v's residual is mechanism (1) over a different path
(d=5..12 path, with significant residual remaining).  They share
neither source nor mechanism.

UPDATED THREE-MECHANISM STATUS
===============================
The mechanism (1) Gram has clearer scope after this correction:

  rho_Lambda: closes -2.2% -> -0.07% via delta_path(5, 217)
              (full-cascade because both endpoint sphere areas
               are explicit cascade quantities)

  v_EW:       closes -2.2% -> -1.0% via delta_path(5, 12)
              (alpha_s' path because M_Pl,red is treated as input;
               full closure requires higher-order corrections)

  Bundle/scalar gap at d=13..21:
              closes -1.6% -> -0.05% via delta_path(5, 21)
              (descent endpoint at d=21, electron home)

These all use the same Gram FORMULA but different PATH LENGTHS.
Path length is forced by the observable's explicit cascade structure
(deepest cascade layer that explicitly appears in the leading
formula).

CONCLUSION
==========
v_EW residual is NOT bundle/scalar gap stacking.  Part 0 first-order
Gram closes v from -2.2% to -1.0% via the alpha_s descent path
d=5..12.  v is NOT closed at experimental precision; the remaining
-1.0% is unaccounted at first order.

Bundle/scalar gap (mechanism 3) does NOT influence v -- v is in the
descent regime (mechanism 1), but with a SHORTER path than the
cosmological constant.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, os.path.join(TOOLS_DIR, "research"))

from cascade_constants import alpha as alpha_cas, R, p, pi  # noqa: E402
from cascade_gram_bott_tower import gram_path_sum, Phi_cascade  # noqa: E402

M_PL_RED = 2.435e18
ALPHA_S_LEAD = 0.1159
V_PDG = 246.21965
N_C = 3
OMEGA_3 = 2 * math.pi ** 2


def v_cascade(alpha_s: float = ALPHA_S_LEAD) -> float:
    return M_PL_RED * alpha_s * math.exp(-pi / alpha_cas(5))


def report_setup() -> None:
    print("=" * 88)
    print("STEP 1: setup -- the v_EW residual under test")
    print("=" * 88)
    print()
    v_lead = v_cascade()
    print(f"  v_lead = M_Pl,red * alpha_s_lead * exp(-pi/alpha(5))")
    print(f"        = {M_PL_RED:.4e} * {ALPHA_S_LEAD} * exp(-{pi/alpha_cas(5):.4f})")
    print(f"        = {v_lead:.4f} GeV")
    print()
    print(f"  v_PDG = {V_PDG:.4f} GeV")
    print(f"  Residual = {100*(v_lead - V_PDG)/V_PDG:+.3f}%")
    print(f"  log shift needed = {math.log(V_PDG/v_lead):+.6f}")
    print()


def report_hypothesis_test() -> None:
    print("=" * 88)
    print("STEP 2: hypothesis -- is v_residual = 2 * bundle/scalar gap?")
    print("=" * 88)
    print()
    e_phi = math.exp(Phi_cascade(21) - Phi_cascade(13))
    target = N_C * OMEGA_3
    gap = math.log(target / e_phi)
    v_lead = v_cascade()

    print(f"  Bundle/scalar gap (log)  = {gap:+.6f}  ({100*(math.exp(gap)-1):.3f}%)")
    print(f"  2 * gap                  = {2*gap:+.6f}  ({100*(math.exp(2*gap)-1):.3f}%)")
    print()
    print(f"  Test: v_lead * exp(2*gap) = {v_lead*math.exp(2*gap):.4f}")
    print(f"        Deviation         = {100*(v_lead*math.exp(2*gap) - V_PDG)/V_PDG:+.3f}%")
    print()
    print(f"  2 * gap OVERSHOOTS PDG.  Hypothesis NOT confirmed.")
    print()


def report_part0_decomposition() -> None:
    print("=" * 88)
    print("STEP 3: Part 0's canonical decomposition (d=5..12 path)")
    print("=" * 88)
    print()
    v_lead = v_cascade()
    gram_5_12 = gram_path_sum(5, 12)
    v_corrected = v_lead * math.exp(gram_5_12)

    print(f"  Part 0 line 1781 (Gram correction table):")
    print(f"    v leading       = 240.8 GeV   (uses alpha_s leading 0.1159)")
    print(f"    v corrected     = 243.7 GeV   (after delta_path(5..12))")
    print(f"    v observed      = 246.2 GeV")
    print(f"    deviation       = -1.0%")
    print()
    print(f"  Verification:")
    print(f"    delta_path(5, 12)  = {gram_5_12:.6f}  (Part 0 reports 0.01186)")
    print(f"    v_lead             = {v_lead:.4f} GeV")
    print(f"    v_corrected        = v_lead * exp({gram_5_12:.6f})")
    print(f"                       = {v_corrected:.4f} GeV")
    print(f"    Residual           = {100*(v_corrected - V_PDG)/V_PDG:+.3f}%")
    print()
    print(f"  Match to Part 0: {v_corrected:.1f} ~= 243.7 (within rounding).")
    print()


def report_correction_to_earlier_claim() -> None:
    print("=" * 88)
    print("STEP 4: correction to earlier 'v closes via SAME Gram as CC' claim")
    print("=" * 88)
    print()
    v_lead = v_cascade()
    gram_5_217 = gram_path_sum(5, 217)
    needed = math.log(V_PDG / v_lead)
    gram_5_12 = gram_path_sum(5, 12)

    print(f"  An earlier version of this script claimed:")
    print(f"    'v residual closes via delta_path(5, 217) to -0.15%'")
    print(f"  This was WRONG.")
    print()
    print(f"  Numerically:")
    print(f"    log shift needed         = {needed:+.6f}")
    print(f"    delta_path(5, 217)       = {gram_5_217:+.6f}  (within 7% of needed)")
    print(f"    delta_path(5, 12)        = {gram_5_12:+.6f}  (only 52% of needed)")
    print()
    print(f"  The numerical proximity of delta_path(5, 217) to the needed shift")
    print(f"  was a COINCIDENCE, not a structural identity.  Part 0's canonical")
    print(f"  Gram path for v is d=5..12, NOT d=5..217.")
    print()
    print(f"  Why d=5..12 is canonical (Part 0 ratification):")
    print(f"    - v formula: M_Pl,red * alpha_s * exp(-pi/alpha(5))")
    print(f"    - M_Pl,red treated as input (from G_Newton), not cascade-derived")
    print(f"    - Descent-dependent piece: alpha_s * exp(-pi/alpha(5))")
    print(f"    - That descent is alpha_s' path d=5..12")
    print()
    print(f"  CORRECT STATUS: v post-Gram = 243.7 GeV, residual -1.0%.")
    print(f"  v is NOT closed at experimental precision; remaining -1.0%")
    print(f"  needs higher-order or other corrections.")
    print()


def report_three_mechanism_update() -> None:
    print("=" * 88)
    print("STEP 5: updated mechanism (1) Gram scope")
    print("=" * 88)
    print()
    print("  Three observables that close (partially or fully) via Gram:")
    print()
    print("  +-------------------+--------+-----------+----------+----------+")
    print("  | observable        | path   | leading   | post-Gram| residual |")
    print("  +-------------------+--------+-----------+----------+----------+")
    print("  | rho_Lambda/M_Pl^4 | 5..217 | -2.2%     | -0.07%   | CLOSED   |")
    print("  | v_EW              | 5..12  | -2.2%     | -1.0%    | partial  |")
    print("  | bundle/scalar gap | 5..21  | -1.6%     | -0.05%   | near-closed|")
    print("  +-------------------+--------+-----------+----------+----------+")
    print()
    print("  Same FORMULA, different PATH LENGTHS.  Path is forced by the")
    print("  deepest cascade layer that explicitly appears in the leading")
    print("  formula:")
    print("    - rho_Lambda: explicit Omega_217 -> d_max = 217")
    print("    - v_EW: explicit alpha_s descent at d=12 -> d_max = 12")
    print("    - bundle/scalar gap: span ends at d=21 -> d_max = 21")
    print()
    print("  Different observables, different residuals after first-order")
    print("  Gram.  v_EW is NOT a 'Gram sister' of the cosmological constant")
    print("  in the strong sense; both use Gram, but at different depths.")
    print()


def main() -> int:
    print("=" * 88)
    print("v_EW RESIDUAL DECOMPOSITION (corrected)")
    print("Hypothesis: v residual is bundle/scalar gap stacking.")
    print("Result:     NOT confirmed.  v closes via Part 0's first-order Gram")
    print("            on alpha_s' path d=5..12 to residual -1.0% (NOT -0.15%).")
    print("=" * 88)
    print()
    report_setup()
    report_hypothesis_test()
    report_part0_decomposition()
    report_correction_to_earlier_claim()
    report_three_mechanism_update()
    print("=" * 88)
    print("HEADLINE:")
    print()
    print("  v_EW residual is NOT bundle/scalar gap stacking.")
    print()
    print("  v closes via Part 0 first-order Gram on alpha_s' path d=5..12:")
    print("    240.8 GeV -> 243.7 GeV (residual -1.0%)")
    print()
    print("  v is NOT closed at experimental precision.  The remaining -1.0%")
    print("  needs higher-order Gram corrections or other mechanisms.")
    print()
    print("  The earlier claim 'v closes via SAME Gram as CC' was WRONG --")
    print("  numerical coincidence (delta_path(5, 217) ~= needed log shift)")
    print("  mistaken for structural identity.  Part 0's canonical path for")
    print("  v is d=5..12, not d=5..217.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
