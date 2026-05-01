#!/usr/bin/env python3
"""
Multiplicity matching at d=13: precise comparison of cascade Route (i)
matter content at d=12 vs SM color-charged matter content per 3 gens.

CONTEXT
=======
The morning planning recap framed the gap as 'cascade Route (i):
14+14 vs SM's 12+21 across 3 gens.'  That framing was INACCURATE:

  - The 14+14 in rem:single-h-factor's table is the FULL Spin(12)
    Dirac singlet/doublet count, including n_S = 2 singlets and
    n_S = 3 doublets that ARE EXCLUDED by single-H-factor (n_S
    in {0, 1}).
  - The actual Route (i) count is 8 singlets + 12 doublets (n_S
    in {0, 1} only), per PR #109's verifier
    cascade_rep_selection_gap1.py.

This script:
  1. Restates the cascade Route (i) count precisely.
  2. Computes SM color-charged matter per 3 generations precisely.
  3. Identifies the actual mismatch.
  4. Audits cascade-internal candidate explanations.
  5. Honest assessment: defect, structural mechanism, or category
     error?

PRECISE COUNTS
==============

Cascade Route (i) at d=12 Spin(12) Dirac under SU(2)_R, restricted
to single-H-factor (n_S in {0, 1}):

  n_S = 0 (WWW combination):     8 singlets
  n_S = 1 (WWS-type, 3 combos): 12 doublets (4 doublets × 3 combos)
  -----------------------------------------
  Total:                          20 multiplets
  Total components:               8 + 24 = 32

SM color-charged matter per 3 generations (LH Weyl convention):
  3 Q_L (one per gen):            3 doublets × (3 colors × 2 isospin) = 18 components
  3 u_L^c (one per gen):          3 singlets × (3 colors × 1) = 9 components
  3 d_L^c:                        3 singlets × 3 = 9 components
  -----------------------------------------
  Total per 3 gens:               36 LH Weyl components

ACTUAL MISMATCH
===============
  Cascade Route (i): 32 components (20 multiplets: 8 singlets + 12 doublets)
  SM 3-gen quarks:   36 components (9 multiplets: 3 doublets + 6 singlets,
                                    with implicit color triplet structure
                                    making 9 doublet states + 18 singlet
                                    states = 27 color-multiplet states)

Component count: cascade 32 vs SM 36 (cascade SHORT by 4).
'Multiplet' count: depends on convention.

WHAT THIS SCRIPT DELIVERS
=========================
Precise audit of the multiplicity-matching gap.  This is the most
concrete attack on Option (1) (the standing largest unaddressed gap).
Outcome: either a structural mechanism that resolves the mismatch,
identification of a real cascade defect, or a clarifying category-
error finding.
"""

from __future__ import annotations

import sys


def report_cascade_count():
    print("=" * 78)
    print("CASCADE ROUTE (i) at d=12 Spin(12) Dirac, single-H-factor restriction")
    print("=" * 78)
    print()
    print("Spin(12) Dirac built as Spin(4)^⊗3 on H^3 = R^12, dim 64 complex.")
    print("Each Spin(4) factor's Dirac splits into Weyl_+ (W) and Weyl_- (S).")
    print("Diagonal SU(2)_R sees W as singlet (with 2-fold SU(2)_L mult), S as")
    print("doublet (single).")
    print()
    print("Combinations by n_S = count of S factors:")
    print()
    print(f"  {'n_S':>4s}  {'combos':>10s}  {'singlets':>10s}  {'doublets':>10s}  "
          f"{'triplets':>10s}  {'quartet':>10s}  {'components':>12s}")

    table = [
        (0, ["WWW"], 8, 0, 0, 0, 8),
        (1, ["WWS", "WSW", "SWW"], 0, 12, 0, 0, 24),
        (2, ["WSS", "SWS", "SSW"], 6, 0, 6, 0, 24),
        (3, ["SSS"], 0, 2, 0, 1, 8),
    ]
    total_comp = 0
    route_i_singlets = 0
    route_i_doublets = 0
    for n_S, combos, sng, dbl, trp, quart, comp in table:
        total_comp += comp
        if n_S in (0, 1):
            route_i_singlets += sng
            route_i_doublets += dbl
        print(f"  {n_S:>4d}  {len(combos):>10d}  {sng:>10d}  {dbl:>10d}  "
              f"{trp:>10d}  {quart:>10d}  {comp:>12d}")
    print(f"  {'Total':>4s}  {' ':>10s}  {sum(t[2] for t in table):>10d}  "
          f"{sum(t[3] for t in table):>10d}  {sum(t[4] for t in table):>10d}  "
          f"{sum(t[5] for t in table):>10d}  {total_comp:>12d}")
    print()

    print("Single-H-factor restriction (n_S in {0, 1}) keeps only n_S = 0, 1:")
    print(f"  Route (i) singlets: {route_i_singlets}")
    print(f"  Route (i) doublets: {route_i_doublets}")
    print(f"  Route (i) multiplets: {route_i_singlets + route_i_doublets}")
    route_i_components = route_i_singlets + 2 * route_i_doublets
    print(f"  Route (i) components: {route_i_singlets} + {2 * route_i_doublets} "
          f"= {route_i_components}")
    print()
    return route_i_singlets, route_i_doublets, route_i_components


def report_sm_count():
    print("=" * 78)
    print("SM color-charged matter per 3 generations")
    print("=" * 78)
    print()
    print("LH Weyl convention (matter + CPT-image antimatter both as LH Weyl).")
    print()

    sm_quarks = [
        # (name, multiplets_per_gen, color_dim, isospin_dim)
        ("Q_L",   1, 3, 2),
        ("u_L^c", 1, 3, 1),  # CPT image of u_R
        ("d_L^c", 1, 3, 1),
    ]
    n_gens = 3

    print(f"  {'particle':>10s}  {'mult/gen':>10s}  {'color':>6s}  "
          f"{'isospin':>8s}  {'components/gen':>16s}")
    total_per_gen = 0
    for name, mult, c, t in sm_quarks:
        comp = mult * c * t
        total_per_gen += comp
        print(f"  {name:>10s}  {mult:>10d}  {c:>6d}  {t:>8d}  {comp:>16d}")
    total_3gen = total_per_gen * n_gens
    print(f"  {'Total/gen':>10s}  {' ':>10s}  {' ':>6s}  {' ':>8s}  {total_per_gen:>16d}")
    print(f"  {'Total/3gen':>10s}  {' ':>10s}  {' ':>6s}  {' ':>8s}  {total_3gen:>16d}")
    print()

    # Multiplet counts at different granularities
    print("SM multiplet counts at different granularities:")
    print(f"  Per (gen, particle-type): {len(sm_quarks)} types/gen × {n_gens} gens "
          f"= {len(sm_quarks) * n_gens} multiplets")
    print(f"  Per (gen, particle-type, color): "
          f"{sum(c for _, _, c, _ in sm_quarks)} × {n_gens} = "
          f"{sum(c for _, _, c, _ in sm_quarks) * n_gens} states")
    print()

    sm_doublets = sum(mult * c for name, mult, c, t in sm_quarks if t == 2)
    sm_singlets = sum(mult * c for name, mult, c, t in sm_quarks if t == 1)
    sm_doublets_3gen = sm_doublets * n_gens
    sm_singlets_3gen = sm_singlets * n_gens
    print(f"  Doublet states per gen: {sm_doublets}, per 3 gens: {sm_doublets_3gen}")
    print(f"  Singlet states per gen: {sm_singlets}, per 3 gens: {sm_singlets_3gen}")
    print()
    return total_3gen, sm_doublets_3gen, sm_singlets_3gen


def report_mismatch(cascade_sng, cascade_dbl, cascade_comp,
                    sm_comp, sm_dbl_states, sm_sng_states):
    print("=" * 78)
    print("THE MISMATCH")
    print("=" * 78)
    print()
    print(f"COMPONENTS:")
    print(f"  Cascade Route (i): {cascade_comp}")
    print(f"  SM 3-gen quarks:   {sm_comp}")
    print(f"  Difference:        SM - cascade = {sm_comp - cascade_comp}")
    print()
    print(f"DOUBLET STATES (counting per color):")
    print(f"  Cascade Route (i): {cascade_dbl}")
    print(f"  SM 3-gen quarks:   {sm_dbl_states}")
    print(f"  Difference:        cascade - SM = {cascade_dbl - sm_dbl_states}")
    print()
    print(f"SINGLET STATES (counting per color):")
    print(f"  Cascade Route (i): {cascade_sng}")
    print(f"  SM 3-gen quarks:   {sm_sng_states}")
    print(f"  Difference:        cascade - SM = {cascade_sng - sm_sng_states}")
    print()
    print("Component count: cascade SHORT by 4 (32 vs 36).")
    print("Doublet states: cascade EXCESS of 3 (12 vs 9).")
    print("Singlet states: cascade SHORTAGE of 10 (8 vs 18).")
    print()
    print(f"  Net components:  cascade 12*2 + 8*1 = {12*2 + 8*1} = 32")
    print(f"  Net components:  SM 9*2 + 18*1 = {9*2 + 18*1} = 36")
    print(f"  Difference: 4 = (12-9)*2 + (8-18)*1 = 6 - 10 = -4 components shortage")
    print()


def audit_explanations():
    print("=" * 78)
    print("CANDIDATE CASCADE-INTERNAL EXPLANATIONS")
    print("=" * 78)
    print()
    print("Three structural readings of the cascade-vs-SM mismatch:")
    print()
    print("CANDIDATE A: Per-generation Spin(12) Dirac instances.")
    print("  IF the cascade has THREE separate Spin(12) Dirac instances")
    print("  (one per generation at d=5, d=13, d=21), each providing 32")
    print("  Route (i) components, total = 96 components.  SM is 36.")
    print("  RATIO: cascade 96 / SM 36 = 8/3 ≈ 2.67.  Cascade EXCESS.")
    print("  Status: doesn't match.  Also contradicts cascade structure")
    print("  (d=12 is one shared layer, not per-gen).")
    print()
    print("CANDIDATE B: Single Spin(12) Dirac for all generations combined.")
    print("  Cascade Route (i) at d=12 provides 32 components SHARED across")
    print("  3 generations.  SM 3-gen quarks = 36 components.")
    print("  RATIO: cascade 32 / SM 36 = 8/9.  Cascade SHORTAGE of 4.")
    print("  Status: closest match but off by 4 components.")
    print()
    print("CANDIDATE C: Cascade Route (i) is per-generation, scaled to 3 gens.")
    print("  IF cascade Route (i) gives 32 components per generation,")
    print("  3 gens × 32 = 96 cascade components.  SM 3-gen = 36.")
    print("  RATIO: cascade 96 / SM 36 = 8/3.  Cascade EXCESS of 60.")
    print("  Status: large mismatch.  Same as Candidate A.")
    print()
    print("STRUCTURAL CONSISTENCY CHECK")
    print("============================")
    print("Per rem:path-tensor, the cascade has 15 LH Weyl per generation.")
    print("Per 3 gens: 45 LH Weyl, matching SM 45 LH Weyl per 3 gens.")
    print()
    print("Color-charged subset of 15 Weyl/gen:")
    print("  Q_L: 6 + u_L^c: 3 + d_L^c: 3 = 12 components (color-charged)")
    print("  L_L: 2 + e_L^c: 1 = 3 components (color-singlet)")
    print()
    print("Per 3 gens:")
    print("  Color-charged: 12 × 3 = 36 components")
    print("  Color-singlet: 3 × 3 = 9 components")
    print("  Total: 45 ✓ (matches rem:path-tensor)")
    print()
    print("SM AGREES with rem:path-tensor's 45 LH Weyl per 3 gens.")
    print()
    print("The 32 vs 36 mismatch is in the COLOR-CHARGED subset specifically.")
    print("rem:path-tensor's 45 includes leptons; the cascade Spin(12) Dirac")
    print("Route (i) sector is QUARKS ONLY.")
    print()


def report_assessment():
    print("=" * 78)
    print("ASSESSMENT (after direct source reading)")
    print("=" * 78)
    print()
    print("VERIFIED via direct reading of Part IVa rem:single-h-factor")
    print("(line 1014-1037) + rem:path-tensor (line 855-873):")
    print()
    print("  rem:path-tensor: matter content is V_{12} otimes V_{13} otimes V_{14}")
    print("  per particle, and the verifier")
    print("  tools/verifiers/cascade_path_tensor_product.py confirms 15 Weyl/gen")
    print("  exactly, matching SM.")
    print()
    print("  rem:single-h-factor Route (i): the Spin(12) Dirac decomposition")
    print("  is used to PROVE that V_{13} in {1, 2} for color-charged matter")
    print("  (excluding triplet/quartet via single-H-factor restriction).")
    print("  It is a STRUCTURAL CONSTRAINT on V_{13}, not a count of matter.")
    print()
    print("  rem:single-h-factor Route (ii): for color-singlet matter, the")
    print("  Spin(12) Dirac analysis 'does not directly govern its SU(2) rep'")
    print("  (line 1016-1017).")
    print()
    print("CONCLUSION: 'multiplicity matching at d=13' was a CATEGORY ERROR")
    print("============================================================")
    print("The Spin(12) Dirac decomposition at d=12 is a STRUCTURAL TOOL")
    print("for constraining V_{13} representations of color-charged matter")
    print("(showing V_{13} in {1, 2} via single-H-factor restriction).")
    print("It is NOT a counting structure for SM matter content.")
    print()
    print("The actual cascade matter count is per rem:path-tensor:")
    print("  15 LH Weyl per generation x 3 generations = 45 components")
    print("  matching SM 45 LH Weyl per 3 generations EXACTLY.")
    print()
    print("The earlier framing of '14+14 cascade vs 12+21 SM' or '32 vs 36")
    print("components' was comparing two unrelated counts:")
    print("  - Spin(12) Dirac multiplet count: structural Dirac decomposition")
    print("    by SU(2)_R rep, used to PROVE V_{13} in {1, 2}.")
    print("  - SM matter content: per-particle count via path-tensor structure.")
    print()
    print("THE GAP DOES NOT EXIST AS A QUANTITATIVE MULTIPLICITY MISMATCH.")
    print()
    print("WHAT THIS DIG EARNS")
    print("===================")
    print("- Identifies the 'multiplicity matching at d=13' gap as a category")
    print("  error in the prior framing.  No actual quantitative mismatch.")
    print("- Removes one item from the standing-open list in CLAUDE.md and")
    print("  Part IVa rem:observer-identification.")
    print("- Sharpens what the Spin(12) Dirac decomposition actually does")
    print("  (constrains V_{13} for color-charged matter via single-H-factor)")
    print("  versus what counts matter content (path-tensor V_{12} otimes V_{13}")
    print("  otimes V_{14}, 15 Weyl/gen).")
    print()
    print("WHAT THIS DIG DOES NOT DO")
    print("==========================")
    print("- Add new cascade theorems.")
    print("- Address the OTHER standing open pieces ((R1b) sector-fundamental")
    print("  uniqueness, cosmological residuals).")
    print()
    print("ACTION: update CLAUDE.md and Part IVa rem:observer-identification")
    print("to remove 'multiplicity matching at d=13' from the standing-open")
    print("list.  Replace with explicit note that the gap was a category")
    print("error; cascade matches SM at 15 Weyl/gen via rem:path-tensor.")
    print()


def main() -> int:
    print("=" * 78)
    print("MULTIPLICITY MATCHING AT d=13: precise audit of the cascade vs SM gap")
    print("=" * 78)
    print()
    cs, cd, cc = report_cascade_count()
    sc, sds, sss = report_sm_count()
    report_mismatch(cs, cd, cc, sc, sds, sss)
    audit_explanations()
    report_assessment()
    return 0


if __name__ == "__main__":
    sys.exit(main())
