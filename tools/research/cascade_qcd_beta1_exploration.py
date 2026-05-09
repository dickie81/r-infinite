#!/usr/bin/env python3
"""Cascade-primitive exploration of QCD β_1 (2-loop coefficient).

Standard QCD β_1 (MS-bar scheme):
    β_1 = (34/3)·N_c² - (10/3)·N_c·n_f - 2·C_F·n_f
        = (34/3)·N_c² - [(10/3)·N_c + (N_c²-1)/N_c]·n_f
        = 102 - (38/3)·n_f       for SU(3) with n_f flavors

For n_f = 6: β_1 = 102 - 76 = 26.

Following the success of β_0 cascade-primitive identification
(rem:cascade-beta0, this PR), we test structural forms for β_1's
coefficients using cascade primitives:
  - N_c = 3 (Adams' theorem)
  - N(0) = χ = 2 (Cor:2sqrtpi-primitive)
  - β_0 gauge factor (N_c² + N_c - 1) = 11

For β_1's gauge coefficient "34/3" (or "102" for SU(3)):

  Candidate 1: 102 = (β_0 gauge)·N_c² + N_c
                   = (N_c²+N_c-1)·N_c² + N_c
                   = 11·9 + 3 = 99 + 3 = 102 ✓ (SU(3))

  Candidate 2: 102 = N_c⁴ + N_c³ - N_c² + N_c
                   = 81 + 27 - 9 + 3 = 102 ✓ (SU(3))

  Candidate 3: 102 = (N_c² + 1)·N_c² + 3·N_c
                   = 10·9 + 9 = 99 + 3 = 102 ✓
                   Hmm same as candidate 1 with different decomposition

For β_1's per-fermion coefficient "38/3":

  Candidate A: 38/3 = (10/3)·N_c + (N_c²-1)/N_c
                    = (gauge mixing) + (Casimir)
                    = (10/3)·3 + 8/3 = 10 + 8/3 = 38/3 ✓ (SU(3))
              The "10" in (10/3)·N_c at N_c=3:
                10 = N_c² + 1 = N_c² + (N(0) - 1) = 10 ✓
                (or: 10 = N_c² + 1 with "1" as raw integer)
              The "(N_c²-1)/N_c" = (gluon count)/(color count):
                cascade-primitive, generalizes for SU(N)

  Candidate B: 38/3 = (β_0 gauge - N_c² + 1)/N_c·N_c + N_c²...
              Doesn't yield clean form

This tool computes both candidates, verifies numerical match, and
reports honest cascade-primitive status for β_1. Empirical match is
exact across flavor windows; the structural derivation interpretation
is what's being tested.
"""

from __future__ import annotations

import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
sys.path.insert(0, TOOLS_DIR)

# Cascade primitives
N_C = 3
N_0 = 2


def standard_beta1(n_c: int, n_f: int) -> float:
    """Standard QCD β_1 in MS-bar scheme.

    β_1 = (34/3)·N_c² - (10/3)·N_c·n_f - 2·C_F·n_f
        where C_F = (N_c²-1)/(2·N_c)
    """
    c_f = (n_c**2 - 1) / (2 * n_c)
    return (34/3) * n_c**2 - (10/3) * n_c * n_f - 2 * c_f * n_f


def cascade_beta1_candidate_1(n_c: int, n_0: int, n_f: int) -> float:
    """Cascade reading: β_1 = (β_0 gauge)·N_c² + N_c - per-fermion·n_f.

    Per-fermion = (gauge mixing) + (Casimir) = (10/3)·N_c + (N_c²-1)/N_c
                = (N_c² + 1) + (N_c²-1)/N_c·1   [for the gauge mixing part: 10/3·N_c = N_c²+1 for N_c=3]

    For SU(3): per-fermion = 10 + 8/3 = 38/3 ✓
    """
    gauge = (n_c**2 + n_c - 1) * n_c**2 + n_c  # = 102 for N_c=3
    # Per fermion: (N_c²+1) + (N_c²-1)/N_c
    per_fermion = (n_c**2 + 1) + (n_c**2 - 1) / n_c
    return gauge - per_fermion * n_f


def cascade_beta1_candidate_2(n_c: int, n_0: int, n_f: int) -> float:
    """Alternative gauge form: β_1 = N_c⁴ + N_c³ - N_c² + N_c - per-fermion·n_f."""
    gauge = n_c**4 + n_c**3 - n_c**2 + n_c  # also = 102 for N_c=3
    per_fermion = (n_c**2 + 1) + (n_c**2 - 1) / n_c
    return gauge - per_fermion * n_f


def main() -> None:
    print("=" * 96)
    print("CASCADE-PRIMITIVE EXPLORATION OF QCD β_1 (2-LOOP COEFFICIENT)")
    print("=" * 96)
    print()
    print("Standard QCD β_1 = (34/3)·N_c² - (10/3)·N_c·n_f - 2·C_F·n_f")
    print(f"For SU(3): β_1 = 102 - (38/3)·n_f")
    print()
    print(f"Cascade primitives: N_c = {N_C} (Adams), N(0) = {N_0} (Cor:2sqrtpi)")
    print()

    print("=" * 96)
    print("Cascade-primitive candidate forms for β_1's coefficients:")
    print("=" * 96)
    print()
    print("GAUGE COEFFICIENT '102':")
    print(f"  Candidate 1: (β_0 gauge)·N_c² + N_c = (N_c²+N_c-1)·N_c² + N_c")
    print(f"               = {(N_C**2+N_C-1)}·{N_C**2} + {N_C}")
    print(f"               = {(N_C**2+N_C-1)*N_C**2} + {N_C} = {(N_C**2+N_C-1)*N_C**2 + N_C}")
    print()
    print(f"  Candidate 2: N_c⁴ + N_c³ - N_c² + N_c")
    print(f"               = {N_C**4} + {N_C**3} - {N_C**2} + {N_C} = {N_C**4 + N_C**3 - N_C**2 + N_C}")
    print()

    print("PER-FERMION COEFFICIENT '38/3':")
    print(f"  (10/3)·N_c + (N_c²-1)/N_c   [gauge-mixing + Casimir]")
    print(f"  = {(10/3)*N_C} + {(N_C**2-1)/N_C}")
    print(f"  = {(10/3)*N_C + (N_C**2-1)/N_C}")
    print()
    print(f"  Cascade form:")
    print(f"    (10/3)·N_c at N_c=3:  10 = N_c² + 1 = {N_C**2 + 1}, so (10/3)·N_c = (N_c²+1)·N_c/N_c·... ")
    print(f"                          Cleaner: 10 = N_c² + 1 (uses N_c only, '+1' as integer)")
    print(f"                          OR: 10 = N_c² + N(0) - N(0)·χ/2... [hand-wavy]")
    print(f"    (N_c²-1)/N_c = (gluon count)/(color count) = {(N_C**2-1)/N_C}")
    print(f"                  cascade-native: 2·C_F where C_F = (N_c²-1)/(2N_c)")
    print()

    print("=" * 96)
    print("Numerical verification across flavor windows:")
    print("=" * 96)
    print()
    print(f"{'n_f':>4}  {'cascade β_1 (cand 1)':>22}  {'cascade β_1 (cand 2)':>22}  "
          f"{'standard β_1':>14}  {'match':>10}")
    print("-" * 96)

    for n_f in [3, 4, 5, 6]:
        c1 = cascade_beta1_candidate_1(N_C, N_0, n_f)
        c2 = cascade_beta1_candidate_2(N_C, N_0, n_f)
        std = standard_beta1(N_C, n_f)
        match_1 = abs(c1 - std) < 1e-9
        match_2 = abs(c2 - std) < 1e-9
        match = "BOTH" if (match_1 and match_2) else ("MISMATCH" if not (match_1 or match_2) else "1ONLY" if match_1 else "2ONLY")
        print(f"  {n_f:>2}   {c1:>22.4f}  {c2:>22.4f}  {std:>14.4f}  {match:>10}")
    print()

    print("=" * 96)
    print("STRUCTURAL READING")
    print("=" * 96)
    print()
    print("Cascade-primitive identification of β_1's coefficients SUCCEEDS for SU(3):")
    print()
    print("  Gauge coefficient 102:")
    print("    - Candidate 1: (β_0 gauge factor)·N_c² + N_c")
    print("    - Both decompositions use cascade primitives N_c (Adams)")
    print("    - Structural reading: β_0 gauge factor (N_c²+N_c-1) raised by")
    print("      N_c² (a 2-loop multiplicative factor), plus N_c (color count)")
    print()
    print("  Per-fermion coefficient 38/3:")
    print("    - Two-piece structure: gauge-mixing (10/3)·N_c + Casimir 2·C_F")
    print("    - Casimir piece (N_c²-1)/N_c is cascade-native (gluon/color)")
    print("    - Gauge-mixing piece (10/3)·N_c uses '10 = N_c²+1' for SU(3)")
    print()
    print("Numerical match: cascade β_1 = standard β_1 EXACTLY for SU(3)")
    print("across flavor windows (n_f = 3, 4, 5, 6).")
    print()
    print("Cascade primitives suffice to reproduce standard QCD β_1 numerically.")
    print()
    print("=" * 96)
    print("HONEST STRUCTURAL VERDICT")
    print("=" * 96)
    print()
    print("Cascade β_1 is at Tier 3 (cascade-primitive identification at")
    print("empirical-match precision), NOT Tier 2 (full structural derivation).")
    print()
    print("WHY: β_1's gauge coefficient '102' admits multiple cascade-primitive")
    print("decompositions:")
    print("  - (N_c²+N_c-1)·N_c² + N_c (Candidate 1)")
    print("  - N_c⁴ + N_c³ - N_c² + N_c (Candidate 2)")
    print()
    print("Both yield 102 at N_c=3, but they're structurally different. The")
    print("CLEANER structural choice would emerge from cascade-internal physics")
    print("of the 2-loop diagrams — which contributions live at which cascade")
    print("layers — but this hasn't been derived.")
    print()
    print("Compare β_0: only ONE cascade-primitive form (N_c² + N_c - 1) -")
    print("(N(0)/N_c)·n_f. Clean.")
    print()
    print("β_1's two-form ambiguity is structural: at 2-loop, multiple Feynman")
    print("diagrams contribute, and the cascade reading needs a derivation of")
    print("WHICH structural decomposition is forced by cascade interactions.")
    print("This is the open structural piece for β_1, parallel to PR #140's")
    print("open structural piece for β_0 (why N_c²+N_c-1 specifically).")
    print()
    print("Higher-loop (β_2, β_3, β_4) extensions would have similar issues:")
    print("multiple contributing diagrams, multiple cascade-primitive forms,")
    print("ambiguity in choice of decomposition without cascade-internal")
    print("interaction-level derivation.")
    print()
    print("RECOMMENDATION:")
    print("  - β_0 cascade-primitive identification (rem:cascade-beta0): clean")
    print("    Tier 3 result, specific ambiguity in structural meaning")
    print("  - β_1 cascade-primitive identification (this tool): ambiguous form,")
    print("    requires cascade-interaction-level derivation to disambiguate")
    print("  - Higher-loop QCD running cascade-natively: open structural problem")
    print("    requiring substantive cascade research at the 2-loop+ level")
    print()
    print("This is the natural extension of cascade-native QED frontier work")
    print("(oq:higher-loop-qed-coefficients) to QCD: same structural pattern,")
    print("same difficulties at higher orders, same need for cascade-")
    print("interaction-level derivation.")


if __name__ == "__main__":
    main()
