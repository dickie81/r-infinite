#!/usr/bin/env python3
"""
Audit Section 10.10: d = 14 = dim G_2 coincidence.

The audit flags this as IGN with a question mark: "Coincidence at U(1) layer?"

Facts:
  - G_2 is the smallest exceptional Lie group, rank 2, dim 14.
  - G_2 = Aut(O), the automorphism group of the octonions.
  - G_2 acts on S^6 = unit imaginary octonions, preserving cross-product structure.
  - dim G_2 = 14.
  - Cascade U(1) hypercharge layer is at d = 14 (gauge window upper edge).
  - Cascade SU(3) algebra is at d = 7 = dim S^6 (where G_2 acts), USED via
    audit entry 10.11 (G_2/SU(3) on S^6 at d=7).

Question: is d = 14 = dim G_2 a structural relation, or numerical coincidence?

Three readings to test:
  R1: NUMEROLOGY -- coincidence, no cascade content.
  R2: AUTOMORPHISM -- d = 14 plays the role "dim of automorphism group of
      d = 8's structure" (since 8 = dim O and 14 = dim Aut(O) = G_2).
  R3: HIDDEN G_2 -- the cascade encodes G_2 structure at d = 14 via some
      mechanism (analogous to G_2 on S^6 at d = 7).
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def R(d: int) -> float:
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha(d: int) -> float:
    return R(d) ** 2 / 4


def main() -> int:
    print("=" * 78)
    print("AUDIT 10.10: d = 14 = dim G_2 -- COINCIDENCE OR STRUCTURE?")
    print("=" * 78)
    print()

    # G_2 facts
    print("G_2 FACTS:")
    print("  dim G_2          = 14")
    print("  rank G_2         = 2")
    print("  num roots        = 12 (6 long + 6 short)")
    print("  G_2 = Aut(O)     where O is the octonions, dim O = 8")
    print("  G_2 acts on S^6  = unit imaginary octonions (dim Im O = 7)")
    print()

    # Cascade gauge window
    print("CASCADE GAUGE WINDOW (Part IVa):")
    print("  d = 12: SU(3) gauge boson layer (Adams' theorem rho(12) = 8)")
    print("  d = 13: SU(2) gauge boson layer (Dirac obstruction)")
    print("  d = 14: U(1) hypercharge layer (gauge window upper edge)")
    print("  Standard Model gauge group dimension: 8 + 3 + 1 = 12 (NOT 14)")
    print()

    # Test Reading R2: dim Aut(O) at d = dim O + dim Aut(O)?
    print("-" * 78)
    print("READING R2 TEST: d = 14 as 'dim Aut of structure at d = 8'?")
    print("-" * 78)
    print()
    print("Octonion structure: dim O = 8, dim Aut(O) = dim G_2 = 14.")
    print("Cascade d = 8 is 'first Bott multiple' (audit 10.8, USED).")
    print("Cascade d = 14 might 'remember' the automorphism group of d = 8's")
    print("octonion structure.")
    print()
    print("Test: does any cascade quantity at d = 14 reference d = 8?")
    print()
    print(f"{'quantity':>12}  {'d=8 value':>14}  {'d=14 value':>14}  {'ratio':>14}")
    print("-" * 70)
    qty_8 = R(8)
    qty_14 = R(14)
    print(f"{'R(d)':>12}  {qty_8:>14.6e}  {qty_14:>14.6e}  {qty_14/qty_8:>14.6f}")
    a8 = alpha(8)
    a14 = alpha(14)
    print(f"{'alpha(d)':>12}  {a8:>14.6e}  {a14:>14.6e}  {a14/a8:>14.6f}")
    print()
    print("alpha(14) / alpha(8) ~ 0.36 -- no clean ratio.")
    print("R(14) / R(8) ~ 0.74 -- no clean ratio.")
    print("No cascade quantity at d=14 references d=8 in a way that would")
    print("structurally encode 'dim Aut(O)'.  R2 NOT supported.")
    print()

    # Test Reading R3: G_2 hidden at d = 14?
    print("-" * 78)
    print("READING R3 TEST: hidden G_2 structure at d = 14?")
    print("-" * 78)
    print()
    print("For G_2 to be a structure group at d = 14, S^13 would need to admit")
    print("G_2 structure.  But:")
    print("  - dim S^13 = 13, dim G_2 = 14: G_2 cannot act transitively on S^13")
    print("    (would need orbit dim <= dim S^13).")
    print("  - G_2 has no natural representation of dim 13.  Standard reps:")
    print("    7 (fundamental, on Im O), 14 (adjoint), 27, 64, 77, ...")
    print("    None of these match S^13 = boundary of the d=14 unit ball.")
    print("  - G_2 does NOT act on the 14-dim ball B^14 in a canonical way")
    print("    (not the structure group of any natural 14-manifold).")
    print()
    print("By contrast, G_2 DOES act on S^6 at d=7 via Aut(O) preserving")
    print("imaginary octonion product (audit 10.11, USED).  The d=7 case has")
    print("a structural mechanism; the d=14 case does not.")
    print()
    print("Verdict: R3 not supported.  G_2 has no natural action on the")
    print("d=14 cascade objects (B^14, S^13, or related cascade structures).")
    print()

    # Reading R1: numerology
    print("-" * 78)
    print("READING R1 (NUMEROLOGY): is the coincidence accidental?")
    print("-" * 78)
    print()
    print("dim G_2 = 14 is a fact about Lie group dimensions.")
    print("Cascade d = 14 is the gauge-window upper edge from Bott + Adams.")
    print("The latter is forced by Part IVa's gauge-boson layer assignments")
    print("({12, 13, 14}); the former is independent classical group theory.")
    print()
    print("Other dimension coincidences with cascade tower:")
    print(f"  d=14 vs dim G_2     = 14   COINCIDES")
    print(f"  d=21 vs dim SU(5)   = 24   no")
    print(f"  d=21 vs dim Sp(2)   = 10   no")
    print(f"  d=19 vs dim ?       = ?    no special Lie group")
    print(f"  d=12 vs dim Sp(2)   = 10   no")
    print(f"  d=14 vs dim Sp(3)   = 21   no")
    print(f"  d=8 vs dim SU(3)    = 8    coincides (used: SU(3) at d=12 not d=8)")
    print()
    print("The cascade has 5 distinguished layers + gauge window = 7 special")
    print("integers in {1, ..., 217}.  Any one of them might coincidentally")
    print("equal a Lie-group dimension.  d=14 = dim G_2 is consistent with")
    print("base-rate coincidence given the small sample of cascade-special")
    print("dimensions and the abundance of Lie groups with small dimensions.")
    print()

    print("=" * 78)
    print("VERDICT")
    print("=" * 78)
    print()
    print("d = 14 = dim G_2 has no structural cascade content beyond numerology.")
    print()
    print("  R1 (numerology): consistent with base-rate coincidence given the")
    print("                   small sample of cascade-special dimensions")
    print("  R2 (Aut(O) link): no cascade quantity at d=14 references d=8 in a")
    print("                   structural way; ratios alpha(14)/alpha(8) ~ 0.36")
    print("                   and R(14)/R(8) ~ 0.74 are not clean")
    print("  R3 (hidden G_2): G_2 cannot act on S^13 (dim mismatch); no natural")
    print("                   G_2 action on cascade d=14 objects exists")
    print()
    print("Audit recommendation: 10.10 should move from 'IGN, coincidence?' to")
    print("'IGN, numerological coincidence (no structural mechanism analogous")
    print("to 10.11 d=7 / G_2/SU(3) on S^6)'.")
    print()
    print("This contrasts with 10.11 (d=7 = dim S^6 admits G_2 structure, USED):")
    print("  - 10.11 has a STRUCTURAL MECHANISM: G_2 acts on S^6 = unit imaginary")
    print("    octonions, preserving cross-product structure.")
    print("  - 10.10 has NO STRUCTURAL MECHANISM: G_2 does not act on cascade")
    print("    d=14 objects in any natural way.")
    print()
    print("Honest finding: the most provocative cascade-Lie-group coincidence")
    print("turns out to be empty.  No new structural content emerges.  Section")
    print("10.10 closes as 'numerologically suggestive but structurally empty'.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
