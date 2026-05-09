#!/usr/bin/env python3
"""Cascade investigation: is d_gw = dim G_2 = 14 structurally forced?

Building on PR #141's resolution of d_0 = ρ(8)−1 via Spin(7)/G_2:
the cascade-wide Lie-theoretic dimensional tower (rem:lie-theoretic-tower)
flagged d_gw = dim G_2 = 14 as 'suggestive but not yet rigorously forced'.

This investigation tests whether the equality is forced via a chain
of cascade-internal commitments.

The forcing chain:

  Cascade Catalan (cover sheet):        d_gw = 2·d_0
  Lie-theoretic (G_2 ⊃ SU(3) decomp):   dim G_2 = (N_c² − 1) + (d_0 − 1)
  Equality test:                        2·d_0 = N_c² + d_0 − 2
                                  ⟺     d_0 = N_c² − 2
                                  ⟺     N_c² = d_0 + 2 = 9
                                  ⟺     N_c = 3

The forcing of d_gw = dim G_2 reduces to the small-integer identity
d_0 = N_c² − 2 (equivalently ρ(8) = N_c² − 1 = dim SU(3)). This
identity holds with cascade-derived N_c = 3 (Adams ρ(12)−1) and
d_0 = 7 (Γ-area-max), but its cascade-internal forcing requires a
deeper structural argument.

Possible structural reading: both d_0 = N_c² − 2 = 7 and ρ(8) = 8
encode the octonion dimension dim O = 8, via two cascade structures:
  • dim SU(3) = N_c² − 1 = 8 = dim O   (cascade gauge generators)
  • ρ(8) = 8 (Adams maximum at S^7)     (octonion parallelizability)

If the cascade's commitment to G_2/SU(3) at d_0 forces both
identifications (gauge dim + parallelizability count) to reflect the
SAME octonion dimension, then ρ(8) = N_c² − 1 follows structurally
and d_gw = dim G_2 is forced.

Verdict: d_gw = dim G_2 is CONDITIONALLY forced via the Lie-theoretic
decomposition + cascade Catalan + Adams identity ρ(8) = N_c² − 1
(both factors = dim O = 8). The open structural piece sharpens to:
prove the cascade's two derivations of N_c (Adams gauge layer
ρ(12) − 1 = 3 and octonion-dim parallelizability ρ(8) = 8) coincide
at N_c = 3 by cascade-internal structural mechanism.
"""

from __future__ import annotations

import math


# Cascade primitives
N_C = 3
N_0 = 2
D_V = 5
D_0 = 7
D_GW = 14


def adams_rho(n: int) -> int:
    if n == 0:
        return 0
    e, m = 0, n
    while m % 2 == 0:
        m //= 2
        e += 1
    q, r = e // 4, e % 4
    return 8*q + 2**r


def dim_lie(name: str) -> int:
    """Dimensions of relevant Lie groups."""
    return {
        'SU(3)': 8, 'SU(2)': 3, 'U(1)': 1,
        'G_2': 14, 'F_4': 52, 'E_8': 248,
        'Spin(5)': 10, 'Spin(7)': 21, 'Spin(8)': 28,
        'O': 8,  # octonion algebra dimension
    }[name]


def main() -> None:
    print("=" * 92)
    print("CASCADE INVESTIGATION: is d_gw = dim G_2 = 14 structurally forced?")
    print("=" * 92)
    print()
    print("Cascade-wide Lie-theoretic dimensional tower (PR #141, "
          "rem:lie-theoretic-tower)")
    print("flagged the identification d_gw = dim G_2 as 'suggestive but not yet")
    print("rigorously forced'. This investigation tests the forcing chain.")
    print()

    print("=" * 92)
    print("THE FORCING CHAIN")
    print("=" * 92)
    print()
    print("Two cascade-internal derivations of d_gw and dim G_2:")
    print()
    print("PATH 1 — cascade derivation of d_gw:")
    print(f"  Cascade Catalan reading (cover sheet, line 2473):")
    print(f"     d_gw = 2 · d_0 = 2 · {D_0} = {2*D_0}")
    print(f"  Adams + cascade gauge structure:")
    print(f"     d_gw = 14 because ρ(14) − 1 = 1 (U(1) gauge layer)")
    print()
    print("PATH 2 — Lie-theoretic dim G_2 via G_2 ⊃ SU(3) decomposition:")
    print(f"  G_2 / SU(3) = S^6  (cover sheet, algebra source at d_0=7)")
    print(f"  dim G_2 = dim SU(3) + dim(G_2/SU(3))")
    print(f"         = (N_c² − 1) + (d_0 − 1)")
    print(f"         = {N_C**2 - 1} + {D_0 - 1}")
    print(f"         = {(N_C**2-1) + (D_0-1)}")
    print()
    print(f"Equality:  d_gw = {D_GW}  =  dim G_2 = {(N_C**2-1) + (D_0-1)}  ✓")
    print()

    print("=" * 92)
    print("REDUCING THE FORCING: what's the open piece?")
    print("=" * 92)
    print()
    print("Setting Path 1 = Path 2:")
    print(f"  2·d_0 = (N_c² − 1) + (d_0 − 1)")
    print(f"  2·d_0 = N_c² + d_0 − 2")
    print(f"  d_0 = N_c² − 2")
    print()
    print(f"Test: d_0 = N_c² − 2 ⟺ {D_0} = {N_C**2} − 2 = {N_C**2 - 2}  ✓")
    print()
    print("So d_gw = dim G_2 is forced IF the cascade has the identity:")
    print()
    print("  ┌─────────────────────────────────────────────┐")
    print("  │  d_0 = N_c² − 2  (equivalently N_c² = d_0 + 2)  │")
    print("  └─────────────────────────────────────────────┘")
    print()

    print("=" * 92)
    print("EQUIVALENT FORMS OF d_0 = N_c² − 2")
    print("=" * 92)
    print()
    forms = [
        ('d_0 = N_c² − 2',                    D_0,         N_C**2 - 2),
        ('N_c² = d_0 + 2',                    N_C**2,      D_0 + 2),
        ('ρ(8) = N_c² − 1',                   adams_rho(8), N_C**2 - 1),
        ('ρ(8) = dim SU(3)',                   adams_rho(8), 8),
        ('d_0 + 1 = ρ(8) = dim O',             D_0 + 1,    adams_rho(8)),
        ('d_0 = dim SU(3) − 1 = dim O − 1',    D_0,         dim_lie('SU(3)') - 1),
    ]
    for form, lhs, rhs in forms:
        match = '✓' if lhs == rhs else '✗'
        print(f"  {form:<40}  {lhs} = {rhs}  {match}")
    print()

    print("Cascade reading: d_0 + 1 = dim O (octonion algebra dim) = 8.")
    print()
    print("The octonion dimension '8' enters the cascade in TWO independent ways:")
    print()
    print("  (a) ρ(8) = 8: Adams maximum at the parallelizable octonion sphere S^7")
    print("      (Hurwitz-Radon at n = 2^3, octonion right-multiplications)")
    print("  (b) dim SU(3) = N_c² − 1 = 8 (with cascade N_c = 3 from Adams ρ(12)−1)")
    print("      (Lie algebra of SU(N) has N²−1 generators)")
    print()
    print("For d_gw = dim G_2 to be cascade-forced, (a) and (b) must coincide via")
    print("a STRUCTURAL mechanism, not just a small-integer identity.")
    print()

    print("=" * 92)
    print("STRUCTURAL READING")
    print("=" * 92)
    print()
    print("The cascade's commitment to G_2/SU(3) = S^6 at d_0 (cover sheet)")
    print("brings octonions into play. G_2 = Aut(O) is the octonion automorphism")
    print("Lie group. The cascade gauge group SU(3) sits inside G_2 as the")
    print("stabilizer of a unit octonion in S^7. Two consequences:")
    print()
    print("  (i)  dim O = 8 is determined (octonion algebra is 8-dimensional)")
    print("  (ii) SU(3) ⊂ G_2 forces SU(3) to act on the imaginary octonions S^6")
    print()
    print("For (ii) to give SU(3) with EIGHT generators (dim SU(3) = 8 = dim O),")
    print("the cascade gauge group's color count N_c must satisfy")
    print()
    print("   N_c² − 1 = dim SU(3) = 8 = dim O = ρ(8)")
    print()
    print("which forces N_c² = 9, hence N_c = 3.")
    print()
    print("Independently, Adams gives N_c = ρ(12) − 1 = 3 from the cascade gauge")
    print("layer at d_g = 12. So both Adams (combinatorial) and Lie/octonion")
    print("(structural) routes give N_c = 3 at the small-integer level.")
    print()
    print("Their coincidence — N_c (Adams gauge) = N_c (octonion-dim Lie) — is")
    print("the cascade-internal forcing piece. If this coincidence is itself")
    print("forced (e.g., by the cascade's commitment to SU(3) AS THE OCTONION-")
    print("STABILIZER subgroup of G_2), then d_gw = dim G_2 is fully forced.")
    print()
    print("Currently this is one Lie-theoretic step short of full forcing:")
    print()
    print("  Forced:        N_c = 3 from Adams at d_g = 12")
    print("  Lie-theoretic: dim G_2 = dim SU(3) + dim S^6 = (N_c²−1) + (d_0−1)")
    print("  Cascade Cat:   d_gw = 2 d_0")
    print("  Open piece:    Why does Adams ρ(8) = N_c² − 1 cascade-internally?")
    print("                  (i.e., why is the octonion dim equal to dim SU(3)?)")
    print()

    print("=" * 92)
    print("VERDICT")
    print("=" * 92)
    print()
    print("d_gw = dim G_2 = 14 is CONDITIONALLY FORCED via the Lie-theoretic")
    print("decomposition dim G_2 = dim SU(3) + dim S^6 plus cascade Catalan")
    print("d_gw = 2 d_0, conditional on the cascade integer identity")
    print()
    print("    ρ(8) = N_c² − 1 = dim SU(3)  =  dim O = 8")
    print()
    print("(equivalently d_0 = N_c² − 2). This identity holds at cascade-")
    print("derived values of N_c (Adams) and d_0 (Γ), and has a Lie-theoretic")
    print("interpretation as 'SU(3) is the octonion-stabilizer subgroup of G_2",
          "(both have dimension matching the octonion algebra)'.")
    print()
    print("The remaining open structural piece: prove that the cascade's two")
    print("derivations of N_c (Adams ρ(12)−1 = 3 and √(d_0+2) = 3, equivalently")
    print("dim SU(3) = ρ(8)) are forced to coincide cascade-internally. If the")
    print("cascade commitment to G_2/SU(3) at d_0 (cover sheet) forces SU(3)")
    print("to be the octonion-stabilizer with dim SU(3) = ρ(8), then d_gw =")
    print("dim G_2 is fully forced.")
    print()
    print("Status: rem:lie-theoretic-tower's d_gw entry promotes from 'suggestive'")
    print("to 'conditionally forced via the chain above'. The open piece is now")
    print("sharply identified — narrower scope than 'why does d_gw = 14 = dim G_2?'")
    print("— and parallel in structure to PR #141's pre-Spin(7)/G_2 state for d_0.")
    print()
    print("Promotion target: a cascade-internal proof that the SU(3) gauge group")
    print("at d_g = 12 (Adams) is the octonion-stabilizer of G_2 at d_0 = 7,")
    print("with dim SU(3) = dim O = ρ(8) = 8 cascade-natively.")


if __name__ == "__main__":
    main()
