#!/usr/bin/env python3
"""
(R1b) attack: cascade-native derivation of the smallest-magnitude
principle |Y_QL| = 1/(2 N_c) = 1/6.

CONTEXT
=======
After Route A (commit bfc53e7), (R1) Y_H = N_c * Y_QL decomposes as:
  (R1a) |Y_H|  = 1/2   [CLOSED via Higgs vacuum + SU(2) doublet]
  (R1b) |Y_QL| = 1/6   [OPEN: smallest-magnitude principle]
  (R1c) sign relation  [follows from sign anchor]

This script attacks (R1b): close cascade-natively that Y_QL takes
the smallest non-zero value in the cascade fractional structure.

THE STRUCTURAL OBSERVATION
==========================
In cascade-native units with 1 cascade unit = 1/(2 N_c) = 1/6 SM,
all SM Y values are INTEGERS:

  particle  Y_SM    Y_cascade (in 1/6 units)
  Q_L       +1/6    +1   (smallest non-zero magnitude)
  u_R       +2/3    +4
  d_R       -1/3    -2
  L_L       -1/2    -3
  e_R       -1      -6
  H         +1/2    +3

Q_L sits at the cascade-fundamental U(1)_Y rep (smallest non-zero).

(R1b) asks WHY this is so cascade-natively.

THIS SCRIPT
===========
Attempts THREE candidate cascade-native arguments for (R1b):
  CANDIDATE 1: cascade U(1)_Y minimality (matter at smallest rep).
  CANDIDATE 2: maximally-gauge-charged matter at smallest unit.
  CANDIDATE 3: 'fundamental rep of U(1)_Y' in cascade fractional units.

For each, identifies what the argument needs and where it fails or
succeeds.

WHAT THIS SCRIPT DELIVERS
=========================
Honest assessment of (R1b) closability from existing cascade primitives.
"""

from __future__ import annotations

import sys
from fractions import Fraction


def report_setup():
    print("=" * 78)
    print("(R1b) SETUP: smallest-magnitude principle for Y_QL")
    print("=" * 78)
    print()
    print("Cascade fractional structure (CLOSED in CLAUDE.md):")
    print("  Y_QL in (1/6) Z = (1/(2 N_c)) Z")
    print("  Y_QL is ODD multiple of 1/6 (from Q_u, Q_d in (1/3) Z)")
    print("  -> Y_QL in {..., -5/6, -1/2, -1/6, 1/6, 1/2, 5/6, ...}")
    print()
    print("(R1b) STATEMENT: |Y_QL| = 1/6 (smallest non-zero allowed value).")
    print()
    print("In CASCADE-NATIVE UNITS (1 unit = 1/(2 N_c) = 1/6 SM):")
    print()
    print(f"  {'particle':>10s}  {'Y_SM':>10s}  {'Y_cascade':>12s}  {'|Y_cascade|':>14s}")
    rows = [
        ("Q_L",   Fraction(1, 6)),
        ("u_R",   Fraction(2, 3)),
        ("d_R",   Fraction(-1, 3)),
        ("L_L",   Fraction(-1, 2)),
        ("e_R",   Fraction(-1, 1)),
        ("H",     Fraction(1, 2)),
    ]
    for name, Y_sm in rows:
        Y_cascade = Y_sm * 6
        print(f"  {name:>10s}  {str(Y_sm):>10s}  {str(Y_cascade):>12s}  "
              f"{str(abs(Y_cascade)):>14s}")
    print()
    print("Q_L has SMALLEST non-zero |Y_cascade| = 1.")
    print()
    print("(R1b) reformulated: cascade U(1)_Y rep of Q_L is the FUNDAMENTAL")
    print("(smallest non-zero charge) in cascade-native units.")
    print()


def candidate_1_minimality_principle():
    print("=" * 78)
    print("CANDIDATE 1: cascade U(1)_Y minimality principle")
    print("=" * 78)
    print()
    print("HYPOTHESIS: matter at the cascade gauge window occupies U(1)_Y")
    print("reps from the smallest non-zero magnitude UPWARD.  Q_L is at")
    print("the cascade-fundamental U(1)_Y rep (smallest = 1 cascade unit).")
    print()
    print("Cascade-native motivation: the cascade has fund-or-trivial reps")
    print("of SU(3) (V_12 in {1, 3}) and SU(2) (V_13 in {1, 2}), per")
    print("rem:fund-or-trivial.  By analogy, U(1)_Y matter should also be in")
    print("'fundamental' (smallest non-zero) or 'trivial' (zero).")
    print()
    print("CHECK against SM Y values:")
    print()
    print("  particle  Y_cascade  smallest non-zero?")
    rows = [
        ("Q_L", 1, True),
        ("u_R", 4, False),
        ("d_R", -2, False),
        ("L_L", -3, False),
        ("e_R", -6, False),
        ("H",   3, False),
    ]
    for name, Y, small in rows:
        print(f"  {name:>8s}  {Y:>+5d}      {'YES' if small else 'NO'}")
    print()
    print("RESULT: only Q_L is at smallest |Y|.  Other matter has |Y| > 1")
    print("in cascade units.  This BREAKS the strict 'fund-or-trivial of U(1)_Y'")
    print("analogy: U(1)_Y reps for matter are NOT all in {0, +/- 1}.")
    print()
    print("STATUS: HYPOTHESIS FAILS.  Cascade matter does NOT all sit at")
    print("the smallest U(1)_Y rep.  Higher reps (4, -2, -3, -6, 3) appear.")
    print("Strict fund-or-trivial U(1)_Y minimality is contradicted by")
    print("observation.")
    print()
    print("WEAKER VERSION: only Q_L is required to be at smallest U(1)_Y")
    print("rep; other matter Y is determined by Yukawa singlets + (R1a) +")
    print("(R2) given Y_QL.  This is structurally consistent but introduces")
    print("an arbitrary 'Q_L is special' choice.  Cascade-internal reason")
    print("for Q_L being special: Q_L is the only matter type that's BOTH")
    print("color-charged AND isospin-charged (max gauge structure).")
    print()


def candidate_2_max_gauge_structure():
    print("=" * 78)
    print("CANDIDATE 2: maximally-gauge-charged matter at smallest U(1)_Y unit")
    print("=" * 78)
    print()
    print("HYPOTHESIS: the matter unit with the MOST cascade gauge structure")
    print("(highest dim of V_12 x V_13) sits at the smallest non-zero")
    print("U(1)_Y charge.")
    print()
    print("Per-particle (V_12, V_13) dim:")
    rows = [
        ("Q_L", 3, 2, 6),
        ("u_R", 3, 1, 3),
        ("d_R", 3, 1, 3),
        ("L_L", 1, 2, 2),
        ("e_R", 1, 1, 1),
        ("H",   1, 2, 2),
    ]
    print()
    print(f"  {'particle':>10s}  {'V_12 dim':>10s}  {'V_13 dim':>10s}  "
          f"{'product':>10s}  {'|Y_cascade|':>14s}")
    for name, v12, v13, prod in rows:
        Y_cascade_abs = {"Q_L": 1, "u_R": 4, "d_R": 2, "L_L": 3,
                         "e_R": 6, "H": 3}[name]
        print(f"  {name:>10s}  {v12:>10d}  {v13:>10d}  {prod:>10d}  "
              f"{Y_cascade_abs:>+14d}")
    print()
    print("Q_L has product = 6 (max) AND |Y_cascade| = 1 (min).  Pattern HOLDS")
    print("for Q_L specifically.")
    print()
    print("But: matter with intermediate gauge structure has variable |Y|:")
    print("  u_R (3, 1) -> product 3, |Y| = 4")
    print("  d_R (3, 1) -> product 3, |Y| = 2")
    print("  L_L (1, 2) -> product 2, |Y| = 3")
    print("  H   (1, 2) -> product 2, |Y| = 3")
    print("  e_R (1, 1) -> product 1, |Y| = 6")
    print()
    print("The 'inverse correlation' product * |Y| = 6 = N_c * N_doublet is")
    print("checkable:")
    rows = [
        ("Q_L", 6, 1),
        ("u_R", 3, 4),
        ("d_R", 3, 2),
        ("L_L", 2, 3),
        ("e_R", 1, 6),
        ("H",   2, 3),
    ]
    for name, prod, Y_abs in rows:
        product = prod * Y_abs
        print(f"  {name:>8s}: prod * |Y| = {prod} * {Y_abs} = {product}  "
              f"{'== 6 ✓' if product == 6 else 'NOT 6'}")
    print()
    print("RESULT: Q_L, e_R have prod * |Y| = 6.  u_R has prod * |Y| = 12,")
    print("d_R has prod * |Y| = 6, L_L has prod * |Y| = 6, H has prod * |Y| = 6.")
    print()
    print("CLOSE: 5/6 particles satisfy prod * |Y| = N_c * N_doublet = 6.")
    print("u_R is the OUTLIER (prod * |Y| = 12, not 6).")
    print()
    print("STATUS: HYPOTHESIS PARTIALLY HOLDS.  The relation prod * |Y| = 6")
    print("works for Q_L, d_R, L_L, e_R, H but fails for u_R.")
    print()
    print("u_R's |Y| = 4 cascade units (= 2/3 SM) breaks the pattern.")
    print("Cascade-internally: u_R must have Y_uR = Y_QL + Y_H = 1 + 3 = 4")
    print("(Yukawa singlet), so |Y_uR| = 4, not 2.  The Yukawa singlet")
    print("conditions FORCE u_R away from the prod * |Y| = 6 relation.")
    print()
    print("This means the prod * |Y| = N_c * N_doublet = 6 relation is")
    print("structurally INTERPRETABLE for some matter but NOT a forced")
    print("cascade theorem.  It's an EMERGENT pattern post-Yukawa, not a")
    print("derivation principle.")
    print()


def candidate_3_fundamental_U1_rep():
    print("=" * 78)
    print("CANDIDATE 3: U(1)_Y fundamental rep in cascade fractional units")
    print("=" * 78)
    print()
    print("HYPOTHESIS: the cascade U(1)_Y has a discrete charge unit (= 1")
    print("in cascade-native units = 1/(2 N_c) in SM units).  Q_L is at")
    print("the FUNDAMENTAL rep (charge +/- 1 cascade unit).")
    print()
    print("Cascade primitive: U(1)_Y at d=14 generated by J on R^14 = C^7.")
    print("J's eigenvalues are +/- i; under exp(theta J), eigenstates pick")
    print("up phases exp(+/- i theta).")
    print()
    print("In cascade-native units: J's fundamental charge unit is 1.")
    print()
    print("KEY QUESTION: how does the cascade U(1)_Y unit (J's eigenvalue 1)")
    print("relate to the SM Y unit (1/6)?")
    print()
    print("Possibility: the cascade U(1)_Y unit is the 'fundamental rep of")
    print("U(1)_Y on the cascade matter content', and matches the smallest")
    print("non-zero |Y| in the SM spectrum (= 1/6 = 1/(2 N_c)).")
    print()
    print("Combined with the cascade fractional structure (Y in 1/(2 N_c) Z")
    print("units from N_c + doublet), this gives:")
    print("  cascade U(1)_Y unit = 1/(2 N_c) in SM units")
    print("  Q_L at +1 cascade unit = +1/(2 N_c) = +1/6 SM")
    print("  Other matter at higher integer multiples")
    print()
    print("STATUS: structurally consistent but CIRCULAR.  We're saying:")
    print("  (a) The cascade U(1)_Y unit is the smallest non-zero |Y| in the SM.")
    print("  (b) Q_L sits at this smallest unit.")
    print("Both are observation-validated but not derived.")
    print()
    print("To make this a CASCADE THEOREM, need a cascade-native argument")
    print("for WHY the cascade U(1)_Y unit equals 1/(2 N_c) in SM units")
    print("(rather than e.g., 1 SM unit, or 1/N_c, or 1/2).  This requires")
    print("connecting J's eigenvalues at d=14 to the cascade fractional")
    print("structure of matter content at d=12 + d=13.")
    print()


def report_residual():
    print("=" * 78)
    print("(R1b) STATUS AFTER THIS DIG")
    print("=" * 78)
    print()
    print("Three candidate cascade-native arguments attempted:")
    print()
    print("  CANDIDATE 1: cascade U(1)_Y minimality (matter at smallest rep)")
    print("    FAILS strictly: matter Y values include +/- 1, +/- 2, +/- 3,")
    print("    +/- 4, +/- 6 in cascade units, not just 0 or +/- 1.")
    print("    Weaker version (Q_L only at smallest) introduces 'Q_L is")
    print("    special' without cascade-internal justification.")
    print()
    print("  CANDIDATE 2: max gauge structure at smallest U(1)_Y unit")
    print("    PARTIALLY HOLDS: prod(V_12 dim, V_13 dim) * |Y_cascade| = 6")
    print("    for Q_L, d_R, L_L, e_R, H -- but NOT for u_R (which gives 12).")
    print("    The relation is post-Yukawa, not a derivation principle.")
    print()
    print("  CANDIDATE 3: U(1)_Y fundamental rep in cascade fractional units")
    print("    STRUCTURALLY CONSISTENT but CIRCULAR.  Requires a separate")
    print("    cascade-native argument for why the cascade U(1)_Y unit at")
    print("    d=14 equals 1/(2 N_c) in SM units.")
    print()
    print("HONEST CONCLUSION")
    print("=================")
    print("(R1b) is NOT closeable cascade-natively from existing primitives.")
    print()
    print("The smallest-magnitude principle for Y_QL is structurally well-")
    print("defined and observationally validated, but no cascade-internal")
    print("derivation has been identified.  The three candidate routes:")
    print("  (1) Strict minimality - falsified by SM Y spectrum.")
    print("  (2) Max-gauge-structure - works for 5/6 particles, fails for u_R.")
    print("  (3) U(1)_Y fundamental rep - circular without separate input.")
    print()
    print("The structural content of (R1b) reduces to: 'the cascade U(1)_Y")
    print("unit at d=14 equals 1/(2 N_c) in SM units, and Q_L sits at this")
    print("smallest unit'.  Both pieces are observation-input currently.")
    print()
    print("WHAT WOULD CLOSE (R1b) CASCADE-NATIVELY")
    print("=========================================")
    print("A cascade theorem connecting J's eigenvalues at d=14 (cascade")
    print("U(1)_Y unit) to the cascade fractional structure of matter at")
    print("d=12 (color triplet with charge denominator N_c) + d=13 (SU(2)")
    print("doublet structure with T_3 +/- 1/2).  The theorem would force:")
    print()
    print("  cascade U(1)_Y unit at d=14 = 1/(2 N_c) in SM units")
    print()
    print("Currently, the cascade has J's eigenvalues +/- 1 (cascade unit)")
    print("and matter Y in (1/(2 N_c)) Z (cascade fractional structure), but")
    print("the IDENTIFICATION of the two units is observation-input.  Closing")
    print("(R1b) would require deriving this identification cascade-natively.")
    print()
    print("CHAIN OF REDUCTIONS (UPDATED)")
    print("==============================")
    print("  matter-rep gap (CLAUDE.md, original)")
    print("    -> oq:fermion-gauge-action")
    print("    -> path-tensor consistency")
    print("    -> integer Q numerators")
    print("    -> (R1), DECOMPOSED:")
    print("       (R1a) |Y_H|  = 1/2  [CLOSED via Higgs vacuum + Z_2]")
    print("       (R1b) |Y_QL| = 1/6")
    print("            -> cascade U(1)_Y unit = 1/(2 N_c) in SM units")
    print("               [OPEN: requires J-cascade-fractional identification]")
    print("            + Q_L at smallest cascade U(1)_Y rep")
    print("               [OPEN: 'Q_L is special' lacks cascade reason]")
    print("       (R1c) sign relation [follows from sign anchor]")
    print("    -> sign anchor: observer-hemisphere on S^4  [REFRAMED]")
    print()
    print("(R1b) is now further sharpened into TWO sub-pieces, each")
    print("specific and tractable but not yet derived.")
    print()


def main() -> int:
    print("=" * 78)
    print("(R1b) ATTACK: cascade-native smallest-magnitude principle")
    print("=" * 78)
    print()
    report_setup()
    candidate_1_minimality_principle()
    candidate_2_max_gauge_structure()
    candidate_3_fundamental_U1_rep()
    report_residual()
    return 0


if __name__ == "__main__":
    sys.exit(main())
