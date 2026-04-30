#!/usr/bin/env python3
"""
(R1b) deeper attack: sector-dependent fundamental U(1)_Y rep
+ Yukawa pairing structure.

CONTEXT
=======
After commit b56b62b, (R1b) sharpens to two sub-pieces:
  (R1b-i)  cascade U(1)_Y unit at d=14 = 1/(2 N_c) in SM units.
  (R1b-ii) Q_L at smallest cascade U(1)_Y rep.

This script attempts a unified bridge: matter occupies the
FUNDAMENTAL U(1)_Y rep of its (V_12, V_13) SECTOR, where the
fundamental unit is sector-dependent.

THE STRUCTURAL OBSERVATION
==========================
Each (V_12, V_13) combination has a natural U(1)_Y unit determined
by the cascade fractional structure of that sector:

  sector (V_12, V_13)  | fundamental U(1)_Y unit  | matter type
  --------------------------------------------------------------
  (3, 2)               | 1/(N_c * N_doublet) = 1/6 | Q_L
  (3, 1)               | 1/N_c = 1/3              | u_R, d_R
  (1, 2)               | 1/N_doublet = 1/2        | L_L, H
  (1, 1)               | 1                         | e_R

Each matter type sits at the FUNDAMENTAL of its sector (charge +/- 1
in sector units), MODULO Yukawa singlet pairing which may push some
to higher integer multiples.

CHECK
=====
Does each SM particle sit at +/- 1 sector-fundamental unit?

  Q_L: Y_QL = +1/6 = +1 (3,2)-sector unit  ✓
  d_R: Y_dR = -1/3 = -1 (3,1)-sector unit  ✓
  L_L: Y_LL = -1/2 = -1 (1,2)-sector unit  ✓
  e_R: Y_eR = -1   = -1 (1,1)-sector unit  ✓
  H:   Y_H  = +1/2 = +1 (1,2)-sector unit  ✓
  u_R: Y_uR = +2/3 = +2 (3,1)-sector units  OUTLIER

5/6 particles satisfy 'fundamental of sector'.  u_R is the outlier,
forced to +2 sector units by Yukawa singlet:
  Y_uR = Y_QL + Y_H = +1/6 + 1/2 = +2/3 = 2 * (1/3)

The cascade-internal structure for u_R: it's the Yukawa partner of
Q_L (via tilde H), so its Y is FORCED by Y_QL and Y_H, not
independently fundamental.

CASCADE-NATIVE PRINCIPLE
========================
'Matter at the cascade gauge window occupies the FUNDAMENTAL U(1)_Y
rep of its (V_12, V_13) sector, modulo Yukawa singlet pairing.'

This bridges (R1b-i) and (R1b-ii):
  (R1b-i)  The cascade U(1)_Y unit = 1/(2 N_c) in SM units
           IS the fundamental unit of the (3,2) sector.
  (R1b-ii) Q_L sits at +/- 1 sector-fundamental unit.

WHY CASCADE-NATIVE
==================
The principle extends Part IVa rem:fund-or-trivial from individual
gauge groups (matter at fundamental of SU(3), SU(2)) to the
combined gauge structure: matter at fundamental of EACH (V_12,
V_13)-sectorial U(1)_Y rep.

Specifically: U(1)_Y commutes with SU(3) and SU(2), so its rep on
matter has a PER-SECTOR structure.  The fundamental rep of each
sector is the smallest non-zero allowed charge in that sector.

WHAT THIS SCRIPT DELIVERS
=========================
1. Defines sector-dependent fundamental U(1)_Y units cascade-natively.
2. Verifies SM Y values match 'fundamental of sector' for 5/6 matter
   types.
3. Identifies u_R as Yukawa-forced outlier (= 2 sector units, not 1).
4. Articulates the cascade-native principle bridging (R1b-i) + (R1b-ii).
5. Closes (R1b) MODULO the structural extension of fund-or-trivial
   to U(1)_Y per-sector reps.
"""

from __future__ import annotations

import sys
from fractions import Fraction


def report_setup():
    print("=" * 78)
    print("(R1b) DEEPER ATTACK: sector-dependent fundamental U(1)_Y rep")
    print("=" * 78)
    print()
    print("Sectors are defined by (V_12 dim, V_13 dim).  Each sector has a")
    print("fundamental U(1)_Y unit = 1 / (V_12 dim * V_13 dim) in SM units.")
    print()
    print("Sector fundamental units:")
    print()
    sectors = [
        ((3, 2), Fraction(1, 6)),
        ((3, 1), Fraction(1, 3)),
        ((1, 2), Fraction(1, 2)),
        ((1, 1), Fraction(1, 1)),
    ]
    print(f"  {'sector':>10s}  {'fundamental unit':>20s}  matter types")
    matter_in_sector = {
        (3, 2): "Q_L",
        (3, 1): "u_R, d_R",
        (1, 2): "L_L, H",
        (1, 1): "e_R",
    }
    for sect, unit in sectors:
        print(f"  ({sect[0]}, {sect[1]}){'':>4s}  {str(unit):>20s}  "
              f"{matter_in_sector[sect]}")
    print()


def verify_fundamental_assignments():
    print("=" * 78)
    print("CHECK: SM Y values vs 'fundamental of sector'")
    print("=" * 78)
    print()
    rows = [
        # (name, V_12, V_13, Y_SM)
        ("Q_L",   3, 2, Fraction(1, 6)),
        ("u_R",   3, 1, Fraction(2, 3)),
        ("d_R",   3, 1, Fraction(-1, 3)),
        ("L_L",   1, 2, Fraction(-1, 2)),
        ("e_R",   1, 1, Fraction(-1, 1)),
        ("H",     1, 2, Fraction(1, 2)),
    ]
    print(f"  {'particle':>8s}  {'sector':>8s}  {'Y_SM':>8s}  "
          f"{'unit':>8s}  {'Y/unit':>8s}  fundamental?")
    fundamental_count = 0
    outlier_list = []
    for name, v12, v13, Y in rows:
        unit = Fraction(1, v12 * v13)
        ratio = Y / unit
        is_fund = abs(ratio) == 1
        if is_fund:
            fundamental_count += 1
        else:
            outlier_list.append((name, ratio))
        sect_str = f"({v12},{v13})"
        ratio_str = ("+" if ratio > 0 else "") + str(ratio)
        print(f"  {name:>8s}  {sect_str:>8s}  {str(Y):>8s}  "
              f"{str(unit):>8s}  {ratio_str:>8s}  "
              f"{'YES' if is_fund else 'NO (= ' + ratio_str + ' units)'}")
    print()
    print(f"Fundamental of sector: {fundamental_count}/{len(rows)} particles ✓")
    print(f"Outliers: {outlier_list}")
    print()
    return outlier_list


def explain_outlier(outlier_list):
    print("=" * 78)
    print("OUTLIER ANALYSIS: u_R via Yukawa singlet")
    print("=" * 78)
    print()
    print("u_R sits at +2 sector-fundamental units (= +2/3 SM), NOT +1.")
    print()
    print("Cascade-internal reason: Yukawa singlet condition.  u_R is the")
    print("Yukawa partner of Q_L via tilde H:")
    print()
    print("  bar Q_L tilde H u_R  must be SU(2) x U(1)_Y invariant:")
    print("    -Y_QL - Y_H_conj + Y_uR = 0")
    print("    Y_uR = Y_QL + Y_H  (with Y_H_conj = -Y_H by tilde)")
    print()
    print("  Plug in Y_QL = +1/6 (fundamental of (3,2)) + Y_H = +1/2 ((R1a) closed):")
    print(f"    Y_uR = +1/6 + 1/2 = {Fraction(1,6) + Fraction(1,2)}")
    print()
    print("  In (3,1) sector units: Y_uR / (1/3) = +2/3 / (1/3) = 2.")
    print("  u_R is at 2 sector-fundamental units, FORCED by Yukawa pairing.")
    print()
    print("The other Yukawa-paired matter:")
    print()
    print("  d_R: bar Q_L H d_R -> Y_dR = Y_QL - Y_H = 1/6 - 1/2 = -1/3 = -1 unit ✓")
    print("       (d_R IS at fundamental of (3,1))")
    print()
    print("  e_R: bar L_L H e_R -> Y_eR = Y_LL - Y_H = -1/2 - 1/2 = -1 = -1 unit ✓")
    print("       (e_R IS at fundamental of (1,1))")
    print()
    print("Why is u_R special?  Because tilde H (Y = -Y_H = -1/2) gives the")
    print("OPPOSITE sign in the Yukawa: Y_uR = Y_QL - (-Y_H) = Y_QL + Y_H,")
    print("ADDING magnitudes rather than subtracting.")
    print()
    print("Mechanism: Y_QL and Y_H have the SAME sign (R1c closure), so:")
    print("  bar Q_L H d_R    -> Y_dR = Y_QL - Y_H  (subtracts: 1/6 - 1/2 = -1/3)")
    print("  bar Q_L tilde H u_R -> Y_uR = Y_QL + Y_H  (adds:    1/6 + 1/2 = 2/3)")
    print("  bar L_L H e_R    -> Y_eR = Y_LL - Y_H  (Y_LL = -1/2, sub: -1/2 - 1/2 = -1)")
    print()
    print("u_R is the unique combination Y_QL + Y_H (rather than Y_QL - Y_H),")
    print("hence at higher rep magnitude.")
    print()


def cascade_native_principle():
    print("=" * 78)
    print("CASCADE-NATIVE PRINCIPLE: bridges (R1b-i) and (R1b-ii)")
    print("=" * 78)
    print()
    print("PRINCIPLE: 'Matter at the cascade gauge window occupies the")
    print("fundamental U(1)_Y rep of its (V_12, V_13) SECTOR, modulo Yukawa")
    print("singlet pairing.'")
    print()
    print("CASCADE-NATIVE BACKING")
    print("======================")
    print("This extends Part IVa rem:fund-or-trivial from individual gauge")
    print("groups to the combined SU(3) x SU(2) x U(1)_Y structure:")
    print()
    print("  - rem:fund-or-trivial: V_12 in {1, 3} of SU(3), V_13 in {1, 2}")
    print("    of SU(2).  Matter is at FUNDAMENTAL or TRIVIAL.")
    print()
    print("  - Extension: V_14 (U(1)_Y rep) is at the FUNDAMENTAL of the")
    print("    SECTORIAL U(1)_Y, where the fundamental unit is sector-dependent.")
    print()
    print("Why sector-dependent?  U(1)_Y commutes with SU(3) and SU(2), so")
    print("its action on matter has a per-sector structure.  The 'natural")
    print("smallest charge' for matter in (V_12, V_13)-sector is 1/(V_12 dim")
    print("* V_13 dim) -- the FRACTIONAL CASCADE UNIT scaled by sector dimension.")
    print()
    print("WHAT THIS PRINCIPLE EARNS")
    print("==========================")
    print("(R1b-i) bridge: cascade U(1)_Y unit IS the sectorial fundamental.")
    print("        For (3, 2) sector: unit = 1/(2 N_c) = 1/6 in SM units.")
    print()
    print("(R1b-ii) bridge: Q_L sits at fundamental of (3, 2) sector =")
    print("         +/- 1 sector unit = +/- 1/6 SM.")
    print()
    print("Combined: |Y_QL| = 1/6 cascade-natively, MODULO the structural")
    print("extension of fund-or-trivial to U(1)_Y per-sector reps.")
    print()
    print("RESIDUAL")
    print("========")
    print("The 'extend fund-or-trivial to U(1)_Y per-sector' is the")
    print("structural step.  It's analogous to rem:fund-or-trivial but")
    print("applied to the U(1)_Y x (V_12 x V_13) combined structure.")
    print()
    print("This residual is structurally specific and cascade-natively")
    print("plausible.  Closing it would require a Part IVa extension of")
    print("rem:fund-or-trivial to include U(1)_Y per-sector reps.")
    print()


def report_status():
    print("=" * 78)
    print("(R1b) STATUS AFTER THIS DEEPER DIG")
    print("=" * 78)
    print()
    print("(R1b) sharpened to a single structural target:")
    print()
    print("  EXTENDED FUND-OR-TRIVIAL: matter at the cascade gauge window")
    print("  occupies the fundamental U(1)_Y rep of its (V_12, V_13)")
    print("  SECTOR, modulo Yukawa singlet pairing which may push some")
    print("  particles to higher integer multiples.")
    print()
    print("Verified against SM:")
    print("  - 5/6 particles (Q_L, d_R, L_L, e_R, H) at fundamental of sector ✓")
    print("  - 1/6 particle (u_R) at +2 sector units, FORCED by Yukawa")
    print("    singlet bar Q_L tilde H u_R.")
    print()
    print("Cascade-native source: extension of Part IVa rem:fund-or-trivial.")
    print()
    print("UPDATED Y-SPECTRUM CHAIN")
    print("=========================")
    print("  matter-rep gap (CLAUDE.md, original)")
    print("    -> (R1), DECOMPOSED:")
    print("       (R1a) |Y_H|  = 1/2  [CLOSED via Higgs vacuum + Z_2]")
    print("       (R1b) |Y_QL| = 1/6  [SHARPENED to extended fund-or-trivial]")
    print("       (R1c) sign relation [CLOSED via hemisphere correlation]")
    print("    -> sign anchor: observer-hemisphere on S^4  [REFRAMED]")
    print()
    print("(R1b) is now reduced to ONE structural target: extending")
    print("rem:fund-or-trivial to U(1)_Y per-sector reps, plus the")
    print("Yukawa-singlet outlier mechanism for u_R.")
    print()
    print("WHAT THIS COMMIT EARNS")
    print("=======================")
    print("- Identifies cascade-native principle that bridges (R1b-i) and")
    print("  (R1b-ii) simultaneously.")
    print("- Shows 5/6 SM particles satisfy the principle exactly.")
    print("- Explains u_R as Yukawa-forced outlier, not principle violation.")
    print("- Reduces (R1b) to one structural extension (per-sector U(1)_Y")
    print("  fund-or-trivial), plausible cascade-natively.")
    print()
    print("WHAT THIS COMMIT DOES NOT DO")
    print("=============================")
    print("- Close the structural extension of rem:fund-or-trivial to")
    print("  per-sector U(1)_Y reps.  That's a Part IVa write-up step")
    print("  if the principle is accepted as cascade-native.")
    print("- Reopen any closed pieces.")
    print()


def main() -> int:
    print("=" * 78)
    print("(R1b) DEEPER DIG: sector-dependent fundamental U(1)_Y rep")
    print("=" * 78)
    print()
    report_setup()
    outliers = verify_fundamental_assignments()
    explain_outlier(outliers)
    cascade_native_principle()
    report_status()
    return 0


if __name__ == "__main__":
    sys.exit(main())
