#!/usr/bin/env python3
"""
Cascade Y trace identity: Y_H = N_c * Y_QL as a path-tensor consistency
condition (potential closure of ANGLE A).

CONTEXT
=======
Commit 6ce655e (path-tensor consistency) reduced the Y-spectrum closure
to deriving cascade-native integer Q numerators (or equivalently Y_H).

This script identifies a STRIKING STRUCTURAL RELATION in the SM Y
spectrum that may be cascade-native, and articulates it as a candidate
path-tensor trace identity.

THE OBSERVATION
===============
In the SM, the following relations hold among Y values:

    Y_H  =  +1/2
    Y_QL =  +1/6
    Y_LL =  -1/2
    Y_uRc = -2/3   (= -Y_QL - Y_H, from Yukawa)
    Y_dRc = +1/3   (= -Y_QL + Y_H, from Yukawa)
    Y_eRc = +1     (= -Y_LL + Y_H, from Yukawa)

Two structural relations appear:

    (R1)  Y_H = N_c * Y_QL                  [Y_H = 3 * 1/6 = 1/2 ✓]
    (R2)  Y_LL = -Y_H                       [Y_LL = -1/2 ✓]

Combined with the cascade-native fractional units (Y in 1/(2 N_c) =
1/6 for color-charged matter, 1/2 for color-singlets) and the smallest-
magnitude principle (smallest non-zero numerator), these two relations
PIN the Y spectrum modulo signs.

CANDIDATE CASCADE-NATIVE READING
=================================
Both relations are reformulated as path-tensor trace identities at
the gauge window:

    (R1)  Y_H = tr_{V_12 = 3} (Y) = sum over color of Y per color slot
                                  = N_c * (Y per color slot)
                                  = N_c * Y_QL

          INTERPRETATION: the Higgs's V_{14} weight (Y_H) equals the
          trace over the SU(3) fundamental's 3 color slots of the
          quark doublet's V_{14} weight (Y_QL).  This is what 'integrating
          over color' looks like cascade-natively.

    (R2)  Y_LL = -Y_H

          INTERPRETATION: the lepton doublet's Y is minus the Higgs's
          Y.  This emerges from the requirement that the Higgs Yukawa
          for charged leptons (bar L_L H e_R) be SU(2)xU(1)-invariant
          and consistent with the cascade's 'electron has integer Q'
          structure.  Equivalently: Y_H + Y_LL = 0 is the reduced form
          of the gravitational anomaly after substituting Yukawa
          relations (a multi-particle constraint).

WHAT THIS SCRIPT DELIVERS
=========================
1. Verifies (R1) and (R2) hold in the SM Y spectrum exactly.
2. Articulates the cascade-native trace-identity reading.
3. Shows that (R1) + (R2) + cascade fractional structure + smallest-
   magnitude principle PIN the SM Y spectrum modulo signs.
4. Identifies the residual: cascade-native derivation of (R1) from
   path-tensor consistency over the SU(3) trace.

WHAT THIS SCRIPT DOES NOT DO
============================
- Derive (R1) cascade-natively.  It identifies (R1) as the candidate
  structural identity and the path forward.
- Pin signs.  Smallest-magnitude principle gives |Y_QL| = 1/6 but
  not Y_QL = +1/6 specifically.  Sign determination is residual to
  this dig.

CHAIN OF REDUCTIONS (CURRENT STATE)
====================================
  matter-rep gap (CLAUDE.md, original)
    -> oq:fermion-gauge-action (ab4e1ed)
    -> path-tensor consistency (3dec8a5)
    -> cascade-native integer Q numerators (6ce655e)
    -> cascade-native (R1) Y_H = N_c * Y_QL trace identity
       (THIS COMMIT, partial -- identifies candidate, doesn't close)
"""

from __future__ import annotations

import sys
from fractions import Fraction


# ---------------------------------------------------------------------------
# SM Y values (LH Weyl convention, with Higgs)
# ---------------------------------------------------------------------------

SM_Y = {
    "Q_L":   Fraction(1, 6),
    "u_R^c": Fraction(-2, 3),  # conjugate of u_R
    "d_R^c": Fraction(1, 3),
    "L_L":   Fraction(-1, 2),
    "e_R^c": Fraction(1, 1),
    "H":     Fraction(1, 2),
}

# SU(3), SU(2) reps (fundamental dim) and multiplicity n_i = SU(3) * SU(2)
SM_REPS = {
    "Q_L":   (3, 2),  # quark doublet
    "u_R^c": (3, 1),  # quark singlet
    "d_R^c": (3, 1),
    "L_L":   (1, 2),
    "e_R^c": (1, 1),
    "H":     (1, 2),  # Higgs, for reference
}


# ---------------------------------------------------------------------------
# Step 1: verify the SM trace relations
# ---------------------------------------------------------------------------

def verify_relations():
    print("=" * 78)
    print("STEP 1: verify candidate trace relations in SM Y spectrum")
    print("=" * 78)
    print()

    Y_H  = SM_Y["H"]
    Y_QL = SM_Y["Q_L"]
    Y_LL = SM_Y["L_L"]
    N_c  = 3

    print(f"  SM values (LH Weyl):")
    print(f"    Y_H  = {Y_H}")
    print(f"    Y_QL = {Y_QL}")
    print(f"    Y_LL = {Y_LL}")
    print(f"    N_c  = {N_c}")
    print()

    # Relation R1: Y_H = N_c * Y_QL
    print("  (R1)  Y_H = N_c * Y_QL")
    LHS = Y_H
    RHS = N_c * Y_QL
    print(f"        LHS = {LHS}")
    print(f"        RHS = {N_c} * {Y_QL} = {RHS}")
    print(f"        Match: {LHS == RHS}")
    print()

    # Relation R2: Y_LL = -Y_H
    print("  (R2)  Y_LL = -Y_H")
    LHS = Y_LL
    RHS = -Y_H
    print(f"        LHS = {LHS}")
    print(f"        RHS = -{Y_H} = {RHS}")
    print(f"        Match: {LHS == RHS}")
    print()

    # Derived: Y_LL = -N_c * Y_QL (from R1 + R2)
    print("  (R1+R2 derived)  Y_LL = -N_c * Y_QL")
    LHS = Y_LL
    RHS = -N_c * Y_QL
    print(f"        LHS = {LHS}")
    print(f"        RHS = -{N_c} * {Y_QL} = {RHS}")
    print(f"        Match: {LHS == RHS}")
    print()


# ---------------------------------------------------------------------------
# Step 2: gravitational anomaly reduces to (R1) + (R2) given Yukawa singlet
# ---------------------------------------------------------------------------

def derive_grav_anomaly_reduces_to_R1_R2():
    print("=" * 78)
    print("STEP 2: gravitational anomaly reduces to (R1) + (R2) given Yukawa")
    print("=" * 78)
    print()
    print("SM gravitational x U(1)_Y anomaly: sum_i n_i Y_i = 0,")
    print("where i runs over LH Weyl per generation.")
    print()
    print("Substitute Yukawa singlet conditions (cascade-native: Higgs Yukawa")
    print("must be SU(2) x U(1)-invariant):")
    print("    Y_uRc = -Y_QL - Y_H")
    print("    Y_dRc = -Y_QL + Y_H")
    print("    Y_eRc = -Y_LL + Y_H")
    print()
    print("Plug into the anomaly sum:")
    print("    6 Y_QL + 3 Y_uRc + 3 Y_dRc + 2 Y_LL + Y_eRc = 0")
    print("  = 6 Y_QL + 3(-Y_QL - Y_H) + 3(-Y_QL + Y_H) + 2 Y_LL + (-Y_LL + Y_H)")
    print("  = 6 Y_QL - 3 Y_QL - 3 Y_H - 3 Y_QL + 3 Y_H + 2 Y_LL - Y_LL + Y_H")
    print("  = 0 * Y_QL + Y_H + Y_LL = 0")
    print()
    print("Therefore: gravitational anomaly + Yukawa singlet  <=>  Y_H + Y_LL = 0")
    print("                                                  <=>  (R2)")
    print()
    print("Verify numerically with SM values:")
    Y_QL  = SM_Y["Q_L"]
    Y_uRc = SM_Y["u_R^c"]
    Y_dRc = SM_Y["d_R^c"]
    Y_LL  = SM_Y["L_L"]
    Y_eRc = SM_Y["e_R^c"]
    Y_H   = SM_Y["H"]

    grav = 6 * Y_QL + 3 * Y_uRc + 3 * Y_dRc + 2 * Y_LL + Y_eRc
    yukawa_check_uRc = Y_uRc - (-Y_QL - Y_H)
    yukawa_check_dRc = Y_dRc - (-Y_QL + Y_H)
    yukawa_check_eRc = Y_eRc - (-Y_LL + Y_H)
    R2 = Y_H + Y_LL

    print(f"    grav anomaly sum n_i Y_i = {grav}")
    print(f"    Yukawa check (uRc):  Y_uRc - (-Y_QL - Y_H) = {yukawa_check_uRc}")
    print(f"    Yukawa check (dRc):  Y_dRc - (-Y_QL + Y_H) = {yukawa_check_dRc}")
    print(f"    Yukawa check (eRc):  Y_eRc - (-Y_LL + Y_H) = {yukawa_check_eRc}")
    print(f"    (R2) Y_H + Y_LL = {R2}")
    print()
    print("All zero: gravitational anomaly + Yukawa singlet = (R2) is exact.")
    print()


# ---------------------------------------------------------------------------
# Step 3: structural reading of (R1) as path-tensor trace identity
# ---------------------------------------------------------------------------

def report_R1_trace_reading():
    print("=" * 78)
    print("STEP 3: structural reading of (R1) Y_H = N_c * Y_QL")
    print("=" * 78)
    print()
    print("Path-tensor structure (Part IVa rem:path-tensor):")
    print("  Each particle has rep content V_12 x V_13 x V_14 in the gauge window.")
    print("  Q_L:  V_12 = 3 (color triplet),  V_13 = 2 (SU(2) doublet),  V_14 weight Y_QL")
    print("  H:    V_12 = 1 (color singlet),  V_13 = 2 (SU(2) doublet),  V_14 weight Y_H")
    print()
    print("Both Q_L and H are V_13 = 2 (SU(2) doublets) at d=13.  They differ")
    print("at d=12: Q_L is color-triplet (V_12 = 3); H is color-singlet (V_12 = 1).")
    print()
    print("CANDIDATE TRACE IDENTITY (cascade-native):")
    print("------------------------------------------")
    print("The U(1)_Y weight at d=14 of a path-tensor with V_12 = 1 component")
    print("equals the TRACE over the V_12 = 3 cascade space of the U(1)_Y weight")
    print("of a path-tensor with V_12 = 3 component.  Symbolically:")
    print()
    print("    Y(V_12 = 1)  =  tr_{V_12 = 3} (Y per color slot)")
    print("                =  sum over 3 color slots of Y_QL")
    print("                =  N_c * Y_QL")
    print()
    print("Cascade-native motivation: V_12 = 1 (color singlet) is the cascade")
    print("'sum' over V_12 = 3's three color slots (the SU(3)-trivial direction")
    print("in H^3 = R^12).  When U(1)_Y acts at d=14 on the full path tensor,")
    print("the V_12 = 1 weight collects contributions from all 3 color slots,")
    print("each weighted by Y_QL.  Total: N_c * Y_QL.")
    print()
    print("This is the cascade-native form of 'tracing over color' that arises")
    print("naturally in the gauge-coupled fermion action's V_12 reduction.")
    print()
    print("STATUS: cascade-native interpretation, NOT yet derived from a")
    print("structural theorem.  Closure would require formalising 'V_12 = 1")
    print("is the trace over V_12 = 3' as a cascade theorem on the H^3 = R^12")
    print("structure.")
    print()


# ---------------------------------------------------------------------------
# Step 4: pinning the SM Y spectrum modulo signs
# ---------------------------------------------------------------------------

def pin_y_spectrum_modulo_signs():
    print("=" * 78)
    print("STEP 4: (R1) + (R2) + cascade structure pins Y modulo signs")
    print("=" * 78)
    print()
    print("Cascade-native constraints (assumed derivable):")
    print("  - Y_QL in (1/6) Z (from N_c=3 + SU(2) doublet structure)")
    print("  - Y_LL in (1/2) Z (from color-singlet + SU(2) doublet)")
    print("  - |Y_QL| smallest non-zero -> |Y_QL| = 1/6")
    print("  - |Y_LL| smallest non-zero -> |Y_LL| = 1/2")
    print()
    print("Apply (R1) Y_H = N_c * Y_QL:")
    print("  - |Y_H| = N_c * |Y_QL| = 3 * 1/6 = 1/2")
    print("  - sign(Y_H) = sign(Y_QL)")
    print()
    print("Apply (R2) Y_LL = -Y_H:")
    print("  - |Y_LL| = |Y_H| = 1/2  (consistent with smallest-magnitude)")
    print("  - sign(Y_LL) = -sign(Y_H) = -sign(Y_QL)")
    print()
    print("Apply Yukawa singlet conditions:")
    print("  Y_uRc = -Y_QL - Y_H = -Y_QL - N_c Y_QL = -(N_c + 1) Y_QL")
    print("  Y_dRc = -Y_QL + Y_H = -Y_QL + N_c Y_QL = (N_c - 1) Y_QL")
    print("  Y_eRc = -Y_LL + Y_H = Y_H + Y_H = 2 Y_H = 2 N_c Y_QL")
    print()
    print("With N_c = 3:")
    print("  Y_uRc = -4 Y_QL")
    print("  Y_dRc = +2 Y_QL")
    print("  Y_eRc = +6 Y_QL")
    print()
    print("Substitute Y_QL = +1/6:")
    Y_QL = Fraction(1, 6)
    N_c = 3
    Y_H   = N_c * Y_QL
    Y_LL  = -Y_H
    Y_uRc = -(N_c + 1) * Y_QL
    Y_dRc = (N_c - 1) * Y_QL
    Y_eRc = 2 * N_c * Y_QL
    print(f"  Y_QL  = {Y_QL}")
    print(f"  Y_H   = {Y_H}")
    print(f"  Y_LL  = {Y_LL}")
    print(f"  Y_uRc = {Y_uRc}")
    print(f"  Y_dRc = {Y_dRc}")
    print(f"  Y_eRc = {Y_eRc}")
    print()
    print("Compare to SM:")
    for key in ["Q_L", "H", "L_L", "u_R^c", "d_R^c", "e_R^c"]:
        derived = {"Q_L": Y_QL, "H": Y_H, "L_L": Y_LL,
                   "u_R^c": Y_uRc, "d_R^c": Y_dRc, "e_R^c": Y_eRc}[key]
        sm = SM_Y[key]
        match = derived == sm
        print(f"  {key:6s}  derived = {str(derived):>6s}  SM = {str(sm):>6s}  "
              f"{'MATCH' if match else 'MISMATCH'}")
    print()
    print("ALL SIX SM Y VALUES are derived from:")
    print("  - Cascade fractional structure (1/6 units for color-charged,")
    print("    1/2 units for color-singlets).")
    print("  - Smallest-magnitude: |Y_QL| = 1/6, |Y_LL| = 1/2.")
    print("  - Trace identity (R1): Y_H = N_c * Y_QL.")
    print("  - Reduced gravitational anomaly (R2): Y_LL = -Y_H.")
    print("  - Yukawa singlet conditions (SU(2)xU(1)-invariance of bar Q_L H u_R etc).")
    print("  - Sign convention: Y_QL > 0 (the open piece below).")
    print()


# ---------------------------------------------------------------------------
# Step 5: residual -- the sign of Y_QL
# ---------------------------------------------------------------------------

def report_residual_sign():
    print("=" * 78)
    print("STEP 5: residual after this dig -- sign of Y_QL")
    print("=" * 78)
    print()
    print("Steps 1-4 establish that with (R1), (R2), cascade fractional")
    print("structure, smallest-magnitude principle, and Yukawa singlet")
    print("conditions, the SM Y spectrum is determined modulo overall sign.")
    print()
    print("THE TWO POSSIBILITIES (sign(Y_QL) = +1 or -1):")
    print()
    print("  Sign(Y_QL) = +1  ->  SM convention (Y_QL = +1/6, ..., Y_eRc = +1)")
    print("  Sign(Y_QL) = -1  ->  conjugated SM (Y_QL = -1/6, ..., Y_eRc = -1)")
    print()
    print("These two are PHYSICALLY DISTINCT in CP-violating contexts but")
    print("are CONNECTED by complex conjugation in the cascade (which flips")
    print("the SIGN of the U(1)_Y phase).  In the cascade picture, the choice")
    print("of sign corresponds to:")
    print()
    print("  - The orientation of the Higgs vacuum in the SU(2)_L doublet")
    print("    (T_3 = +1/2 or T_3 = -1/2 component).")
    print("  - The sign convention of J at d=14 (J vs -J; either gives a")
    print("    valid cascade complex structure).")
    print()
    print("CASCADE-NATIVE SIGN PINNING (open):")
    print("  The cascade has chirality structure at d=13 (Spin(12)-Weyl_- vs")
    print("  Weyl_+, with PR #108's chirality split distinguishing the two).")
    print("  The Higgs's vacuum-direction component (T_3 sign) might be")
    print("  pinned by the d=13 chirality structure, which would in turn pin")
    print("  Y_QL > 0.  This is open.")
    print()


# ---------------------------------------------------------------------------
# Step 6: chain of reductions and what remains
# ---------------------------------------------------------------------------

def report_final_chain():
    print("=" * 78)
    print("STEP 6: chain of reductions and the current bottleneck")
    print("=" * 78)
    print()
    print("Updated chain:")
    print()
    print("  matter-rep gap (CLAUDE.md, original)")
    print("    -> oq:fermion-gauge-action")
    print("    -> path-tensor consistency")
    print("    -> cascade-native integer Q numerators")
    print("    -> two structural relations:")
    print("       (R1) Y_H = N_c * Y_QL  (path-tensor color trace, candidate)")
    print("       (R2) Y_LL = -Y_H  (gravitational anomaly + Yukawa, derivable)")
    print("    -> [THIS DIG] sign of Y_QL  (cascade chirality at d=13?)")
    print()
    print("CURRENT BOTTLENECK (after this dig):")
    print()
    print("  1. Derive (R1) cascade-natively: 'V_12 = 1 weight is the trace")
    print("     over V_12 = 3 of the V_12 = 3 weight'.  This is a structural")
    print("     theorem on H^3 = R^12 + U(1)_Y representations.")
    print()
    print("  2. Pin sign(Y_QL) cascade-natively (chirality at d=13 + Higgs")
    print("     vacuum direction).")
    print()
    print("Closing both would derive the SM Y spectrum from cascade primitives,")
    print("closing the matter-rep gap of CLAUDE.md.")
    print()
    print("Each of (1) and (2) is structurally specific and tractable.  The")
    print("chain has reduced from 'derive 5-6 free Y values' to 'derive ONE")
    print("structural trace identity + ONE sign'.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE Y TRACE IDENTITY: Y_H = N_c * Y_QL as path-tensor consistency")
    print("=" * 78)
    print()
    verify_relations()
    derive_grav_anomaly_reduces_to_R1_R2()
    report_R1_trace_reading()
    pin_y_spectrum_modulo_signs()
    report_residual_sign()
    report_final_chain()
    return 0


if __name__ == "__main__":
    sys.exit(main())
