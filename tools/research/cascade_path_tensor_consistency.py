#!/usr/bin/env python3
"""
Path-tensor consistency at the gauge window: cascade-native Q = T_3 + Y
and the path-tensor angle on the Y spectrum (one of several converging
routes; see STATUS below).

STATUS (April 2026 update): SUPERSEDED at the Y-spectrum closure level
=====================================================================
This script's "Step 3 / Step 5" framing --- which presents the specific
integer numerators of SM electric charges as the current Y-spectrum
bottleneck --- is STALE.  The Y spectrum is now closed at the
magnitude + sign level cascade-natively, via converging routes
documented in Part IVa rem:y-spectrum-open and CLAUDE.md
"Y spectrum --- CLOSED at the magnitude + sign level":

  - (R1a) |Y_H| = 1/2: closed via sector-fundamental in (1, 2) per
    Part IVb thm:sector-fundamental-y; independently via Higgs vacuum
    neutrality + SU(2) doublet structure.
  - (R1b) |Y_QL| = 1/6: closed via the gauge-centre-quotient mechanism
    of Part IVb thm:sector-fundamental-y.  The cascade gauge centres
    Z_3 (SU(3)) and Z_2 (SU(2)) act on path-tensor matter; the unique
    diagonal Z_6 subgroup of SU(3) x SU(2) x U(1)_Y acting trivially
    on every cascade matter sector forces the effective gauge group
    to G_cw / Z_6.  U(1)_Y charges in the (V_12, V_13)-sector are
    quantised in units of 1 / (dim V_12 . dim V_13); the smallest
    non-trivial |Y| in each sector is the sector-fundamental.
  - (R1c) sign(Y_H) = sign(Y_QL): closed via hemisphere-sign
    consistency (vacuum neutrality + Yukawa structure + hemisphere
    swap flips both signs together).
  - (R1) Y_H = N_c . Y_QL: automatic from (R1a)+(R1b)+(R1c) as a
    sector-dimension ratio (NOT a path-tensor color trace).
  - Smallest-magnitude principle: k=+/- 1 for Q_L, d_R, L_L, e_R, H
    (smallest non-trivial irrep of U(1)_Y / Z_n via extended
    fund-or-trivial); k=+/- 2 for u_R forced by Yukawa singlet
    Y_uR = Y_QL + Y_H.
  - Basin-label sign anchor: STRUCTURALLY RESOLVED on the S^4 shell
    at d_V = 5 via Part IVb thm:chirality-factorisation +
    rem:cpt-balance-basins.  Two CPT-conjugate basins of equal area;
    each observer relationally central in their own basin; the choice
    between {Y_QL = +1/6, Y_QL = -1/6} is a labeling convention with
    ZERO observational content, at parity with the SM's Q_e = -1
    convention.

This script's path-tensor-consistency angle remains a valid
contributing argument: it derives Q = T_3 + Y from the Higgs
mechanism + thm:weinberg cascade-natively, and isolates the
denominator structure plus within-multiplet differences that the
sector-fundamental theorem subsequently combines with the
fund-or-trivial smallest-magnitude principle to fix the integer
numerators.  But the specific integer numerators are NOT the open
bottleneck.

CURRENT OPEN DYNAMICS-RELATED ITEMS (the actual remaining work):
  - 1/alpha_em screening: 6 pi = 3 . N(0) . Gamma(1/2)^2 per
    generation identified by target-matching (Part IVb
    oq:alpha-em-screening), not yet derived from the photon
    self-energy on the cascade lattice.
  - SU(2)_L parity-violation structure: Part IVa S2.3 explicitly
    defers this to the gauge-coupled fermion action
    (oq:fermion-gauge-action item c).
  - Multi-layer hopping term in the proposed gauge-coupled fermion
    action: per-layer pieces verified at A=0; layer-coupling that
    reproduces thm:forced-paths' descent attenuation is open.
  - Cascade analogue of PMNS / solar splitting: heaviest neutrino
    mass closes; lighter two too small under single-source diagonal
    form, suggesting an inter-generation mixing analogue of PMNS
    is needed.

ORIGINAL CONTEXT (preserved as historical record below)
========================================================
Commit 3dec8a5 (per-layer locality of the cascade fermion) reframed
the Y-spectrum closure from QFT triangle anomalies to PATH-TENSOR
CONSISTENCY: the multi-layer gauge transformation
U(1)_Y x SU(2) x SU(3) acting on a single particle's path tensor
V_{12} otimes V_{13} otimes V_{14} must close consistently.

This script digs into path-tensor consistency:
  1. Articulates the explicit cascade-native consistency condition
     after EW symmetry breaking at d=13.
  2. Derives Q = T_3 + Y as a cascade-native relation (NOT a
     definition) from the cascade's Higgs mechanism + thm:weinberg.
  3. Identifies N_c = 3 cascade fractional unit (Q in 1/3 units for
     color-triplets) cascade-natively.
  4. Identifies the SU(2) doublet structure pinning Q_u - Q_d = 1 etc.
  5. (At time of writing) presented the specific integer numerators
     of SM electric charges as the residual bottleneck.  This framing
     is now SUPERSEDED --- see STATUS section above.

The script's Steps 1-4 remain valid as one route to the cascade-native
Q-spectrum structure; Step 5's "bottleneck" framing should be read
as the path-tensor-consistency-only picture, before the
sector-fundamental theorem closed the integer numerators via a
different mechanism.
"""

from __future__ import annotations

import sys
from fractions import Fraction


# ---------------------------------------------------------------------------
# Step 1: explicit cascade-native consistency condition
# ---------------------------------------------------------------------------

def report_consistency_condition():
    print("=" * 78)
    print("STEP 1: cascade-native path-tensor consistency condition")
    print("=" * 78)
    print()
    print("After EW symmetry breaking at d=13 (Part IVa thm:lefschetz on")
    print("S^12 + thm:breaking + thm:higgs), the cascade's gauge group")
    print("SU(2)_L x U(1)_Y restricts to the unbroken U(1)_em + a broken")
    print("(massive) Z and W^pm.  Cascade-native:")
    print()
    print("  - Higgs is the hairy-ball zero on S^12 at d=13.")
    print("  - Higgs VEV picks a vacuum direction in V_13 (SU(2) doublet).")
    print("  - The unbroken U(1)_em is the linear combination of")
    print("    SU(2)_L's T_3 and U(1)_Y's Y that annihilates the VEV.")
    print()
    print("  CASCADE-NATIVE PATH-TENSOR CONSISTENCY CONDITION:")
    print("  ---------------------------------------------------")
    print("  For a single particle with rep content (V_12, V_13, V_14) in")
    print("  the gauge window, the OBSERVER's electric charge Q is")
    print("    Q = T_3 + Y")
    print("  where T_3 is the SU(2)_L eigenvalue (at d=13) and Y is the")
    print("  U(1)_Y eigenvalue (V_14 weight at d=14).")
    print()
    print("  This is DERIVED, not assumed: it follows from the cascade's")
    print("  Higgs mechanism + thm:weinberg's diagonalisation of the")
    print("  (W^3, B) mass matrix.  The unbroken combination is fixed by")
    print("  the requirement that the Higgs VEV is electrically neutral.")
    print()


# ---------------------------------------------------------------------------
# Step 2: SM Q values + cascade-native pieces
# ---------------------------------------------------------------------------

def report_sm_q_cascade_pieces():
    print("=" * 78)
    print("STEP 2: SM Q values; cascade-native pieces of the puzzle")
    print("=" * 78)
    print()
    print("SM Q values per generation (LH Weyl convention):")
    print()
    table = [
        ("u_L",   3, 2, Fraction(2, 3),  Fraction(1, 2)),
        ("d_L",   3, 2, Fraction(-1, 3), Fraction(-1, 2)),
        ("u_L^c", 3, 1, Fraction(-2, 3), Fraction(0, 1)),
        ("d_L^c", 3, 1, Fraction(1, 3),  Fraction(0, 1)),
        ("nu_L",  1, 2, Fraction(0, 1),  Fraction(1, 2)),
        ("e_L",   1, 2, Fraction(-1, 1), Fraction(-1, 2)),
        ("e_L^c", 1, 1, Fraction(1, 1),  Fraction(0, 1)),
    ]
    print(f"  {'name':6s} {'V_12':>4s} {'V_13':>4s} {'Q':>8s} {'T_3':>8s} {'Y=Q-T_3':>10s}")
    for name, V12, V13, Q, T3 in table:
        Y = Q - T3
        print(f"  {name:6s} {V12:>4d} {V13:>4d} {str(Q):>8s} {str(T3):>8s} {str(Y):>10s}")
    print()
    print("Cascade-native pieces of the Q structure:")
    print()
    print("  (a) Cascade SU(3) at d=12 has N_c = 3 fundamental")
    print("      (Adams + H^3 = R^12).  Color-triplet quarks have")
    print("      charges in fractional units of 1/N_c = 1/3.")
    print("      Cascade-native CHARGE DENOMINATOR = 3 for triplets.")
    print()
    print("  (b) Cascade SU(2)_L doublet at d=13 has T_3 = +/- 1/2.")
    print("      Within a doublet (V_13 = 2), Q values differ by")
    print("      Delta T_3 = 1 (since Y is constant across the doublet).")
    print("      Q_u - Q_d = 1 ✓  (cascade: T_3(u) - T_3(d) = 1)")
    print("      Q_nu - Q_e = 1 ✓  (cascade: T_3(nu) - T_3(e) = 1)")
    print("      Cascade-native CHARGE DIFFERENCE within doublets = 1.")
    print()
    print("  (c) Cascade U(1)_Y at d=14 has J's eigenvalues +/- i,")
    print("      so the U(1) generator J|_{S^13} acts with charges +/- 1")
    print("      under exp(theta J).  Cascade-native U(1) FUNDAMENTAL")
    print("      UNIT = 1 (matches integer-unit electric charge for")
    print("      color-singlets).")
    print()


# ---------------------------------------------------------------------------
# Step 3: what this leaves for Y spectrum closure
# ---------------------------------------------------------------------------

def report_residual():
    print("=" * 78)
    print("STEP 3: the residual after path-tensor consistency")
    print("=" * 78)
    print()
    print("[NOTE: This step's 'residual' framing is SUPERSEDED at the")
    print("Y-spectrum closure level by Part IVb thm:sector-fundamental-y.")
    print("See module docstring STATUS section.  Below is the path-tensor-")
    print("consistency-only picture, preserved as a historical record of")
    print("one converging route.]")
    print()
    print("Path-tensor consistency + cascade pieces (a)-(c) determine:")
    print()
    print("  - The DENOMINATOR structure of Q (and hence Y):")
    print("      color-singlets: Q in 1/1 units (integers)")
    print("      color-triplets: Q in 1/3 units")
    print("      All Y values are in 1/(2 N_c) = 1/6 units (cascade-native).")
    print()
    print("  - The DIFFERENCES between Q values within each multiplet:")
    print("      Q_u - Q_d = 1 (within Q_L)")
    print("      Q_nu - Q_e = 1 (within L_L)")
    print()
    print("  - The relation Q = T_3 + Y for each particle.")
    print()
    print("WHAT IS NOT DETERMINED CASCADE-NATIVELY:")
    print()
    print("  The SPECIFIC INTEGER NUMERATORS in Q values:")
    print("    Q_u = +2/3 (numerator +2 in 1/3 units)")
    print("    Q_d = -1/3 (numerator -1 in 1/3 units)")
    print("    Q_e = -1   (numerator -1 in 1/1 units, or -3 in 1/3 units)")
    print("    Q_nu = 0")
    print()
    print("  The differences Q_u - Q_d = 1 = 3/3 and Q_e - Q_nu = -1 = -3/3")
    print("  are cascade-native (from SU(2) doublet structure), but the")
    print("  INDIVIDUAL Q values within each doublet are not pinned by")
    print("  these differences alone.")
    print()
    print("  Equivalently: we know Q_u = Q_d + 1, Q_nu = Q_e + 1, but we")
    print("  don't know Q_d (or Q_e) cascade-natively without additional")
    print("  input.")
    print()
    print("  The standard SM derivation pins the individual Q values via")
    print("  anomaly cancellation conditions on Y, but those conditions")
    print("  require a fermion path integral with derivative gauge")
    print("  couplings, which the cascade does NOT have (per-layer locality).")
    print()


# ---------------------------------------------------------------------------
# Step 4: cascade-native angles for closing the residual
# ---------------------------------------------------------------------------

def report_closure_angles():
    print("=" * 78)
    print("STEP 4: cascade-native angles for closing the residual")
    print("=" * 78)
    print()
    print("To pin the integer numerators in Q values, the cascade needs")
    print("ONE of the following cascade-internal mechanisms:")
    print()
    print("  ANGLE A: Higgs Y-charge pinned cascade-natively.")
    print("  --------")
    print("  In the SM, Y_Higgs = +1/2 (convention), giving Q_higgs = 0.")
    print("  Y-charges of matter follow from requiring the Higgs Yukawa")
    print("  couplings to be SU(2) x U(1)-invariant:")
    print("    Q_L (Y=+1/6) x H (Y=+1/2) -> u_R^c (Y=-2/3) requires")
    print("    Y_QL + Y_H + Y_uRc = 1/6 + 1/2 - 2/3 = 0 (singlet)  ✓")
    print("    Q_L x H_bar -> d_R^c requires")
    print("    Y_QL - Y_H + Y_dRc = 1/6 - 1/2 + 1/3 = 0  ✓")
    print("  If the cascade derives Y_H = +1/2 from the cascade Higgs's")
    print("  position in the (T_3, Y) plane, then the Yukawa-singlet")
    print("  conditions pin all matter Y values.")
    print("  Cascade structure: the Higgs is at d=13, position in V_13")
    print("  doublet x V_14 = 1 sector.  Cascade-native Y_H?  Open.")
    print()
    print("  ANGLE B: Path-tensor anomaly via tensor-product traces.")
    print("  --------")
    print("  Even without derivative gauge couplings, the path tensor")
    print("  V_12 otimes V_13 otimes V_14 has trace identities:")
    print("    tr(V_12) tr(V_13) tr(V_14) = 0  (gravitational anomaly)")
    print("    tr(T^a T^a) tr(V_13) tr(V_14) = 0  (SU(3)^2 anomaly)")
    print("    tr(V_12) tr(T^a T^a) tr(V_14) = 0  (SU(2)^2 anomaly)")
    print("    tr(V_12 V_13) Y^3 = 0  (Y^3 anomaly)")
    print("  These trace identities CAN be cascade-native if path-tensor")
    print("  consistency demands them as multi-particle conditions.  But")
    print("  the cascade's per-layer locality may prevent them: there is")
    print("  no multi-particle path integral.  Open: whether cascade-")
    print("  internal multi-particle consistency forces these traces.")
    print()
    print("  ANGLE C: J's spectrum at d=14 + chirality structure.")
    print("  --------")
    print("  J's eigenvalues are +/- i (uniformly).  After EW breaking,")
    print("  the photon's effective coupling to matter sees the COMBINATION")
    print("  T_3 + Y, not Y alone.  The integer numerators in Q might")
    print("  emerge from the specific way J's +/- 1 eigenvalues distribute")
    print("  over the chirality-factorised matter content (Part IVb")
    print("  thm:chirality-factorisation).  Open.")
    print()


# ---------------------------------------------------------------------------
# Step 5: status summary
# ---------------------------------------------------------------------------

def report_status():
    print("=" * 78)
    print("STEP 5: Y-spectrum gap status after this dig")
    print("=" * 78)
    print()
    print("[NOTE: The 'current bottleneck = integer Q numerators' framing")
    print("below is SUPERSEDED.  The Y spectrum is closed at the magnitude")
    print("+ sign level cascade-natively via Part IVb thm:sector-fundamental-y")
    print("(gauge-centre-quotient mechanism on path-tensor matter)")
    print("combined with the fund-or-trivial smallest-magnitude principle")
    print("and the basin-label structural resolution on the S^4 shell at")
    print("d_V = 5 (Part IVb thm:chirality-factorisation +")
    print("rem:cpt-balance-basins).  See module docstring STATUS section.")
    print("The chain below records the path-tensor-consistency angle as")
    print("of the time of writing, preserved for historical reference.]")
    print()
    print("Chain of reductions:")
    print()
    print("  matter-rep gap (CLAUDE.md, original)")
    print("    = 'specific reps + hypercharges imported from SM observation'")
    print()
    print("  -> Reduced to oq:fermion-gauge-action (commit ab4e1ed)")
    print("     'gauge-coupled fermion action open at d=14'")
    print()
    print("  -> Reduced to path-tensor consistency (commit 3dec8a5)")
    print("     'multi-layer gauge transformation closes on V_12 x V_13 x V_14'")
    print()
    print("  -> Reduced to cascade-native Q values (THIS COMMIT)")
    print("     'Q = T_3 + Y is cascade-derived; specific integer Q numerators")
    print("      remain open'")
    print()
    print("Each reduction is structurally specific.  The current bottleneck")
    print("is the most concrete it has been: derive cascade-natively the")
    print("integer numerators in SM electric charges, OR equivalently")
    print("derive Y_Higgs cascade-natively (closes via Yukawa singlet)")
    print("OR derive the path-tensor trace identities cascade-natively")
    print("(closes via anomaly-style traces).")
    print()
    print("WHAT EACH CASCADE LAYER NOW SUPPLIES:")
    print()
    print("  d=12 (SU(3)): N_c = 3 -> Q denominator = 3 for color-triplets.")
    print("  d=13 (SU(2)): T_3 = +/- 1/2 -> Q differences within doublets.")
    print("  d=14 (U(1)):  J eigenvalues +/- 1 -> Q fundamental unit = 1.")
    print("  d=13 Higgs:   EW breaking -> Q = T_3 + Y as derived relation.")
    print()
    print("WHAT REMAINS:")
    print()
    print("  Specific integer Q numerators (e.g. Q_u = +2/3, not -2/3 or 0).")
    print("  These are the SM-input pieces not yet derived cascade-natively.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE PATH-TENSOR CONSISTENCY: cascade-native Q = T_3 + Y")
    print("and the residual cascade-native Q-derivation question")
    print("=" * 78)
    print()
    report_consistency_condition()
    report_sm_q_cascade_pieces()
    report_residual()
    report_closure_angles()
    report_status()
    return 0


if __name__ == "__main__":
    sys.exit(main())
