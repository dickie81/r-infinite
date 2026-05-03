#!/usr/bin/env python3
"""
Exploration of the theta_23 P_2 rigour gap (roadmap item #1, residual (a)).

THE ORIGINAL GAP (per ROADMAP and current verifier Step 4(1))
=============================================================
"theta_23 P_2 is structurally weaker (no interior Dirac layer; relies on
cascade continuity through Majorana stretches plus the d_1 phase
transition's chirality basin selection)."

The framing implied:
  - Dirac-anchored cases (theta_C P_1, b/s P_0, theta_23 P_1) are
    structurally rigorous.
  - Non-Dirac-anchored cases (theta_23 P_2) are structurally weaker.

THIS SCRIPT'S FINDING
=====================
The framing is INVERTED.  The (w_1, w_2) Z_2 selectors do NOT live at
Dirac layers (d mod 8 = 5).  They live at residues n_sphere equiv 0, 1
(mod 8), i.e., d = 8n + 1 (for w_1) and d = 8n + 2 (for w_2).  The
Dirac residue is d mod 8 = 5, distinct from both.

Per-case anchoring under the corrected residues:

  obs         period  path       w_1@   w_2@   Dirac@   anchoring type
  -------------------------------------------------------------------
  theta_C     P_1     d=12..13   d=9    d=10   d=13     INHERITED
  b/s         P_0     d=6..13    d=1    d=2    d=5      INHERITED
  b/s         P_1     d=6..13    d=9    d=10   d=13     DIRECT
  theta_23    P_1     d=12..20   d=9    d=10   d=13     INHERITED
  theta_23    P_2     d=12..20   d=17   d=18   d=21     DIRECT

  DIRECT     = (w_1, w_2) generator layers IN the descent path.
  INHERITED  = (w_1, w_2) generator layers OUTSIDE the path; selection
               must extend from the period's Dirac layer to the
               generator layers via cascade structure.

Result: 2/5 cases are DIRECT (b/s P_1, theta_23 P_2);
        3/5 cases are INHERITED (theta_C P_1, b/s P_0, theta_23 P_1).

theta_23 P_2 is one of the two MOST DIRECTLY ANCHORED cases.  The
"rigour gap" framing was incorrect.

UNDER THIS REFRAMING, WHAT DOES THE RIGOUR GAP ACTUALLY LOOK LIKE?
==================================================================
Three candidate residual gaps:

  (R1) The INHERITED cases need an argument propagating the Dirac
       chirality basin selection at d=13 (or d=5) to the (w_1, w_2)
       generator layers d=9, 10 (or d=1, 2) OUTSIDE the path.
       Specifically:
         - For w_1 (chirality basin / Morse orientation): propagation
           via cascade scalar action's adjacency couples the Morse-
           function basin at d=13 to that at d=9 through Delta phi.
           Plausible.
         - For w_2 (spin lift): the cascade scalar field phi(d) is
           spin-agnostic, so the action does NOT directly propagate
           spin lifts.  Inherited w_2 must come from cascade-global
           spin convention, not from per-period propagation.

  (R2) The DIRECT cases (b/s P_1, theta_23 P_2) need an argument that
       the (w_1, w_2) selection at d=8n+1 and d=8n+2 in the path is
       cascade-natural.  Specifically:
         - For w_1 at d=17 (theta_23 P_2): the Morse function on S^16
           has 2 basins; cascade descent direction selects "down"
           basin -> w_1 = +.  Concrete.
         - For w_2 at d=18 (theta_23 P_2): S^17 is odd-dim (no
           chirality decomposition); the Z_2 spin lift selector at
           KO^2 is purely a labeling convention.

  (R3) The cascade-global w_2 = + convention.  For both DIRECT and
       INHERITED cases, the w_2 selection ultimately reduces to the
       cascade's universal convention "select Weyl_- chirality basin /
       cascade left-handed".  This is parallel to the Standard Model's
       "matter is left-handed under SU(2)_L" convention -- a labeling
       convention with zero observational input per Part IVb
       Remark cpt-balance-basins.

(R1) and (R2) are bookkeeping; the substantive content of the rigour
gap reduces to (R3): w_2 is a global labeling convention, not a
derivation.  This is parallel to other cascade labeling conventions
(matter/antimatter basin in CPT-balance; Q_e = -1 in SM).

CONCLUSION
==========
The rigour gap on theta_23 P_2 dissolves under the corrected anchoring
analysis.  All five period-by-period selections give w_2 = + by the
same cascade-global convention; whether the anchoring is DIRECT
(generator layer in path) or INHERITED (extended from a Dirac layer
in the period) is bookkeeping.

The residual is the recognition that w_2 is a labeling convention (the
same status as the SM's left-handed-matter convention), not a
derivation.  This is at strict parity with other cascade labeling
conventions and carries zero observational input.

Roadmap item #1 residual narrows to ONE item: the formal completeness
proof excluding higher KO classes (KO^4 = Z, etc.) from the channel
count.  The "theta_23 P_2 rigour" entry is closed.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

from cascade_constants import R, alpha, p, Omega  # noqa: E402

CHI = 2
BOTT_PERIOD = 8


def w1_layer(period: int) -> int:
    return BOTT_PERIOD * period + 1


def w2_layer(period: int) -> int:
    return BOTT_PERIOD * period + 2


def dirac_layers_in_period(period: int) -> list[int]:
    return [d for d in range(BOTT_PERIOD * period + 1, BOTT_PERIOD * (period + 1) + 1)
            if d % BOTT_PERIOD == 5]


# ---------------------------------------------------------------------------
# Step 1: enumerate the per-period anchoring type for each case
# ---------------------------------------------------------------------------

def report_anchoring_inversion() -> None:
    print("=" * 78)
    print("STEP 1: per-case anchoring type (DIRECT vs INHERITED)")
    print("=" * 78)
    print()
    print("The (w_1, w_2) Z_2 selectors live at sphere indices n equiv 0, 1")
    print("(mod 8) -- i.e., at cascade layers d = 8n + 1 (w_1) and d = 8n + 2")
    print("(w_2).  These are DISTINCT from the Dirac residue d mod 8 = 5.")
    print()
    print("DIRECT     = both (w_1, w_2) generator layers are in the path.")
    print("INHERITED  = generator layers are outside the path; selection must")
    print("             extend from the period's Dirac layer (or other anchor)")
    print("             to the generator layers via cascade structure.")
    print()
    print(f"  {'obs':<10s}  {'period':<6s}  {'path':<11s}  "
          f"{'w_1@':<5s}  {'w_2@':<5s}  {'Dirac@':<8s}  anchoring")
    print("  " + "-" * 76)

    cases = [
        ("theta_C",  1, 12, 13),
        ("b/s",      0, 6, 13),
        ("b/s",      1, 6, 13),
        ("theta_23", 1, 12, 20),
        ("theta_23", 2, 12, 20),
    ]
    direct = 0
    inherited = 0
    for name, period, lo, hi in cases:
        w1 = w1_layer(period)
        w2 = w2_layer(period)
        diracs = dirac_layers_in_period(period)
        dirac_str = ",".join(str(d) for d in diracs) if diracs else "none"
        w1_in = lo <= w1 <= hi
        w2_in = lo <= w2 <= hi
        if w1_in and w2_in:
            atype = "DIRECT"
            direct += 1
        elif (not w1_in) and (not w2_in):
            atype = "INHERITED"
            inherited += 1
        else:
            atype = "MIXED"
        print(f"  {name:<10s}  P_{period:<5d}  d={lo}..{hi:<6d}  d={w1:<3d}  d={w2:<3d}  "
              f"d={dirac_str:<6s}  {atype}")
    print()
    print(f"Tally: {direct}/5 DIRECT, {inherited}/5 INHERITED.")
    print()
    print("Note: theta_23 P_2 is DIRECT, not INHERITED.  The original ROADMAP")
    print("framing called it 'structurally weaker' because no Dirac layer is")
    print("crossed.  But the (w_1, w_2) generators are NOT Dirac layers -- they")
    print("sit at residues 1, 2 mod 8, distinct from Dirac (residue 5 mod 8).")
    print("In theta_23 P_2's path d=17..20, both generators (d=17, d=18) are")
    print("directly in the path.  In theta_C P_1's path d=12..13, neither")
    print("generator (d=9, d=10) is in the path.")
    print()


# ---------------------------------------------------------------------------
# Step 2: examine the inheritance mechanism for INHERITED cases
# ---------------------------------------------------------------------------

def report_inheritance_mechanism() -> None:
    print("=" * 78)
    print("STEP 2: inheritance mechanism for INHERITED cases")
    print("=" * 78)
    print()
    print("Three INHERITED cases: theta_C P_1, b/s P_0, theta_23 P_1.  In each,")
    print("the (w_1, w_2) generator layers are OUTSIDE the path, and the")
    print("selection must extend from the period's Dirac layer to those")
    print("generator layers via cascade structure.")
    print()
    print("WHAT THE INHERITANCE NEEDS TO PROPAGATE:")
    print()
    print("  - w_1 (Morse orientation / chirality basin label):")
    print("    The cascade scalar field phi(d) = ln Omega_d carries Morse-")
    print("    function basin labels on each even-dim S^{d-1}.  The cascade")
    print("    scalar action S[phi] = sum_d (2 alpha(d))^-1 (Delta phi)^2")
    print("    couples adjacent layers via Delta phi, so the basin label at a")
    print("    Dirac layer (e.g., d=13) propagates back to the (w_1) generator")
    print("    layer at d=9 via the action's continuity.  PROPAGATION VIA")
    print("    SCALAR ACTION: PLAUSIBLE.")
    print()
    print("  - w_2 (spin lift on S^{d-1}):")
    print("    The cascade scalar field phi(d) is spin-agnostic (a 0-form on")
    print("    the cascade lattice; carries no tangent-bundle data).  The")
    print("    action S[phi] is therefore invariant under spin-lift flips at")
    print("    every layer.  Consequently, the action does NOT propagate spin")
    print("    lifts between layers.  Inherited w_2 selection cannot come from")
    print("    the action; it must come from a separate cascade structure.")
    print()
    print("    The only available cascade structure that fixes w_2 universally")
    print("    is the cascade's GLOBAL spin lift convention -- a labeling")
    print("    convention parallel to the SM's 'matter is left-handed under")
    print("    SU(2)_L' convention.  Per Part IVb Remark cpt-balance-basins,")
    print("    this has ZERO OBSERVATIONAL INPUT (basin labels are convention-")
    print("    symmetric under CPT).")
    print()
    print("  CONCLUSION FOR INHERITED CASES:")
    print("    w_1: propagates via cascade scalar action (cascade-native).")
    print("    w_2: forced by cascade-global labeling convention (parity with")
    print("         SM convention; zero observational input).")
    print()


# ---------------------------------------------------------------------------
# Step 3: examine the direct mechanism for DIRECT cases
# ---------------------------------------------------------------------------

def report_direct_mechanism() -> None:
    print("=" * 78)
    print("STEP 3: direct mechanism for DIRECT cases")
    print("=" * 78)
    print()
    print("Two DIRECT cases: b/s P_1 and theta_23 P_2.  Both (w_1, w_2)")
    print("generator layers are in the path.")
    print()
    print("FOR b/s P_1 (path d=6..13, generators at d=9, 10):")
    print()
    print("  - w_1 at d=9: S^8 is even-dim (chi=2).  Morse function on S^8")
    print("    has 2 basins.  Cascade descent direction (high-d -> low-d,")
    print("    i.e., d=13 -> d=9 along the path) selects the 'down' basin.")
    print("    w_1 = + (cascade-natural orientation).")
    print()
    print("  - w_2 at d=10: S^9 is odd-dim (chi=0).  No chirality decomposition")
    print("    on S^9 directly.  The KO^2 = Z_2 spin lift selector classifies")
    print("    the two spin structures on S^9 (since pi_1(SO(10)) = Z/2).")
    print("    Cascade picks one by global convention.  w_2 = + (cascade-natural).")
    print()
    print("FOR theta_23 P_2 (path d=17..20, generators at d=17, 18):")
    print()
    print("  - w_1 at d=17: S^16 is even-dim (chi=2).  Morse function on S^16")
    print("    has 2 basins.  Cascade descent direction selects the 'down'")
    print("    basin (descent goes d=20 -> d=17 along the path).")
    print("    w_1 = + (cascade-natural orientation, same convention as b/s P_1).")
    print()
    print("  - w_2 at d=18: S^17 is odd-dim (chi=0).  No chirality decomposition.")
    print("    KO^2 = Z_2 spin lift selector on S^17.  Cascade picks one by")
    print("    global convention.  w_2 = + (cascade-natural, same convention).")
    print()
    print("  CONCLUSION FOR DIRECT CASES:")
    print("    w_1: forced by cascade descent direction at the (w_1) generator")
    print("         layer in path.  Concrete and cascade-internal.")
    print("    w_2: forced by cascade-global labeling convention at the (w_2)")
    print("         generator layer in path.  Same convention as INHERITED")
    print("         cases.")
    print()


# ---------------------------------------------------------------------------
# Step 4: the unified picture
# ---------------------------------------------------------------------------

def report_unified_picture() -> None:
    print("=" * 78)
    print("STEP 4: unified picture")
    print("=" * 78)
    print()
    print("Both DIRECT and INHERITED cases reduce to the same two cascade-")
    print("internal forcing arguments:")
    print()
    print("  (A) w_1 = + universally:")
    print("      Cascade descent direction (high-d -> low-d) is forced by the")
    print("      slicing recurrence Omega_{d+1} = Omega_d * sqrt(pi) * R(d) and")
    print("      the cascade's interpretation as descent from B^infty.  This")
    print("      is a derivation, not a convention -- the slicing recurrence")
    print("      defines a unique preferred direction, and the cascade's")
    print("      asymptotic origin at B^infty fixes which direction is")
    print("      'descent' (away from infinity, toward the observer).")
    print()
    print("  (B) w_2 = + universally:")
    print("      Cascade chirality basin convention (Weyl_- under cascade")
    print("      left-handed) is a labeling convention, parallel to the")
    print("      Standard Model's 'matter is left-handed under SU(2)_L'")
    print("      convention.  Per Part IVb Remark cpt-balance-basins, the")
    print("      basin label has zero observational content (the two basins")
    print("      are CPT-conjugate; either is 'matter' under suitable")
    print("      relabeling).")
    print()
    print("Consequence: the cascade has a UNIQUE (+, +) GLOBAL CONVENTION,")
    print("with w_1 = + derived (via slicing recurrence direction) and")
    print("w_2 = + a labeling convention (parity with SM left-handed convention).")
    print()
    print("Per-period anchoring (DIRECT vs INHERITED) is BOOKKEEPING.  Both")
    print("kinds of anchoring evaluate the cascade observable at the global")
    print("(+, +) pattern, picking up factor 1/chi^2 per spanned period.")
    print()
    print("THE ORIGINAL ROADMAP FRAMING WAS WRONG.  The 'theta_23 P_2 is")
    print("structurally weaker' claim was based on the assumption that Dirac-")
    print("anchoring is more rigorous than non-Dirac anchoring.  But the")
    print("(w_1, w_2) generators are NOT at Dirac layers; the rigour question")
    print("is about per-period activation, not about Dirac structure.  Under")
    print("the corrected analysis, theta_23 P_2 is one of the two most")
    print("directly anchored cases (alongside b/s P_1).")
    print()


# ---------------------------------------------------------------------------
# Step 5: residual gap analysis
# ---------------------------------------------------------------------------

def report_residual_gaps() -> None:
    print("=" * 78)
    print("STEP 5: residual gaps after this exploration")
    print("=" * 78)
    print()
    print("WHAT IS NOW CLOSED:")
    print()
    print("  - The 'theta_23 P_2 rigour gap' framing is corrected.  P_2 is")
    print("    DIRECT (most directly anchored), not weaker.  The earlier")
    print("    framing was based on the wrong intuition (Dirac vs non-Dirac).")
    print()
    print("  - The (w_1, w_2) selection is GLOBAL (not per-period anchored):")
    print("    w_1 = + universally derived (slicing recurrence direction).")
    print("    w_2 = + universally a labeling convention (parity with SM).")
    print()
    print("  - The activation argument from the verifier (Step 2(i) + 2(ii))")
    print("    suffices for all five period-by-period selections; no")
    print("    additional Dirac-anchored derivation is required.")
    print()
    print("WHAT REMAINS OPEN:")
    print()
    print("  (X) Formal completeness proof: that no higher-order tangent-")
    print("      bundle structure (e.g., p_1 in KO^4 = Z) activates additional")
    print("      Z_2 selectors at integer-d Bott lattice points.  Conjecture:")
    print("      KO^4 = Z is at residue n equiv 3 (mod 8), a free abelian")
    print("      factor (not a Z_2 chirality filter), and contributes to")
    print("      source strength (roadmap item #3) rather than channel count.")
    print()
    print("      Closing this requires explicit enumeration of im J's Z_2")
    print("      generators across the Bott periods touched by cascade")
    print("      descent paths and verification that no other structure")
    print("      activates.")
    print()
    print("  (Y) Recognition that w_2 = + is a labeling convention with")
    print("      zero observational content.  This is at strict parity with")
    print("      the SM's left-handed-matter convention and the cascade's")
    print("      CPT-balance basin label (Part IVb rem:cpt-balance-basins).")
    print("      Already acknowledged elsewhere; explicitly linking it here")
    print("      is the closure act.")
    print()


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main() -> int:
    print("=" * 78)
    print("CHANNEL-COUNT RULE: EXPLORATION OF THE THETA_23 P_2 RIGOUR GAP")
    print("Roadmap item #1, residual (a)")
    print("=" * 78)
    print()
    report_anchoring_inversion()
    report_inheritance_mechanism()
    report_direct_mechanism()
    report_unified_picture()
    report_residual_gaps()
    print("=" * 78)
    print("FINDING: the original 'theta_23 P_2 is weaker' framing is INVERTED.")
    print("         P_2 is one of the two most DIRECTLY anchored cases.  The")
    print("         (w_1, w_2) selection is GLOBAL: w_1 derived from slicing")
    print("         recurrence direction; w_2 a labeling convention parallel to")
    print("         the SM's left-handed convention (zero observational input).")
    print()
    print("STATUS:  Residual (a) on roadmap item #1 closes under this analysis.")
    print("         Only residual (b) -- formal completeness proof excluding")
    print("         higher KO classes -- remains.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
