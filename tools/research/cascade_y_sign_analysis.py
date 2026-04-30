#!/usr/bin/env python3
"""
Cascade Y sign analysis: is sign(Y_QL) cascade-derivable, or is it
a convention shared with the SM?

CONTEXT
=======
Commit b1d573f reduced the Y-spectrum residual to:
  (1) Derive (R1) Y_H = N_c * Y_QL cascade-natively, AND
  (2) Pin sign(Y_QL) cascade-natively.

This script audits cascade primitives that carry sign content and
asks whether any uniquely pins sign(Y_QL).

THE QUESTION
============
The cascade-derived Y spectrum (under the trace-identity proposal)
is determined modulo overall sign:

  Sign convention 1 (SM):    Y_QL = +1/6, Y_uRc = -2/3, Y_eRc = +1
  Sign convention 2 (CP'd):  Y_QL = -1/6, Y_uRc = +2/3, Y_eRc = -1

The two are physically distinct (charge of the electron differs in
sign), connected by complex conjugation in the cascade U(1)_Y phase.

Can the cascade pick one over the other from internal primitives,
or does it require an external sign anchor (analogous to the SM's
'electron has charge -1' anchor)?

CASCADE PRIMITIVES WITH SIGN CONTENT
=====================================
Four candidate cascade structures carry sign:

  (A) J vs -J at d=14.  Cascade complex structure (Part II thm:complex)
      with J^2 = -Id.  Either sign of J defines a valid complex structure;
      Adams uniqueness (rho(14)-1 = 1) doesn't distinguish J from -J.

  (B) Spin(12)-Weyl_- vs Weyl_+ chirality at d=13.  PR #108 distinguished
      these (Weyl_- is doublet under SU(2)_R, Weyl_+ is singlet).  But
      the LABELS 'left-handed' vs 'right-handed' are conventional --
      cascade-internally, only the chirality SPLIT is structural; the
      assignment to L vs R observer-handed matter is convention.

  (C) Higgs vacuum direction at d=13.  Cascade Higgs at S^12 hairy-ball
      zero (Part IVa thm:higgs); VEV at the equator (geodesic distance
      pi/2).  The DIRECTION on the equator is SU(2)-conventional: any
      direction is gauge-equivalent under SU(2)_L rotation.

  (D) Cascade time direction (d-increasing).  Forced by Part 0 threshold
      ladder (observer at d=5 toward Planck sink at d=217).  Cascade-
      derived structurally.

This script audits each to determine whether it pins sign(Y_QL).
"""

from __future__ import annotations

import sys


def report_question():
    print("=" * 78)
    print("CASCADE Y SIGN ANALYSIS")
    print("=" * 78)
    print()
    print("Question: is sign(Y_QL) cascade-derivable from internal primitives,")
    print("or does the cascade need an external sign anchor (like the SM's")
    print("'electron has Q = -1')?")
    print()


def audit_J_orientation():
    print("=" * 78)
    print("AUDIT (A): J vs -J at d=14")
    print("=" * 78)
    print()
    print("Part II thm:complex derives J via forced precession.  Part II")
    print("thm:precession: 'angle between consecutive slicing axes is")
    print("alpha = pi/2, forced by the cascade's orthogonality axiom.'")
    print()
    print("KEY OBSERVATION (Part II line 615-617): orthogonality is")
    print("REFLECTION-SYMMETRIC.  '|alpha| = pi/2' satisfies e_{k+1} perp e_k")
    print("for both alpha = +pi/2 AND alpha = -pi/2.  The orthogonality axiom")
    print("forces the MAGNITUDE of the precession angle but NOT the SIGN.")
    print()
    print("Consequence: J at d=14 has two equally cascade-consistent")
    print("orientations:")
    print("  +J:  rotation by +pi/2 (CCW in the e_1-e_2 plane)")
    print("  -J:  rotation by -pi/2 (CW)")
    print()
    print("Both have J^2 = -Id, both are valid Adams fields on S^13, both")
    print("generate U(1)_Y as exp(theta J).  The CHOICE between them is")
    print("conventional in the cascade.")
    print()
    print("RESULT for (A): J's sign is NOT cascade-pinned.  This is one")
    print("internal sign convention.")
    print()


def audit_spin12_chirality():
    print("=" * 78)
    print("AUDIT (B): Spin(12)-Weyl_- vs Weyl_+ at d=13")
    print("=" * 78)
    print()
    print("PR #108 established the chirality split: under diagonal SU(2)_R")
    print("on the Spin(12) Dirac, Weyl_- decomposes as 14 doublets + 1")
    print("quartet (the multiplets the cascade keeps for left-handed matter)")
    print("and Weyl_+ decomposes as 14 singlets + 6 triplets (the multiplets")
    print("the cascade keeps for right-handed matter).")
    print()
    print("KEY OBSERVATION: the chirality SPLIT is cascade-derived, but the")
    print("LABELING 'Weyl_- is left' vs 'Weyl_- is right' is not.")
    print()
    print("Spin(12) Dirac has gamma_13 (the chirality matrix) with eigenvalues")
    print("+/- 1.  The two eigenspaces are isomorphic as vector spaces and")
    print("only distinguished by a sign convention.  Identifying 'Weyl_- =")
    print("eigenvalue +1' vs 'Weyl_- = eigenvalue -1' is a sign convention.")
    print()
    print("This sign convention is RELATED to (A): once J's orientation is")
    print("chosen, the natural identification of Weyl chirality follows from")
    print("J's action on each Spin(4) factor.  Specifically, J's eigenvalues")
    print("+i (= +1 on the 'positive chirality' subspace) define which")
    print("subspace is 'Weyl_-' = SU(2)_R doublet.")
    print()
    print("Consequence: (A) and (B) are NOT independent sign conventions.")
    print("They collapse to a single cascade-internal sign convention via")
    print("the J-chirality coupling at d=13.")
    print()
    print("RESULT for (B): no INDEPENDENT cascade-pinned sign here.  Once")
    print("(A) is fixed, (B) is determined.")
    print()


def audit_higgs_vacuum_direction():
    print("=" * 78)
    print("AUDIT (C): Higgs vacuum direction at d=13")
    print("=" * 78)
    print()
    print("Cascade Higgs at S^12 hairy-ball zero (Part IVa thm:higgs).")
    print("VEV at the equator (geodesic distance pi/2 from the zero).")
    print()
    print("KEY OBSERVATION: any direction on the S^12 equator is SU(2)_L-")
    print("equivalent.  Two points on the equator differ by an SU(2)_L")
    print("rotation, which is a gauge transformation.  Different choices")
    print("of vacuum direction correspond to gauge-equivalent vacua.")
    print()
    print("Once the gauge is fixed (i.e., once a specific direction on the")
    print("equator is chosen as 'the' VEV), the SU(2)_L doublet decomposes")
    print("into 'upper' (T_3 = +1/2) and 'lower' (T_3 = -1/2) components.")
    print("The vacuum sits at one of these.")
    print()
    print("The choice of upper-vs-lower = sign of T_3 for the vacuum component,")
    print("which determines sign(Y_H) via Y_H = -T_3^vac.  This is the same")
    print("sign convention as (A) and (B): once the cascade's J orientation")
    print("and Spin(12) chirality assignments are fixed, the vacuum direction")
    print("follows.")
    print()
    print("RESULT for (C): no INDEPENDENT cascade-pinned sign here.  Once")
    print("(A) is fixed, (C) is determined (modulo gauge choice, which is")
    print("absorbed into the U(1)_em definition).")
    print()


def audit_cascade_time_direction():
    print("=" * 78)
    print("AUDIT (D): cascade time direction (d-increasing)")
    print("=" * 78)
    print()
    print("Part 0 threshold ladder forces the cascade to flow from observer")
    print("(d_V = 5) toward Planck sink (d_2 = 217).  This direction IS")
    print("cascade-derived: d_2 > d_1 > d_0 > d_V is structural.")
    print()
    print("KEY OBSERVATION: time direction does NOT pin charge sign.")
    print("In QFT:")
    print("  - Time-reversal (T): flips momentum, spin; preserves charge.")
    print("  - Parity (P):       flips spatial coordinates; preserves charge.")
    print("  - Charge conjugation (C): flips charge.")
    print()
    print("Charge sign is flipped only by C, which is independent of the")
    print("cascade's d-direction.  The cascade's time-arrow does not")
    print("constrain sign(Y).")
    print()
    print("CP-violation: if the cascade had a specific CP-violating")
    print("phase, it could distinguish 'matter' from 'antimatter' and pin")
    print("a charge sign.  The cascade's J orientation is naively CP-symmetric")
    print("(J -> -J under CP).  The cascade does not currently derive a")
    print("specific CP-violating phase that would anchor sign(Y).")
    print()
    print("RESULT for (D): cascade time direction does NOT pin sign(Y).")
    print()


def report_conclusion():
    print("=" * 78)
    print("CONCLUSION: cascade and SM are at parity on sign anchoring")
    print("=" * 78)
    print()
    print("Cascade structure:")
    print("  - Three sign-content primitives (A), (B), (C) collapse to ONE")
    print("    independent sign convention via cascade-internal relations")
    print("    (J's orientation determines (B) and (C) consistently).")
    print("  - (D) Cascade time direction does not pin charge sign.")
    print("  - Net: the cascade has ONE external sign convention to anchor.")
    print()
    print("SM structure:")
    print("  - Anomaly cancellation pins Y values modulo overall sign.")
    print("  - Q_e = -1 is observed, anchoring the sign.")
    print("  - Net: the SM has ONE external sign convention to anchor")
    print("    (the observed sign of the electron's charge).")
    print()
    print("Both cascade and SM derive the Y SPECTRUM up to one overall")
    print("sign, and both require ONE external anchor to pin it.  The")
    print("cascade is NOT structurally deficient relative to the SM on")
    print("sign anchoring.")
    print()
    print("REFRAMING")
    print("=========")
    print("'Sign(Y_QL) cascade-derivation' was an over-strict criterion.")
    print("The honest formulation:")
    print()
    print("  Y SPECTRUM (under (R1) trace identity + cascade structure")
    print("  + smallest-magnitude principle): cascade-derivable up to one")
    print("  overall sign.")
    print()
    print("  ANCHOR: external (cascade J orientation, equivalent to the")
    print("  SM's Q_e = -1 observation).")
    print()
    print("The matter-rep gap of CLAUDE.md reduces from 'specific Y values")
    print("imported from SM observation' to 'overall sign of Y values")
    print("anchored by external convention (parallel to the SM's Q_e = -1");
    print("convention)' once (R1) is closed cascade-natively.")
    print()
    print("STATUS")
    print("======")
    print("The chain of reductions now ends at:")
    print()
    print("  matter-rep gap (CLAUDE.md, original)")
    print("    -> oq:fermion-gauge-action")
    print("    -> path-tensor consistency")
    print("    -> cascade-native integer Q numerators")
    print("    -> (R1) Y_H = N_c * Y_QL  [open: derive trace identity]")
    print("    -> (R2) Y_LL = -Y_H       [closed: gravitational anomaly + Yukawa]")
    print("    -> sign(Y_QL)             [SHARED CONVENTION WITH SM, not")
    print("                                cascade-derivable from internal")
    print("                                primitives alone]")
    print()
    print("After this dig: only (R1) remains as a cascade-internal open")
    print("question.  The sign question is reframed as 'shared with SM,")
    print("not deficient.'")
    print()


def main() -> int:
    report_question()
    audit_J_orientation()
    audit_spin12_chirality()
    audit_higgs_vacuum_direction()
    audit_cascade_time_direction()
    report_conclusion()
    return 0


if __name__ == "__main__":
    sys.exit(main())
