#!/usr/bin/env python3
"""
Cascade Y sign: the Morse-index sign rule and what it actually
constrains.

CONTEXT
=======
Earlier dig (cascade_y_sign_analysis.py) flagged the two-population
Morse-index sign rule (Roadmap item 7) as a candidate for pinning
sign(Y_QL).  This script reads the rule's actual scope from
Part IVb rem:phase-family and audits whether it propagates to Y
eigenvalues.

THE TWO-POPULATION SIGN RULE'S SCOPE (Part IVb rem:phase-family)
=================================================================
The rule pins the SIGN of cascade potential SHIFTS delta Phi for
each precision observable Q:

  - Descent observables (alpha_s, m_tau, m_tau/m_mu, sin^2 theta_W,
    Omega_m, ell_A, v): sign +delta Phi.
    Cauchy-Schwarz Gram deficit Sum (1 - C^2_{d,d+1}) > 0 forces
    +sign cascade-natively (DERIVED, line 1174).

  - Geometric observables (theta_C, m_H/m_W, Omega_b): sign -delta Phi.
    Currently empirically consistent for theta_C, m_H/m_W; PROVED
    structurally for Omega_m via Bott-vs-lapse (line 1176-1182).
    Roadmap item 7 asks for full Morse-index closure.

  - Morse-index conjecture: 'minima for descent, saddles for geometric'
    (line 1185).  If derived, would close the sign rule cascade-natively.

CRITICAL OBSERVATION
====================
The sign rule operates on cascade potential SHIFTS delta Phi
(observable-level corrections at the observer).  It does NOT operate
on U(1)_Y eigenvalues Y per particle.  These are different
structures.

This script verifies that the propagation from delta-Phi sign rule
to Y-eigenvalue sign is NOT automatic, and identifies what
additional structure would be needed.

WHAT THIS SCRIPT DELIVERS
=========================
A clean statement of which cascade-derived sign mechanisms target
which sign questions.  The conclusion (negative for Y-sign closure
via Morse-index alone) is honest research result, not closure.
"""

from __future__ import annotations

import sys


def report_signed_structures():
    print("=" * 78)
    print("CASCADE-DERIVED SIGN MECHANISMS: scope and target")
    print("=" * 78)
    print()
    print("Mechanism (1): Cauchy-Schwarz Gram deficit")
    print("  Source: Part 0 Supplement, Sum (1 - C^2_{d,d+1}) > 0 strictly")
    print("          (adjacent-layer integrands not collinear in L^2).")
    print("  Targets: sign of delta Phi for DESCENT observables.")
    print("  Result:  +delta Phi forced.")
    print("  Status:  DERIVED rigorously (Part IVb rem:phase-family line 1174).")
    print()
    print("Mechanism (2): Bott-vs-lapse residue inequality")
    print("  Source: tools/verifiers/bott_vs_lapse_proof.py")
    print("          Strict inequality Sum_{d mod 8 = r} Omega_{d-1} < T/(2 pi)")
    print("          for every residue r in {0,...,7}.")
    print("  Targets: sign of delta Phi for Omega_m (geometric ratio-of-sums).")
    print("  Result:  -delta Phi forced for Omega_m.")
    print("  Status:  PROVED (Part IVb line 1176-1182).")
    print()
    print("Mechanism (3): Morse-index of observable in cascade configuration")
    print("  Source: Conjecture in Part IVb rem:phase-family line 1185.")
    print("          'Minima for descent, saddles for geometric.'")
    print("  Targets: sign of delta Phi for ALL observables.")
    print("  Result:  +delta Phi for descent (minima), -delta Phi for geometric (saddles).")
    print("  Status:  Conjectured; Roadmap item 7 (line 2309).")
    print()
    print("Mechanism (4): J orientation at d=14")
    print("  Source: Part II thm:complex (J^2 = -Id; J vs -J either valid).")
    print("  Targets: sign of U(1)_Y rotation (Y values flip sign under J -> -J).")
    print("  Result:  Y -> -Y under sign flip.")
    print("  Status:  CONVENTIONAL; not pinned by Part II thm:precession")
    print("          (orthogonality is reflection-symmetric: alpha = +/- pi/2).")
    print()


def audit_propagation_to_y():
    print("=" * 78)
    print("AUDIT: do mechanisms (1)-(3) propagate to sign(Y_QL)?")
    print("=" * 78)
    print()
    print("KEY DISTINCTION")
    print("---------------")
    print("Mechanisms (1)-(3) target the sign of delta Phi shifts -- additive")
    print("corrections to the cascade potential at the observer.  These are")
    print("SUBLEADING corrections to OBSERVABLE quantities (mass ratios,")
    print("gauge couplings, mixing angles).")
    print()
    print("Y values are NOT delta Phi shifts.  They are U(1)_Y eigenvalues")
    print("at d=14 -- weights of single-particle representations under")
    print("the U(1)_Y generator J|_{S^13}.  Different structural object.")
    print()
    print("PROPAGATION CHECK")
    print("-----------------")
    print("Could the Morse-index of a Y-related observable indirectly pin")
    print("sign(Y)?  Audit by observable type:")
    print()
    print("  (a) Yukawa-mediated mass m_e: descent observable, +delta Phi.")
    print("      But m_e (a positive scalar mass) is independent of sign(Y).")
    print("      m_e = |y_e| v / sqrt(2), with the modulus removing sign(Y).")
    print("      -> NO PROPAGATION to sign(Y).")
    print()
    print("  (b) Electroweak mixing sin^2 theta_W: descent observable,")
    print("      +delta Phi (closure via Theorem thm:weinberg-closure).")
    print("      sin^2 theta_W = g_1^2 / (g_1^2 + g_2^2): squared couplings,")
    print("      no sign content.")
    print("      -> NO PROPAGATION to sign(Y).")
    print()
    print("  (c) Cabibbo angle theta_C: geometric observable, -delta Phi.")
    print("      theta_C is a positive angle; its SIGN convention is")
    print("      determined by CKM matrix orientation (a flavor-basis choice).")
    print("      Cascade derives |theta_C| via -alpha(7)/chi^2 but does not")
    print("      derive the sign of theta_C from cascade primitives.")
    print("      -> NO PROPAGATION to sign(Y).")
    print()
    print("  (d) Cosmological matter fraction Omega_m: geometric observable,")
    print("      -delta Phi (proved via Bott-vs-lapse).  Omega_m is a")
    print("      positive fraction, no sign content beyond the -delta Phi sign.")
    print("      -> NO PROPAGATION to sign(Y).")
    print()
    print("  (e) Charge sum sum_i n_i Y_i: this IS a Y-trace.  In the SM it")
    print("      vanishes (gravitational anomaly).  A 'sum = 0' condition")
    print("      doesn't pin individual Y signs.")
    print("      -> NO PROPAGATION to sign(Y).")
    print()
    print("CONCLUSION")
    print("----------")
    print("None of the cascade-derived sign mechanisms (1)-(3) propagate")
    print("to sign(Y_QL).  They target observable-level delta Phi shifts,")
    print("which are quadratic/positive quantities (masses, mixing")
    print("magnitudes, fractions) or zero-sum traces -- all sign-invariant")
    print("under Y -> -Y.")
    print()
    print("Closing Roadmap item 7 (Morse-index sign rule) would NOT close")
    print("sign(Y_QL).  These are independent sign structures.")
    print()


def report_what_would_pin_sign():
    print("=" * 78)
    print("WHAT WOULD PIN sign(Y_QL) cascade-natively?")
    print("=" * 78)
    print()
    print("Closing sign(Y_QL) requires a cascade-internal structure that")
    print("EXPLICITLY breaks the J -> -J symmetry.  None of the existing")
    print("derived signed structures do this:")
    print()
    print("  - Cauchy-Schwarz Gram deficit: sums > 0 are sign-invariant.")
    print("  - Bott-vs-lapse: |Omega_d| inequalities are sign-invariant.")
    print("  - Morse-index: classifies observables by minimum/saddle, both")
    print("    invariant under Y -> -Y.")
    print()
    print("The cascade WOULD need a CP-violating structure or a parity-")
    print("breaking observable for which Y enters LINEARLY (not quadratically).")
    print("Candidates examined:")
    print()
    print("  (i) Cascade-derived CKM phase: cascade derives |theta_C|, but")
    print("      not its CP-violating phase.  If the cascade derived the")
    print("      phase cascade-natively (as a function of Y values), and")
    print("      observation pinned the phase's sign, this would pin Y.")
    print("      OPEN: cascade does not currently derive CP-violating phase.")
    print()
    print(" (ii) Cosmological matter excess: in our universe, the matter-")
    print("      antimatter asymmetry is observed (~10^-9 baryon excess).")
    print("      If the cascade derived this (e.g., via Sakharov conditions")
    print("      with cascade-internal CP-violation), it would pin Y signs.")
    print("      OPEN: cascade does not currently derive matter excess.")
    print()
    print("(iii) Linear-in-Y observable: any cascade-internal observable")
    print("      that is linear in Y (not |Y| or Y^2) would carry sign")
    print("      content directly.  None identified yet.")
    print()
    print("HONEST ASSESSMENT")
    print("=================")
    print("The cascade's powerful signed-structure machinery (Cauchy-Schwarz,")
    print("Bott-vs-lapse, Morse) operates on quadratic/positive cascade")
    print("quantities, not on linear U(1)_Y eigenvalues.  Pinning sign(Y_QL)")
    print("would require either:")
    print()
    print("  1. A new linear-in-Y cascade observable (unidentified).")
    print("  2. Cascade-derived CP-violation (open research direction).")
    print("  3. Cascade-derived cosmological matter excess (open research")
    print("     direction, possibly tied to (2)).")
    print()
    print("None of these are within reach of the existing cascade primitives.")
    print()
    print("CONCLUSION: sign(Y_QL) genuinely appears to be at parity with")
    print("the SM's external sign anchor (Q_e = -1).  The user's hope that")
    print("a geometric/topological fact would close it does not match the")
    print("cascade's existing derived structures, which all target the")
    print("wrong sign question (delta Phi observable corrections rather")
    print("than U(1)_Y eigenvalue signs).")
    print()


def report_silver_lining():
    print("=" * 78)
    print("SILVER LINING")
    print("=" * 78)
    print()
    print("The negative result has structural value:")
    print()
    print("  1. The cascade's delta Phi sign rule IS a real cascade-derived")
    print("     signed structure.  Closing Roadmap item 7 would still be")
    print("     valuable -- it makes the empirical 'descent vs geometric'")
    print("     classification structural.")
    print()
    print("  2. The Y-sign question is now SHARPLY separated from the")
    print("     delta Phi-sign question.  Different mechanisms target each.")
    print("     This clarifies the cascade's dependency map.")
    print()
    print("  3. The matter-rep gap status is more honest: the cascade")
    print("     reduces 5-6 free Y values to 1 trace identity (R1) + 1")
    print("     external sign anchor.  The external anchor is at PARITY")
    print("     with the SM's Q_e = -1, not a structural deficit.")
    print()
    print("  4. Three open research directions for sign closure are now")
    print("     identified explicitly:")
    print("       (i)   cascade CP-violating phase derivation,")
    print("       (ii)  cascade cosmological-matter-excess derivation,")
    print("       (iii) discovery of a linear-in-Y cascade observable.")
    print("     Each is a tractable structural research target.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE Y SIGN: Morse-index audit and propagation")
    print("=" * 78)
    print()
    report_signed_structures()
    audit_propagation_to_y()
    report_what_would_pin_sign()
    report_silver_lining()
    return 0


if __name__ == "__main__":
    sys.exit(main())
