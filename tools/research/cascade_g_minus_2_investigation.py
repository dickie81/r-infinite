#!/usr/bin/env python3
"""
Cascade-native (g-2) anomalous magnetic moment: structural reading
of Schwinger's alpha/(2 pi) at 1-loop and assessment of higher-loop
predictions.

CONTEXT
=======
The m - k = 0 balanced slot in the cascade's chirality classification
is currently empty (cascade_mk0_investigation.py).  The natural test
observable is the anomalous magnetic moment (g-2), which corresponds
to a 1-loop vertex correction with k=1 external fermion mode + m=1
internal closed loop.

This script:
  1. Articulates the cascade-native structural form for a_f at 1-loop.
  2. Tests the structural identification against observed a_e and a_mu.
  3. Examines whether higher-loop corrections are cascade-native.
  4. Identifies the framework gap and the most tractable next step.

WHAT THIS SCRIPT FINDS
======================
At 1-loop, the cascade has a structural identification reading:

  a_f^{cascade-1loop} = alpha_em / (2 pi)
                      = (cascade gauge coupling at observer) /
                        (closed-loop n=2 cascade primitive)

This reproduces Schwinger's QED 1-loop result exactly (a_e = 1.162e-3).
But it is a STRUCTURAL READING, not a derived calculation:

  - The cascade has no vertex-correction framework.
  - Per-layer locality precludes the standard QED triangle topology.
  - The "1/(2 pi)" factor is identified as the inverse of the closed-
    loop n=2 cascade primitive; this is suggestive but not derived
    from a cascade-lattice computation.

Higher-loop corrections are NOT obviously cascade-native:

  - QED 2-loop coefficient: -0.328 (alpha/pi)^2  (NEGATIVE sign).
  - Cascade closed-loop n=4 primitive: 2 pi^2 (no obvious sign).
  - The cascade's 2-loop prediction structure is not derivable from
    the n=2 / n=4 hierarchy without additional structural input.

Observed a_e and a_mu values include all loop orders; the cascade's
1-loop Schwinger reproduction is a STRUCTURAL DERIVATION but not a
COMPLETE PREDICTION.

VERDICT
=======
The cascade can structurally identify the 1-loop coefficient 1/(2 pi)
with the inverse of its closed-loop n=2 primitive.  This is suggestive
but does not yet constitute a derived cascade-native (g-2) calculation.
The framework gap (no vertex-correction structure in the gauge-coupled
fermion action) is real.

Closing the m - k = 0 slot via (g-2) requires:
  1. Cascade-lattice vertex correction calculation.
  2. Scalar-mediated transport between Dirac layer (fermion) and
     gauge-window layer (photon).
  3. Extraction of the dimensionless coefficient F_2(0) = a_f.

These are substantial structural-research targets, not just a
verification of an existing rule.  The (g-2) test is not currently
tractable as a clean cascade calculation without first developing
the gauge-coupled fermion action's vertex correction structure.
"""

from __future__ import annotations

import math
import sys


# ---------------------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------------------

def Gamma_half() -> float:
    return math.sqrt(math.pi)


def chi() -> float:
    return 2.0


def alpha_cascade(d: int) -> float:
    R = math.exp(math.lgamma((d+1)/2) - math.lgamma((d+2)/2))
    return R**2 / 4


def alpha_em_cascade() -> float:
    """Cascade prediction for 1/alpha_em(observer) = 1/alpha(13) + pi/alpha(14) + 6 pi.

    Returns alpha_em (not 1/alpha_em).
    """
    inv_a13 = 1.0 / alpha_cascade(13)
    inv_a14 = 1.0 / alpha_cascade(14)
    inv_alpha_em = inv_a13 + math.pi * inv_a14 + 6 * math.pi
    return 1.0 / inv_alpha_em


# ---------------------------------------------------------------------------
# Step 1: structural reading of Schwinger
# ---------------------------------------------------------------------------

def report_schwinger_structural():
    print("=" * 78)
    print("STEP 1: structural reading of Schwinger's alpha/(2 pi)")
    print("=" * 78)
    print()
    print("Schwinger 1948: a_e^{1-loop} = alpha / (2 pi)")
    print()
    print("In cascade primitives:")
    alpha_em = alpha_em_cascade()
    inv_alpha_em = 1.0 / alpha_em
    closed_loop_n2 = chi() * Gamma_half() ** 2
    print(f"  alpha_em^{{cascade}} = (1/alpha(13) + pi/alpha(14) + 6 pi)^{{-1}}")
    print(f"                   = (27.018 + 91.160 + 18.850)^{{-1}}")
    print(f"                   = 1/{inv_alpha_em:.4f}")
    print(f"                   = {alpha_em:.6f}")
    print()
    print(f"  closed-loop n=2 primitive = chi * Gamma(1/2)^2 = 2 pi = {closed_loop_n2:.4f}")
    print()
    print("Cascade-native structural identification:")
    print()
    a_e_cascade = alpha_em / closed_loop_n2
    a_e_observed = 1.15965218128e-3  # PDG 2024, electron g-2 measurement
    a_e_schwinger = (1/137.036) / (2 * math.pi)
    print(f"  a_e^{{cascade-1loop}} = alpha_em / (closed-loop n=2 primitive)")
    print(f"                    = {alpha_em:.6f} / {closed_loop_n2:.4f}")
    print(f"                    = {a_e_cascade:.10f}")
    print()
    print(f"  a_e^{{Schwinger}}    = (1/137.036) / (2 pi) = {a_e_schwinger:.10f}")
    print(f"  a_e^{{cascade}} - Schwinger = {(a_e_cascade - a_e_schwinger):+.2e}")
    print()
    print(f"  Observed a_e (PDG 2024 Penning-trap):  {a_e_observed:.10f}")
    print(f"  Cascade match to observed:             {(a_e_cascade - a_e_observed)/a_e_observed*100:+.4f}%")
    print()
    print("INTERPRETATION:")
    print("The cascade reads Schwinger's 1/(2 pi) factor as the INVERSE of")
    print("the closed-loop n=2 cascade primitive 2 pi.  This is the SAME")
    print("primitive that appears in the 1/alpha_em screening (per-Dirac-layer")
    print("contribution = 2 pi).  In the screening, the primitive enters")
    print("ADDITIVELY to 1/alpha_em; in (g-2), the primitive enters")
    print("MULTIPLICATIVELY (as 1/(2 pi)) on the gauge coupling.")
    print()
    print("Both are manifestations of the same closed-loop n=2 cascade")
    print("primitive 2 pi at the Dirac layer.")
    print()


# ---------------------------------------------------------------------------
# Step 2: structural derivation status
# ---------------------------------------------------------------------------

def report_derivation_status():
    print("=" * 78)
    print("STEP 2: derivation status of the cascade (g-2)")
    print("=" * 78)
    print()
    print("The Schwinger reproduction at 1-loop is a STRUCTURAL")
    print("IDENTIFICATION, not a derived calculation.  Three reasons:")
    print()
    print("  1. THE CASCADE HAS NO VERTEX-CORRECTION FRAMEWORK.")
    print("     The cascade's gauge-coupled fermion action proposal")
    print("     (rem:fermion-gauge-coupling-proposal) has per-layer")
    print("     Berezin reduction at A=0 closed, but the photon-")
    print("     fermion-fermion vertex correction structure is open")
    print("     (oq:fermion-gauge-action).  Without the vertex")
    print("     correction calculation, 1/(2 pi) cannot be DERIVED")
    print("     from the cascade -- it is identified by inspection.")
    print()
    print("  2. PER-LAYER LOCALITY PRECLUDES THE QED TRIANGLE TOPOLOGY.")
    print("     QED's vertex correction is a fermion triangle: 3")
    print("     internal fermion propagators forming a closed loop.")
    print("     The cascade fermion is per-layer local: an external")
    print("     fermion at Dirac layer d_g cannot have a sub-loop at")
    print("     the same layer.  The cascade-native vertex correction")
    print("     must be MULTI-LAYER (external f at d_g, loop at d_gw),")
    print("     mediated by the scalar field.  This structure is")
    print("     undeveloped.")
    print()
    print("  3. THE 1/(2 pi) IDENTIFICATION IS A POST-HOC READING.")
    print("     The 1/(2 pi) coefficient is taken from Schwinger; the")
    print("     cascade then identifies it with the inverse of its own")
    print("     closed-loop n=2 primitive.  A genuine cascade derivation")
    print("     would START from cascade primitives and PRODUCE 1/(2 pi)")
    print("     as the result, not the other way around.")
    print()
    print("STATUS: cascade-native (g-2) at 1-loop is STRUCTURAL IDENTIFICATION,")
    print("not derivation.  The cascade reproduces Schwinger numerically by")
    print("identification; a cascade-lattice vertex-correction calculation")
    print("is open work.")
    print()


# ---------------------------------------------------------------------------
# Step 3: higher-loop predictions
# ---------------------------------------------------------------------------

def report_higher_loops():
    print("=" * 78)
    print("STEP 3: higher-loop QED corrections vs cascade primitives")
    print("=" * 78)
    print()
    print("QED higher-loop corrections to a_e:")
    print()
    print("  1-loop (Schwinger):   A^(2) = 1/2     in (alpha/pi)^1")
    print("  2-loop:               A^(4) = -0.328  in (alpha/pi)^2")
    print("  3-loop:               A^(6) = +1.181  in (alpha/pi)^3")
    print("  4-loop:               A^(8) = -1.91   in (alpha/pi)^4")
    print()
    print("Sign pattern: alternating, with 1-loop positive and 2-loop")
    print("negative.  This is the standard pattern of QED loop expansion.")
    print()
    print("Cascade closed-loop primitive hierarchy chi * Gamma(1/2)^n:")
    print()
    print(f"  n=2: 2 pi    = {2*math.pi:.4f}")
    print(f"  n=4: 2 pi^2  = {2*math.pi**2:.4f}")
    print(f"  n=6: 2 pi^3  = {2*math.pi**3:.4f}")
    print()
    print("Cascade structural prediction for 2-loop (g-2) (assuming the")
    print("inverse of the n=4 primitive enters multiplicatively at order")
    print("alpha^2):")
    print()
    a_em = 1/137.036
    a_2loop_qed = -0.328 * (a_em/math.pi)**2
    a_2loop_cascade_naive = (a_em/math.pi)**2 / (2*math.pi**2)
    a_2loop_cascade_signed_minus = -(a_em/math.pi)**2 / (2*math.pi**2)
    print(f"  a_e^{{QED-2loop}}            = {a_2loop_qed:+.3e}")
    print(f"  a_e^{{cascade-2loop-naive}}  = +(alpha/pi)^2 / (2 pi^2) = {a_2loop_cascade_naive:+.3e}")
    print(f"  a_e^{{cascade-2loop-signed-}} = -(alpha/pi)^2 / (2 pi^2) = {a_2loop_cascade_signed_minus:+.3e}")
    print()
    print(f"  Ratio cascade-naive / QED-2loop:  {abs(a_2loop_cascade_naive / a_2loop_qed):.4f}")
    print(f"  Ratio cascade-signed / QED-2loop: {abs(a_2loop_cascade_signed_minus / a_2loop_qed):.4f}")
    print()
    print("INTERPRETATION:")
    print("The cascade's n=4 primitive 2 pi^2 gives a 2-loop coefficient")
    print(f"|A^(4)|^{{cascade}} = 1/(2 pi^2) = {1/(2*math.pi**2):.4f}, which is")
    print(f"smaller than QED's |A^(4)| = 0.328 by a factor of {0.328 * 2*math.pi**2:.2f}.")
    print()
    print("This is NOT a clean match.  The cascade primitive 2 pi^2 doesn't")
    print("reproduce the QED 2-loop coefficient 0.328.")
    print()
    print("Either:")
    print("  (a) The cascade's higher-loop structure is genuinely different")
    print("      from QED's loop expansion.")
    print("  (b) The cascade primitive at order 2-loop is NOT directly")
    print("      1/(2 pi^2) -- there might be a more complex structure.")
    print("  (c) The cascade's per-layer-local vertex correction has a")
    print("      different topological structure than QED's nested loops,")
    print("      and the 'order' counting is different.")
    print()
    print("Without a developed vertex-correction framework, can't resolve this.")
    print()


# ---------------------------------------------------------------------------
# Step 4: a_mu and the muon (g-2) tension
# ---------------------------------------------------------------------------

def report_muon_tension():
    print("=" * 78)
    print("STEP 4: a_mu and the muon (g-2) tension")
    print("=" * 78)
    print()
    print("Observed a_mu (Fermilab g-2 + Brookhaven, world average 2023):")
    print(f"  a_mu^{{obs}}  = (116592061 +/- 41) x 10^{{-11}}")
    print(f"  a_mu^{{SM}}   = (116591810 +/- 43) x 10^{{-11}}")
    print(f"  Tension     = (251 +/- 60) x 10^{{-11}}  ~ 4.2 sigma")
    print()
    print("This is the famous muon (g-2) anomaly.")
    print()
    print("Cascade prediction (1-loop Schwinger reproduction):")
    a_mu_cascade_1loop = (1/137.036) / (2 * math.pi)
    print(f"  a_mu^{{cascade-1loop}} = alpha_em / (2 pi) = {a_mu_cascade_1loop:.6e}")
    print(f"                     ~= {a_mu_cascade_1loop/1e-11:.0f} x 10^{{-11}}")
    print()
    print("Hmm, that's only the leading 1-loop value.  The full SM prediction")
    print("includes hadronic vacuum polarisation, hadronic light-by-light, and")
    print("electroweak contributions, summing to 116591810 x 10^{-11}.")
    print()
    print("The cascade has NO framework for these contributions:")
    print("  - Hadronic VP: requires hadronic spectrum and quark-loop contributions.")
    print("  - Hadronic LbL: this is the n=4 closed-loop case at quark Dirac layers.")
    print("  - Electroweak: requires W, Z, Higgs loop contributions.")
    print()
    print("The cascade's potential contribution to the muon (g-2) anomaly:")
    print("  - If cascade gives the SM 1-loop value (0.001162 = 1162 x 10^{{-9}})")
    print("    plus a structurally-different 2-loop contribution, it could either")
    print("    enhance or relieve the tension.")
    print("  - Without computing higher orders cascade-natively, can't say.")
    print()
    print("The cascade's COMMITMENT (implicit, from its no-extra-physics-beyond-SM")
    print("structural claim): no anomalous (g-2) contribution beyond what the")
    print("structural reading produces.  If the muon (g-2) anomaly is real, the")
    print("cascade is challenged at the same level as SM.")
    print()


# ---------------------------------------------------------------------------
# Step 5: framework gap and tractable next steps
# ---------------------------------------------------------------------------

def report_framework_gap_g_minus_2():
    print("=" * 78)
    print("STEP 5: framework gap and tractable next steps for cascade (g-2)")
    print("=" * 78)
    print()
    print("FRAMEWORK GAP: cascade has no vertex-correction calculation")
    print("framework.  Closing this requires:")
    print()
    print("  1. Set up the gauge-coupled fermion action's photon-fermion-")
    print("     fermion vertex correction structure on the cascade lattice.")
    print()
    print("  2. Define the multi-layer topology: external fermion at Dirac")
    print("     layer d_g, internal closed structure at gauge-window layer")
    print("     d_gw, mediated by the scalar field's kinetic term.")
    print()
    print("  3. Compute the dimensionless coefficient of the magnetic-moment")
    print("     form factor F_2(0) on the cascade lattice.")
    print()
    print("  4. Extract a_f^{cascade} from F_2(0).")
    print()
    print("These are all open work.  The cascade's existing per-layer Berezin")
    print("calculation (rem:berezin-partition-derivation) closes the A=0")
    print("piece, but the gauge-coupled vertex correction is open.")
    print()
    print("MOST TRACTABLE NEXT STEPS (in order of difficulty):")
    print()
    print("  1. SCALAR (g-2)-LIKE TESTBED.  Before computing the fermion")
    print("     vertex correction, compute the scalar analog: phi^4 vertex")
    print("     correction with internal scalar loop on the cascade lattice.")
    print("     If the cascade primitive 1/(2 pi) emerges naturally, the")
    print("     framework generalises.  If it doesn't, the framework needs")
    print("     additional structural input.")
    print()
    print("  2. CASCADE-NATIVE F_2(0) FROM SCALAR-MEDIATED PHOTON COUPLING.")
    print("     The cascade fermion at d_g couples to the photon at d_gw=14")
    print("     via scalar mediation.  Compute the effective F_2(0) from this")
    print("     structure and check against Schwinger.  If F_2(0) =")
    print("     alpha_em / (2 pi), the cascade reproduces Schwinger as a")
    print("     theorem (not just identification).  If not, the cascade")
    print("     gives a different prediction.")
    print()
    print("  3. STRUCTURAL DERIVATION OF THE INVERSE-PRIMITIVE RULE.")
    print("     The structural reading 'a_f = (gauge coupling) / (closed-loop")
    print("     n=2 primitive)' suggests a general rule: every multiplicative")
    print("     correction of the form (gauge coupling) is divided by a")
    print("     cascade primitive determined by the loop topology.  This")
    print("     could extend to anomalous quantities beyond (g-2).  Open.")
    print()
    print("STATUS: (g-2) cascade-native calculation is open at the framework")
    print("level.  The 1-loop Schwinger reproduction is structural")
    print("identification only; higher loops are uncertain.  Substantial")
    print("structural-research work is needed before (g-2) is a derived")
    print("cascade prediction.")
    print()


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

def report_summary():
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print()
    print("Investigation of (g-2) as the canonical m - k = 0 cascade")
    print("observable finds:")
    print()
    print("1. STRUCTURAL READING WORKS AT 1-LOOP.  Schwinger's a_f = alpha/(2 pi)")
    print("   is reproducible by identifying 1/(2 pi) with the inverse of the")
    print("   closed-loop n=2 cascade primitive 2 pi.  Numerical agreement")
    print("   with Schwinger is exact by construction.")
    print()
    print("2. NOT A DERIVED CALCULATION.  The 1-loop reproduction is a")
    print("   structural identification, not a cascade-lattice calculation.")
    print("   The cascade lacks a vertex-correction framework; per-layer")
    print("   locality precludes the standard QED triangle topology.")
    print()
    print("3. HIGHER LOOPS ARE NOT CASCADE-NATIVE.  QED's 2-loop coefficient")
    print("   |A^(4)| = 0.328 is much larger than the cascade's 1/(2 pi^2) =")
    print("   0.0507 (factor 6.5x).  Either the cascade has different higher-")
    print("   loop structure than QED, or the n-leg primitive doesn't enter")
    print("   inversely at order n.")
    print()
    print("4. MUON (g-2) ANOMALY UNRESOLVED.  Without a vertex-correction")
    print("   framework, the cascade cannot make a definitive prediction for")
    print("   a_mu.  If the SM prediction is correct and the experimental")
    print("   anomaly is real, the cascade is challenged at SM level.  If")
    print("   the anomaly resolves toward the SM, the cascade is consistent.")
    print()
    print("5. m - k = 0 SLOT REMAINS EMPTY.  The structural reading at 1-loop")
    print("   is suggestive but not derived.  Closing the m - k = 0 slot")
    print("   requires the cascade-native vertex-correction calculation,")
    print("   which is gated by oq:fermion-gauge-action.")
    print()
    print("VERDICT: digging into (g-2) shows the cascade-native calculation")
    print("is more complex than I initially suggested.  The 'a_f = alpha_em /")
    print("(2 pi)' identification reproduces Schwinger but is NOT a derivation.")
    print("Closing the m - k = 0 slot via (g-2) requires substantial")
    print("structural work in the cascade's gauge-coupled fermion action.")
    print()
    print("This DOES NOT yet justify committing the chirality selection")
    print("rule chi^(m-k) framework to Part IVb.  The closed-loop dual at")
    print("n=2 has empirical support (1/alpha_em screening at 0.006%); the")
    print("m - k = 0 slot has only structural-identification support, not")
    print("derivation.  Adding the framework to Part IVb at this point would")
    print("commit to a structure that's weakly tested at m - k = 0.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE-NATIVE (g-2) ANOMALOUS MAGNETIC MOMENT")
    print("Structural reading at 1-loop and the m - k = 0 framework gap")
    print("=" * 78)
    print()
    report_schwinger_structural()
    report_derivation_status()
    report_higher_loops()
    report_muon_tension()
    report_framework_gap_g_minus_2()
    report_summary()
    return 0


if __name__ == "__main__":
    sys.exit(main())
