#!/usr/bin/env python3
"""
n=4 closed-loop cascade observables: candidate tests of the closed-loop
chirality-factorisation conjecture beyond the n=2 photon self-energy.

CONTEXT
=======
The closed-loop chirality-factorisation conjecture (cascade_alpha_em_screening.py):

  I_Q(d) = chi * Gamma(1/2)^n = N(0) * Gamma(1/2)^n
  per-Dirac-layer topological invariant for an n-leg closed loop.

For n=2 (photon self-energy, two propagator legs in the loop):
  I_Q(d) = chi * pi = 2 pi  per Dirac layer.
  3 charged-fermion generations: 3 * 2 pi = 6 pi.
  Total 1/alpha_em = 137.030 vs observed 137.036, dev 0.005%.  ✓ (tested)

For n=4 (4-leg fermion box: 4 propagator legs at a single Dirac layer):
  I_Q(d) = chi * Gamma(1/2)^4 = 2 * pi^2  per Dirac layer.
  3 charged-fermion generations: 3 * 2 pi^2 = 6 pi^2.
  Cascade observables: NOT YET COMPUTED (this script).

THE CASCADE PRIMITIVE HIERARCHY
================================
Each higher-order closed-loop cascade primitive multiplies by
Gamma(1/2) = sqrt(pi) relative to the previous order:

  n   | per-Dirac-layer       | numerical | sum over 3 gen
  ----|-----------------------|-----------|----------------
  1*  | (2 sqrt(pi))^{-1}     | 0.282     | (open-line; *not closed)
  2   | chi * Gamma(1/2)^2    | 2 pi      | 6 pi   = 18.85 (1/alpha_em screening)
  3** | chi * Gamma(1/2)^3    | 2 pi^1.5  | 6 pi^1.5 = 33.4 (**triangle: requires internal boson)
  4   | chi * Gamma(1/2)^4    | 2 pi^2    | 6 pi^2 = 59.2  (this script's target)
  5** | chi * Gamma(1/2)^5    | 2 pi^2.5  | (**pentagon: requires internal boson)
  6   | chi * Gamma(1/2)^6    | 2 pi^3    | 6 pi^3 = 186   (hexagon, all-fermion)

* n=1 is the open-line case (Theorem 2.1), not a closed loop.
** n=3, 5 (odd) require internal boson lines; the all-fermion closed
   loop topology naturally exists only for even n.

CANDIDATE n=4 CASCADE OBSERVABLES
==================================
A 4-leg fermion box at a single Dirac layer corresponds in QFT to a
4-point amplitude with fermion-loop intermediate state.  Cascade
observables of this kind:

  (A) Light-by-light scattering: gamma gamma -> gamma gamma.
      4 external photon legs, fermion box in the middle.
      Observed at LHC by ATLAS in ultra-peripheral Pb-Pb collisions:
      sigma(gamma gamma -> gamma gamma) ~ 70 nb at sqrt(s) ~ 5 GeV.
      Cascade prediction: per-Dirac-layer 4-leg invariant
      times Q_f^4 charge weighting times kinematic phase space.

  (B) Hadronic light-by-light contribution to muon g-2.
      a_mu^{HLbL} = (9.2 +/- 1.9) x 10^{-10}  (recent SM estimates).
      Cascade prediction: contribution from fermion-box at the
      Dirac layers with quark content (color-charged).  Currently
      handled in SM via hadronic intermediates; cascade would
      compute it directly from the 4-leg loop primitive.

  (C) Heisenberg-Euler effective Lagrangian coefficients.
      At low energies, light-by-light contributes to the EH
      effective Lagrangian L_EH ~ (E^2 - B^2)^2 / m_e^4 etc.
      The dimensionless coefficient is purely cascade-internal
      and could be a clean cascade prediction.

  (D) Higher-order QED running of 1/alpha_em.
      2-loop QED contribution to 1/alpha_em(M_Z) -> 1/alpha_em(0):
      ~0.05.  Much smaller than n=2 (6 pi ~ 18.85); cascade's
      per-layer locality may not have a direct n=4 contribution
      to 1/alpha_em (the topology of the n=4 contribution would
      be a "vacuum polarisation insertion in a vacuum polarisation"
      diagram, which is not an n=4 single-layer fermion box).

THIS SCRIPT
===========
  1. Tabulates the cascade primitive hierarchy chi * Gamma(1/2)^n.
  2. Identifies candidate n=4 cascade observables (A)-(D).
  3. Notes which are tractable and which require new cascade
     machinery.
  4. Reports the most tractable next test as the gamma gamma ->
     gamma gamma cross section in the Heisenberg-Euler regime,
     where the cascade prediction reduces to a dimensionless
     coefficient comparable to QED's 1-loop fermion-box result.
"""

from __future__ import annotations

import math
import sys


# ---------------------------------------------------------------------------
# Cascade primitives (same as cascade_alpha_em_screening.py)
# ---------------------------------------------------------------------------

def Gamma_half() -> float:
    return math.sqrt(math.pi)


def N_zero() -> float:
    return 2.0


def chi_S2n() -> float:
    return 2.0


# ---------------------------------------------------------------------------
# Step 1: cascade primitive hierarchy
# ---------------------------------------------------------------------------

def report_hierarchy():
    print("=" * 78)
    print("STEP 1: cascade primitive hierarchy chi * Gamma(1/2)^n")
    print("=" * 78)
    print()
    print("Each higher-order closed-loop primitive multiplies by Gamma(1/2)")
    print("relative to the previous; the cascade has a discrete tower of")
    print("topological invariants per Dirac layer indexed by n (number of")
    print("propagator legs in the closed loop).")
    print()
    chi = chi_S2n()
    g = Gamma_half()
    print(f"  {'n':>3s}  {'topology':<35s}  {'per-Dirac-layer':<22s}  {'value':>10s}  {'sum (3 gen)':>12s}")
    print("  " + "-" * 95)
    rows = [
        (1, "open line (NOT closed)", "(2 sqrt(pi))^{-1}", 1.0/(chi*g), None, "(open-line obstruction; Thm 2.1)"),
        (2, "self-energy (2 fermion legs)", "chi * Gamma(1/2)^2", chi*g**2, 3*chi*g**2, "1/alpha_em screening (verified 0.006%)"),
        (3, "triangle (req. internal boson)", "chi * Gamma(1/2)^3", chi*g**3, 3*chi*g**3, "vertex correction (per-layer-local issue)"),
        (4, "box (4 fermion legs)", "chi * Gamma(1/2)^4", chi*g**4, 3*chi*g**4, "light-by-light (untested)"),
        (5, "pentagon (req. internal boson)", "chi * Gamma(1/2)^5", chi*g**5, 3*chi*g**5, "5-point correction"),
        (6, "hexagon (6 fermion legs)", "chi * Gamma(1/2)^6", chi*g**6, 3*chi*g**6, "6-photon scattering"),
    ]
    for n, topo, formula, val, sum3, note in rows:
        sum3_str = f"{sum3:>10.3f}" if sum3 else "(open)"
        print(f"  {n:>3d}  {topo:<35s}  {formula:<22s}  {val:>10.4f}  {sum3_str:>12s}  {note}")
    print()
    print("The hierarchy spans a wide numerical range:")
    print(f"  n=2 closed-loop primitive 2*pi             = {2*math.pi:.3f}")
    print(f"  n=4 closed-loop primitive 2*pi^2           = {2*math.pi**2:.3f}")
    print(f"  n=6 closed-loop primitive 2*pi^3           = {2*math.pi**3:.3f}")
    print()
    print("Each layer contributes the SAME primitive regardless of d (layer-")
    print("independent, forced by data at n=2: see cascade_alpha_em_screening.py")
    print("Step 4.5 stress test).  The 3-generation sum scales linearly with N_gen.")
    print()


# ---------------------------------------------------------------------------
# Step 2: candidate n=4 observables
# ---------------------------------------------------------------------------

def report_n4_candidates():
    print("=" * 78)
    print("STEP 2: candidate n=4 cascade observables")
    print("=" * 78)
    print()
    print("A 4-leg fermion box at a single Dirac layer is the cascade analog")
    print("of a 4-point amplitude with fermion-loop intermediate state.  Four")
    print("candidate observables:")
    print()
    print("  (A) gamma gamma -> gamma gamma scattering (light-by-light)")
    print("      ----------------------------------------------------------")
    print("      Topology: 4 external photons attached to a fermion box.")
    print("      Cascade structure: per-Dirac-layer 4-leg invariant 2 pi^2,")
    print("      times Q_f^4 charge weighting (each photon vertex), summed")
    print("      over charged-fermion species and generations.")
    print()
    print("      Sum of Q_f^4 per generation:")
    print("        e (Q=-1):                 1")
    print("        u (Q=2/3, N_c=3 colors):  3 * (2/3)^4 = 16/27")
    print("        d (Q=-1/3, N_c=3 colors): 3 * (1/3)^4 = 1/27")
    sum_Qf4 = 1.0 + 16.0/27 + 1.0/27
    print(f"        per generation:           {sum_Qf4:.4f}")
    print(f"        3 generations:            {3*sum_Qf4:.4f}")
    print()
    print(f"      Cascade structural coefficient (dimensionless):")
    print(f"        per Dirac layer * Q_f^4 sum:  2 pi^2 * (44/27) = {2*math.pi**2 * sum_Qf4:.4f}")
    print(f"        3 generations:                6 pi^2 * (44/27) = {6*math.pi**2 * sum_Qf4:.4f}")
    print()
    print("      Comparison to QED 1-loop result requires the kinematic")
    print("      phase-space factor and external-photon coupling structure.")
    print("      LHC measurement (ATLAS UPC Pb-Pb): sigma ~ 70 +/- 24 nb at")
    print("      sqrt(s) ~ 5 GeV.  Comparing requires the cascade's full")
    print("      cross-section formula at low energies, not yet developed.")
    print()
    print("  (B) Hadronic light-by-light contribution to muon (g-2)")
    print("      ----------------------------------------------------------")
    print("      a_mu^{HLbL} = (9.2 +/- 1.9) * 10^{-10}  (Lattice + dispersive)")
    print("      Cascade structure: 4-leg fermion box at quark Dirac layers")
    print("      with hadronic intermediates.  In SM, computed via hadronic")
    print("      vacuum polarisation + dispersion; in cascade, would be a")
    print("      direct application of the n=4 closed-loop invariant at the")
    print("      relevant Dirac layers.")
    print()
    print("      Cascade prediction structure: 6 pi^2 / (cascade-natural")
    print("      mass-scale factors).  Specific numerical prediction requires")
    print("      a cascade-native (g-2) calculation framework, which does")
    print("      not currently exist in the cascade papers.")
    print()
    print("  (C) Heisenberg-Euler effective Lagrangian coefficients")
    print("      ----------------------------------------------------------")
    print("      At low photon energies, light-by-light scattering is encoded")
    print("      in the Heisenberg-Euler effective Lagrangian:")
    print("        L_EH = (alpha^2 / 90 m_e^4) * [(E^2 - B^2)^2 + 7 (E.B)^2]")
    print("      The coefficient 1/90 is dimensionless and arises from the")
    print("      QED 1-loop fermion-box at the lepton mass scale.")
    print()
    print("      Cascade analog: dimensionless coefficient = (cascade")
    print("      4-leg invariant per Dirac layer) / (kinematic normalisation).")
    print("      QED's 1/90 factors as (kinematic) / (alpha^2 m_e^4) chain;")
    print("      the cascade's prediction for the analog requires explicit")
    print("      cascade-native fermion-box calculation.")
    print()
    print("      MOST TRACTABLE TEST: the dimensionless coefficient 1/90")
    print("      of Heisenberg-Euler is universally electron-loop-derived.")
    print("      A cascade derivation that replaces the QED loop integral")
    print("      with the per-Dirac-layer primitive 2 pi^2 (electron's")
    print("      Gen 1 layer at d=21) would be a clean test.")
    print()
    print("  (D) Higher-order QED running of 1/alpha_em")
    print("      ----------------------------------------------------------")
    print("      2-loop QED contribution to 1/alpha_em(M_Z) -> 1/alpha_em(0):")
    print("      delta(1/alpha) ~ 0.05 (small).")
    print()
    print("      Cascade interpretation: the n=2 closed-loop primitive 2 pi")
    print("      gives the FIRST-ORDER screening (1-loop fermion bubble in")
    print("      photon self-energy).  The n=4 primitive 2 pi^2 would")
    print("      naturally give... what?  A 4-leg fermion box has 4 external")
    print("      photon vertices, which is not a 2-point function and does")
    print("      NOT contribute to 1/alpha_em (which is a 2-point-function")
    print("      coefficient).")
    print()
    print("      So the n=4 closed-loop primitive does NOT contribute to")
    print("      1/alpha_em.  It contributes to 4-point amplitudes (gamma")
    print("      gamma -> gamma gamma, etc.).  The cascade's per-layer")
    print("      locality means there is no '2-loop correction to 1/alpha_em'")
    print("      from a 4-leg insertion; the topology is different.")
    print()


# ---------------------------------------------------------------------------
# Step 3: structural prediction for Heisenberg-Euler
# ---------------------------------------------------------------------------

def report_heisenberg_euler():
    print("=" * 78)
    print("STEP 3: structural prediction for Heisenberg-Euler coefficient")
    print("=" * 78)
    print()
    print("The Heisenberg-Euler effective Lagrangian at one loop:")
    print()
    print("  L_EH = (alpha^2 / (90 m_e^4)) * [(E^2 - B^2)^2 + 7 (E.B)^2]")
    print()
    print("The dimensionless coefficient 1/90 comes from the QED 1-loop")
    print("fermion-box integral.  Its derivation in standard QED involves")
    print("the box integral over loop momentum, with the result")
    print("  (factor) = 4/(45 pi^2) [Heisenberg & Euler 1936]")
    print("  rearranged to the prefactor 1/90 in the Lagrangian.")
    print()
    print("Cascade analog: replace the QED loop integral with the cascade's")
    print("per-Dirac-layer 4-leg invariant 2 pi^2, weighted by external-")
    print("photon coupling and divided by the appropriate kinematic")
    print("normalisation.")
    print()
    print("Possible cascade-native form for the EH coefficient (CONJECTURE):")
    print()
    print("  (per-Dirac-layer 4-leg invariant) / (kinematic phase factor)")
    print("    = 2 pi^2 / (cascade kinematic factor)")
    print()
    print("To test against 1/90: requires the cascade kinematic factor to")
    print("equal 90 * 2 pi^2 / 1 = 180 pi^2, which is an integer multiple")
    print("of pi^2.  Whether the cascade naturally produces this kinematic")
    print("factor is open.")
    print()
    print("Numerical plausibility check:")
    target = 1.0 / 90.0
    cascade_4leg = 2 * math.pi**2
    needed_kinematic = cascade_4leg / target
    print(f"  Target EH coefficient: 1/90 = {target:.6f}")
    print(f"  Cascade 4-leg invariant: 2 pi^2 = {cascade_4leg:.4f}")
    print(f"  Required cascade kinematic factor: 2 pi^2 / (1/90) = {needed_kinematic:.4f}")
    print(f"  As a multiple of pi^2: {needed_kinematic / math.pi**2:.4f}")
    print(f"  Comparison: 180 = {180/math.pi**2:.4f} * pi^2  (180 in units of pi^2)")
    print(f"  Or: pi^4 * something = ?  pi^4 = {math.pi**4:.4f}")
    print()
    print("The required factor 180 pi^2 = 1776 numerically; or 18 pi^4 = 1753")
    print("(close to 1776, off by 1.3%); or 4 pi^6 = 3845 (factor 2 off).")
    print()
    print("None of these natural cascade primitives gives EXACTLY 180 pi^2,")
    print("so the cascade cannot directly reproduce 1/90 as a single-")
    print("primitive expression.  The QED coefficient might instead be the")
    print("RATIO of a cascade kinematic factor to the n=4 invariant; the")
    print("specific match would require working out the cascade's kinematic")
    print("structure for 4-photon scattering.")
    print()


# ---------------------------------------------------------------------------
# Step 4: framework gap and tractable next steps
# ---------------------------------------------------------------------------

def report_framework_gap():
    print("=" * 78)
    print("STEP 4: framework gap and tractable next steps")
    print("=" * 78)
    print()
    print("The n=4 closed-loop chirality-factorisation conjecture predicts")
    print("specific structural contributions to 4-leg cascade observables,")
    print("but the cascade's current framework is undeveloped at this level:")
    print()
    print("FRAMEWORK GAP: the cascade has NO developed calculation for")
    print("higher-point amplitudes.  Existing predictions are:")
    print("  - Mass spectrum (open-line cascade descent, mass formula)")
    print("  - Gauge couplings (open-line descent + n=2 closed-loop screening")
    print("    for 1/alpha_em)")
    print("  - Cosmological parameters (functions of pi)")
    print("Nothing in the cascade currently computes:")
    print("  - 4-photon scattering cross-sections")
    print("  - Anomalous magnetic moments (g-2)")
    print("  - Heisenberg-Euler effective Lagrangian coefficients")
    print("  - Hadronic light-by-light contributions")
    print()
    print("To test the n=4 rule, the cascade needs a framework for:")
    print("  1. 4-point amplitudes with fermion-box intermediate states.")
    print("  2. Kinematic factors at low energies (Heisenberg-Euler regime).")
    print("  3. Charge weighting (Q_f^4 sums) in cascade-native form.")
    print()
    print("Without this framework, the n=4 rule's prediction 2 pi^2 per")
    print("Dirac layer is currently UNTESTABLE in the cascade.  The rule")
    print("makes a clear structural prediction but cannot yet be confronted")
    print("with observation.")
    print()
    print("MOST TRACTABLE NEXT STEPS (in order of difficulty):")
    print()
    print("  1. SCALAR n=4 closed-loop testbed.  Before tackling spinor")
    print("     fermion boxes, compute the scalar analog: phi^4 vertex on")
    print("     the cascade lattice with two scalar pairs forming a closed")
    print("     loop.  The cascade scalar action S = sum_d (2 alpha)^{-1}")
    print("     (Delta phi)^2 + lambda phi^4 / 4! is well-defined; the")
    print("     scalar n=4 closed-loop primitive should be 2 pi^2 per")
    print("     Dirac layer if the rule generalises beyond the gauge sector.")
    print()
    print("  2. CASCADE-NATIVE EH COEFFICIENT.  Set up the gauge-coupled")
    print("     fermion action at the U(1) layer (rem:fermion-gauge-coupling-")
    print("     proposal) and compute the dimensionless coefficient of the")
    print("     4-photon EH Lagrangian.  The cascade-native answer should")
    print("     factor as (per-Dirac-layer 4-leg invariant) / (kinematic")
    print("     factor) for some cascade-natural kinematic factor.")
    print()
    print("  3. PROOF OF THE CHIRALITY-FACTORISATION RULE AT n=4.  Extend")
    print("     the closed-loop chirality-factorisation theorem proof sketch")
    print("     (cascade_alpha_em_screening.py Step 5) from n=2 to general")
    print("     even n.  The proof must show that the per-leg cascade Jacobian")
    print("     primitive Gamma(1/2) is intrinsic for arbitrary n, and that")
    print("     the chirality multiplicity remains chi (one closure per loop)")
    print("     regardless of leg count.")
    print()
    print("Steps 1 and 2 are tractable mathematical exercises that don't")
    print("require new cascade theorems; step 3 is structural/theoretical.")
    print()


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

def report_summary():
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print()
    print("The closed-loop chirality-factorisation rule at n=4 predicts:")
    print(f"  per-Dirac-layer = chi * Gamma(1/2)^4 = 2 pi^2 = {2*math.pi**2:.4f}")
    print(f"  3 charged generations: 3 * 2 pi^2 = 6 pi^2 = {6*math.pi**2:.4f}")
    print()
    print("Candidate cascade observables:")
    print("  (A) gamma gamma -> gamma gamma scattering")
    print("  (B) Hadronic LbL contribution to muon (g-2)")
    print("  (C) Heisenberg-Euler effective Lagrangian coefficient")
    print("  (D) NOT 1/alpha_em (n=4 doesn't contribute to 2-point function)")
    print()
    print("Status: rule is well-defined, predictions are clear, but the")
    print("cascade's framework for higher-point amplitudes is undeveloped.")
    print("Most tractable next test: scalar phi^4 closed-loop on the cascade")
    print("lattice as a testbed before tackling spinor fermion boxes.")
    print()
    print("If the rule passes the n=4 test (e.g., reproduces 1/90 in")
    print("Heisenberg-Euler), the closed-loop chirality-factorisation")
    print("conjecture is strongly supported as a cascade theorem.")
    print()
    print("If the rule fails at n=4 but holds at n=2, the conjecture has")
    print("a structural restriction (e.g., applies only to gauge boson")
    print("self-energies, not generic 4-leg amplitudes).  This would be")
    print("important to know.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE n=4 CLOSED-LOOP OBSERVABLES")
    print("Tests of the closed-loop chirality-factorisation rule beyond n=2")
    print("=" * 78)
    print()
    report_hierarchy()
    report_n4_candidates()
    report_heisenberg_euler()
    report_framework_gap()
    report_summary()
    return 0


if __name__ == "__main__":
    sys.exit(main())
