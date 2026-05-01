#!/usr/bin/env python3
"""
Systematic test of the cascade n=4 closed-loop prediction
against three candidate physical observables.

CONTEXT
=======
After the chirality selection rule (thm:chirality-selection-rule, PR #117),
the per-leg primitive derivation (rem:per-leg-primitive-derivation), and
the wavefunction-renormalisation grounding (rem:wavefunction-renorm-canonical),
the cascade structurally predicts that any observable Q with a 4-leg
closed-loop topology at a Dirac layer carries the cascade-internal factor

    Delta(Q)_d = chi * Gamma(1/2)^4 = 2*pi^2  per Dirac layer (LAYER-INDEPENDENT)

with three Dirac layers d in {5, 13, 21} (one per fermion generation), giving
total 6*pi^2 ~ 59.22 if all three layers contribute.

The prediction is structurally forced once n=2 (the 1/alpha_em closure) is
accepted: the same chirality theorem and proper-time / Gaussian propagator
that close 137.028 also force the n=4 form for any cascade observable that
naturally lives at 4-leg closed-loop topology.

Per-layer locality of the cascade fermion (rem:fermion-gauge-coupling-proposal)
is a STRONG constraint at higher loops.  It admits 4-leg closed loops at a
single Dirac layer (e.g., a fermion box with 4 external boson legs) but
EXCLUDES topologies that require fermion propagation between layers (e.g.,
the standard 2-loop QED triangle topology in (g-2)).  The cascade's n=4
prediction therefore lives in observables that:
  (i)  Have 4-leg closed-loop topology
  (ii) Are computable at a single Dirac layer

Three candidate observables that satisfy both conditions:

  (A) Light-by-light scattering gamma gamma -> gamma gamma:
      4 external photons attached to a single fermion box at a Dirac layer.
      Measured by ATLAS in Pb-Pb UPC: sigma ~ 70 +/- 24 nb at sqrt(s) ~ 5 GeV.

  (B) (g-2) at 2-loop, single-layer topologies only:
      m=2 closed loops + k=1 external fermion mode within per-layer
      locality.  m-k = +1, so chirality factor chi^1 = 2; per-leg primitive
      Gamma(1/2)^4 = pi^2; total 2*pi^2 per Dirac layer for the
      single-layer-allowed topology.

  (C) Higgs quartic coupling lambda correction:
      Higgs lives at d=13 (Dirac layer).  4-leg vertex correction at d=13.
      Cascade prediction: structural cascade factor 2*pi^2 (one Dirac layer
      contribution; Higgs lives at d=13 only, not at d=5, 21).

This script systematically tests the cascade prediction against each.

KEY PROBLEM
===========
Standard QFT amplitudes for these observables have a mass-dependent
decoupling: heavy fermion contributions scale as 1/m_f^4 (Heisenberg-Euler
behaviour in the low-energy limit).  The cascade's "layer-independent"
prediction implies NO mass decoupling: every Dirac layer contributes
equally regardless of the fermion mass at that layer.

This is a STRUCTURAL tension between cascade and standard QFT.  Resolution
options:
  (1) Cascade is wrong at higher loops; per-leg primitive needs revision.
  (2) Cascade is correct but its prediction is for the HIGH-ENERGY /
      asymptotic regime where mass decoupling is absent.
  (3) Cascade is correct and applies to a CASCADE-INTERNAL observable
      that has no direct QFT analog at the dimensional / mass-scale level.

This tool explores each option.

WHAT THIS SCRIPT DOES
=====================
  1. Computes the cascade n=4 prediction for each observable.
  2. Computes the standard QFT prediction (where known) for comparison.
  3. Reports the dimensional / structural mismatch for each.
  4. Identifies which option (1), (2), or (3) best fits each case.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Resolve the tension.  Identifies the gap and three resolution paths.
  - Compute full cross sections.  Uses leading dimensional / structural
    estimates.
  - Make a claim that the cascade fully predicts these observables.
"""

from __future__ import annotations

import math


# ---------------------------------------------------------------------------
# Cascade primitives
# ---------------------------------------------------------------------------

def R_cascade(d: int) -> float:
    return math.exp(math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0))


def alpha_cascade(d: int) -> float:
    return R_cascade(d) ** 2 / 4.0


CHI = 2
GAMMA_HALF = math.sqrt(math.pi)
DIRAC_LAYERS = [5, 13, 21]  # Gen 3, 2, 1
N_GEN = 3


def cascade_n4_invariant_per_layer() -> float:
    return CHI * GAMMA_HALF ** 4   # = 2 * pi^2


def cascade_n4_invariant_total() -> float:
    return N_GEN * cascade_n4_invariant_per_layer()  # = 6 * pi^2


# ---------------------------------------------------------------------------
# Test (A): Light-by-light scattering gamma gamma -> gamma gamma
# ---------------------------------------------------------------------------

def test_light_by_light():
    """
    QED at 1-loop: gamma gamma -> gamma gamma is a fermion-box amplitude.
    At low energy (Heisenberg-Euler regime), the effective Lagrangian is

        L_EH = (alpha^2 / (90 m_e^4)) * [(F.F)^2 + (7/4)(F.F~)^2]

    The dimensionless coefficient 1/90 is the famous Euler-Heisenberg
    constant, derived from the QED 1-loop fermion box at the electron mass.

    Cascade prediction: per-Dirac-layer 4-leg invariant = 2*pi^2 = 19.74,
    times Q_f^4 charge weighting per fermion species.

    Sum of Q_f^4 per generation:
      e (Q=-1):                      1
      u-type (Q=2/3, N_c=3):        3 * (2/3)^4 = 16/27
      d-type (Q=-1/3, N_c=3):       3 * (1/3)^4 =  1/27
      Total per generation:          1 + 16/27 + 1/27 = 1.630
      Total 3 generations:           3 * 1.630 = 4.889

    Cascade structural coefficient summed over 3 generations:
      6*pi^2 * 4.889 = 289.5

    For comparison with QED's 1/90:
      Need cascade dimensionless coefficient / kinematic factor = 1/90
      Cascade gives 6*pi^2 with no obvious kinematic suppression.

    OPTION (1): cascade overshoots by factor 6*pi^2 / (1/90) = 540*pi^2 ~ 5330.
    OPTION (2): cascade's 6*pi^2 is the high-energy regime where mass
    decoupling is absent; QED's 1/m^4 scaling is the low-energy limit.
    OPTION (3): cascade's 6*pi^2 is a structural invariant; the kinematic /
    dimensional factors needed to convert it to a 4-photon amplitude
    require additional cascade machinery (e.g., heat-kernel-on-cascade-
    lattice with 4-derivative coefficient).
    """
    print("=" * 78)
    print("TEST (A): Light-by-light scattering gamma gamma -> gamma gamma")
    print("=" * 78)
    print()

    # Sum of charge-weighted per-generation contribution
    Q4_e = 1.0          # electron, Q=-1
    Q4_u = 3 * (2/3)**4 # 3 colors, Q=2/3
    Q4_d = 3 * (1/3)**4 # 3 colors, Q=-1/3
    Q4_per_gen = Q4_e + Q4_u + Q4_d
    Q4_total = N_GEN * Q4_per_gen

    cascade_invariant = cascade_n4_invariant_total()
    cascade_coef = cascade_invariant * Q4_per_gen   # per-layer * Q_f^4 per gen
    cascade_coef_3gen = cascade_invariant * Q4_per_gen  # already includes N_gen

    qed_coef = 1.0 / 90.0  # Heisenberg-Euler dimensionless coefficient

    ratio = cascade_coef / qed_coef

    print(f"  Charge weighting:")
    print(f"    Q_e^4 (electron):    {Q4_e:.4f}")
    print(f"    sum_quarks Q^4 (up): {Q4_u:.4f}")
    print(f"    sum_quarks Q^4 (dn): {Q4_d:.4f}")
    print(f"    per generation:      {Q4_per_gen:.4f}")
    print(f"    3 generations:       {Q4_total:.4f}")
    print()
    print(f"  Cascade prediction (3 generations, charge-weighted):")
    print(f"    6*pi^2 * (Q^4 sum) = {cascade_coef_3gen:.4f}")
    print()
    print(f"  QED 1-loop EH coefficient:  1/90 = {qed_coef:.6f}")
    print(f"  Ratio cascade / QED:        {ratio:.2f}")
    print(f"  Logarithmic mismatch:       log10 = {math.log10(ratio):.2f}")
    print()
    print(f"  STRUCTURAL TENSION: cascade's layer-independent prediction implies")
    print(f"  NO mass decoupling.  QED's 1/m_f^4 scaling makes muon and tau")
    print(f"  loops negligible compared to electron.  At LHC LbL energies")
    print(f"  (~5 GeV), only electron loop is well above threshold; cascade")
    print(f"  predicts equal contribution from all three generations.")
    print()
    print(f"  RESOLUTION:")
    print(f"  (1) Reject cascade n=4 prediction at face value.")
    print(f"  (2) Cascade prediction is for high-energy regime; needs explicit")
    print(f"      threshold/decoupling structure to compare with low-E EH.")
    print(f"  (3) Cascade 4-leg invariant is structural; needs kinematic")
    print(f"      conversion (heat-kernel structure on cascade lattice) to")
    print(f"      give the QFT 4-photon amplitude.  Open problem.")
    print()


# ---------------------------------------------------------------------------
# Test (B): (g-2) at 2-loop, single-layer topologies only
# ---------------------------------------------------------------------------

def test_g_minus_2_2loop():
    """
    Standard QED 2-loop contribution to a_e:
        a_e^(4) = (-0.328478965...) * (alpha/pi)^2

    The 2-loop topologies in QED include:
      - Photon self-energy insertion in the 1-loop vertex (3 diagrams)
      - Vertex correction to the 1-loop vertex (4 diagrams)
      - Two crossed photons (1 diagram)

    Per-layer locality of the cascade fermion EXCLUDES topologies that
    require fermion propagation between Dirac layers.  At 2-loop with
    fermion propagation entirely within a single Dirac layer, the
    accessible topology has m=2 closed loops and k=1 external fermion mode.

    Cascade prediction (from chirality selection rule + per-leg primitive):
      chirality factor: chi^(m-k) = chi^1 = 2
      per-leg primitive: 4 propagator legs total in 2 loops -> Gamma(1/2)^4 = pi^2
      cascade structural factor: chi * pi^2 = 2*pi^2 per Dirac layer

    Numerically: 2*pi^2 ~ 19.74 per layer.
    QED 2-loop coefficient: |A^(4)| = 0.328 (sub-unity).
    Ratio cascade/QED: 19.74 / 0.328 = 60.

    Cascade overshoots QED 2-loop by factor 60.  Note this is NOT the same
    factor as the LbL test (5300); the cascade prediction at m-k=+1 carries
    one factor of chi less than at m=4 closed-loop topology.

    PRIOR FINDING: tools/research/cascade_g_minus_2_investigation.py
    notes that cascade gives 0.15 * 0.328 = 0.05 at 2-loop, factor 6
    UNDERSHOOT of QED.  The discrepancy with the present analysis suggests
    the 2-loop cascade calculation is doing something different from the
    pure n=4 closed-loop prediction here.  Per-layer locality may be
    excluding the dominant 2-loop QED topologies entirely, leaving only
    a small subset that doesn't reach 2*pi^2.

    Most likely interpretation: per-layer locality of the cascade fermion
    EXCLUDES the standard QED 2-loop topology (the (g-2) 2-loop has the
    fermion propagating between vertices through a non-trivial spacetime
    region), and the cascade has NO 2-loop (g-2) prediction in the
    standard sense.
    """
    print("=" * 78)
    print("TEST (B): (g-2) at 2-loop, single-layer topologies only")
    print("=" * 78)
    print()
    print(f"  QED 2-loop coefficient: |A^(4)| = 0.328478965...")
    print(f"  Cascade m-k=+1 (m=2 closed loops, k=1 external mode):")
    print(f"    chirality factor:   chi^1 = {CHI}")
    print(f"    per-leg primitive:  Gamma(1/2)^4 = pi^2 = {math.pi**2:.4f}")
    print(f"    structural factor:  chi * pi^2 = 2*pi^2 = {2*math.pi**2:.4f}")
    print()
    print(f"  Ratio cascade/QED structural: 2*pi^2 / 0.328 = {2*math.pi**2/0.328:.2f}")
    print()
    print(f"  STRUCTURAL TENSION: per-layer locality of the cascade fermion")
    print(f"  excludes the standard QED 2-loop topology (which requires")
    print(f"  fermion propagation between vertices in spacetime, not within")
    print(f"  a single Dirac layer).  The cascade's m-k=+1 prediction at")
    print(f"  2*pi^2 lives in a different topology than QED's |A^(4)|.")
    print()
    print(f"  PRIOR FINDING (cascade_g_minus_2_investigation.py):")
    print(f"    cascade 2-loop gives 0.05, factor 6 UNDERSHOOT of QED 0.328.")
    print(f"    Suggests per-layer locality EXCLUDES dominant 2-loop")
    print(f"    topologies, leaving a small structural remnant.")
    print()
    print(f"  CONCLUSION: cascade 2-loop (g-2) is not directly predicted by")
    print(f"  the n=4 closed-loop primitive; per-layer locality kills the")
    print(f"  topology.  This is a NEGATIVE test of the n=4 prediction in")
    print(f"  the (g-2) channel, but consistent with cascade's own constraints.")
    print()


# ---------------------------------------------------------------------------
# Test (C): Higgs quartic coupling lambda correction at d=13
# ---------------------------------------------------------------------------

def test_higgs_quartic():
    """
    Higgs lives at d=13 (a Dirac layer where SU(2) is broken).  A 4-leg
    closed-loop correction to the Higgs quartic lambda from a fermion
    box at d=13 has cascade structural factor 2*pi^2 per layer.

    Standard SM 1-loop running of lambda:
        d lambda / d ln mu = (1/(16 pi^2)) * [
            24 lambda^2 - 6 y_t^4 + (3/8)(2 g^4 + (g^2 + g'^2)^2)
            + 12 lambda y_t^2 - 9 lambda (g^2 + (g'^2)/3) ]

    The y_t^4 term is the top-quark 4-leg closed loop at d=12 (not d=13).
    The cascade has top at gauge-window layers d in {12, 13, 14}, and the
    top's box loop at d=12 (or 13) feeds into lambda renormalisation.

    Cascade prediction for the top-loop contribution to delta lambda:
      Cascade 4-leg invariant: 2*pi^2 (per layer, layer-independent)
      Top-quark Q-weighting:   y_t^4 (where y_t is top Yukawa)
      Cascade structural:      2*pi^2 * y_t^4 (per Dirac layer; top is at
                               one specific layer)

    SM coefficient of -6 y_t^4 / (16 pi^2):
      Pre-factor: -6 / (16 pi^2) = -0.038 (dimensionless)

    Ratio cascade / SM: 2*pi^2 / 0.038 = 520
    Same factor-of-O(100s) overshoot as LbL.

    INTERPRETATION: same as LbL.  Cascade's "layer-independent" prediction
    implies all Dirac layers contribute equally; SM has top dominating via
    y_t^4 because the top is the heaviest fermion.  The cascade's structural
    invariant 2*pi^2 is not the SM beta-function coefficient.
    """
    print("=" * 78)
    print("TEST (C): Higgs quartic coupling lambda correction at d=13")
    print("=" * 78)
    print()
    print(f"  Higgs lives at d=13 (Dirac layer; SU(2) broken).")
    print(f"  4-leg closed-loop correction to lambda from fermion box at d=13")
    print(f"  (e.g., top-quark loop at gauge-window layer feeding into lambda).")
    print()
    print(f"  Cascade prediction: 2*pi^2 = {2*math.pi**2:.4f} per Dirac layer")
    print(f"  SM 1-loop coefficient of y_t^4 in lambda beta function: -6/(16*pi^2) = {-6/(16*math.pi**2):.4f}")
    print()
    print(f"  Ratio cascade/SM: 2*pi^2 / |6/(16*pi^2)| = {2*math.pi**2 / (6/(16*math.pi**2)):.2f}")
    print()
    print(f"  STRUCTURAL TENSION: same as LbL.  Cascade's layer-independent")
    print(f"  prediction overshoots the SM beta-function coefficient by")
    print(f"  factor ~500.  The y_t^4 dependence in SM is the top-mass")
    print(f"  scaling; cascade has no analog at the structural level.")
    print()


# ---------------------------------------------------------------------------
# Synthesis: pattern across all three tests
# ---------------------------------------------------------------------------

def synthesis():
    print("=" * 78)
    print("SYNTHESIS")
    print("=" * 78)
    print()
    print("All three tests show a STRUCTURAL OVERSHOOT of the cascade n=4")
    print("prediction relative to standard QFT predictions:")
    print()
    print(f"  Test (A) light-by-light:       cascade ~ 5300 * QED")
    print(f"  Test (B) (g-2) 2-loop:         cascade ~ 60 * QED")
    print(f"  Test (C) Higgs quartic:        cascade ~ 500 * SM")
    print()
    print("The factor varies but cascade always overshoots.  The pattern is")
    print("consistent: standard QFT has MASS DECOUPLING (heavy fermion")
    print("contributions scale as 1/m_f^4, suppressing them); cascade has")
    print("LAYER INDEPENDENCE (every Dirac layer contributes equally).")
    print()
    print("STATUS OF THE n=4 PREDICTION")
    print("-" * 78)
    print()
    print("The structural form chi * Gamma(1/2)^n at higher n is FORCED by:")
    print("  - thm:chirality-selection-rule (closed-loop multiplicity, Step B)")
    print("  - rem:per-leg-primitive-derivation (1D Gaussian / proper-time)")
    print("  - rem:wavefunction-renorm-canonical (canonical normalisation)")
    print()
    print("The structural form predicts 2*pi^2 per Dirac layer for any cascade")
    print("observable with 4-leg closed-loop topology.  This is NOT a free")
    print("prediction; it is forced by accepting the n=2 closure of 1/alpha_em.")
    print()
    print("HOWEVER: the QFT amplitudes that LOOK LIKE 4-leg closed loops")
    print("(LbL, 2-loop g-2, Higgs quartic) DO NOT match the cascade's 2*pi^2")
    print("at face value.  The discrepancy ranges from O(60) to O(5000).")
    print()
    print("RESOLUTION OPTIONS")
    print("-" * 78)
    print()
    print("Option (1): cascade is wrong at higher loops.")
    print("  This would require revising the per-leg primitive at n>=3, or")
    print("  identifying a topology obstruction that excludes n>=3 entirely.")
    print("  But the structural form IS forced by the chirality theorem; if")
    print("  rejected, the chirality theorem itself needs to be questioned.")
    print()
    print("Option (2): cascade prediction is for high-energy / asymptotic regime.")
    print("  In QFT, the LOW-ENERGY effective Lagrangian carries 1/m_f^4")
    print("  factors that decouple heavy fermions.  At HIGH ENERGY (above all")
    print("  fermion thresholds), the amplitude becomes mass-independent.  The")
    print("  cascade's layer-independent 2*pi^2 might be the high-energy limit.")
    print("  Test: compute QED LbL at sqrt(s) >> all m_f and compare to")
    print("  cascade prediction.  Tractable but requires explicit calculation.")
    print()
    print("Option (3): the cascade observables that naturally live at n=4 are")
    print("  CASCADE-INTERNAL, with no direct QFT amplitude analog.  The 2*pi^2")
    print("  per layer would then be a structural invariant of the cascade")
    print("  itself, not directly comparable to QFT amplitudes.  Examples:")
    print("    - 4-point cascade scalar correlator at a Dirac layer")
    print("    - 4-fold compositional cascade descent")
    print("    - Cascade-internal Gauss-Bonnet term")
    print()
    print("RECOMMENDED NEXT STEP")
    print("-" * 78)
    print()
    print("Pursue Option (2) first: compute QED LbL amplitude at high energy")
    print("(asymptotic regime, sqrt(s) >> all m_f).  If the leading")
    print("dimensionless coefficient matches 6*pi^2 in the high-E limit,")
    print("Option (2) is confirmed and the cascade's n=4 prediction is")
    print("validated as the asymptotic invariant.")
    print()
    print("If Option (2) fails numerically, pursue Option (3): identify a")
    print("cascade-internal observable (not a QFT amplitude) at n=4.")
    print()
    print("If both fail, Option (1) becomes the working hypothesis: the")
    print("cascade per-leg primitive does NOT extend cleanly beyond n=2,")
    print("indicating that the chirality-selection-rule structural derivation")
    print("requires refinement at higher n.")
    print()


def main():
    print()
    print("CASCADE n=4 PREDICTION: SYSTEMATIC TEST AGAINST PHYSICAL OBSERVABLES")
    print()
    print(f"Cascade per-Dirac-layer 4-leg invariant: chi * Gamma(1/2)^4 = "
          f"2*pi^2 = {cascade_n4_invariant_per_layer():.4f}")
    print(f"Sum over 3 generations: 6*pi^2 = {cascade_n4_invariant_total():.4f}")
    print()
    test_light_by_light()
    test_g_minus_2_2loop()
    test_higgs_quartic()
    synthesis()


if __name__ == "__main__":
    main()
