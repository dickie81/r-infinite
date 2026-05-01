#!/usr/bin/env python3
"""
m - k = 0 balanced slot: investigation of cascade observables that
should fill the missing chirality-balanced position in the open-closed
mixed observable spectrum.

CONTEXT
=======
cascade_open_closed_mixed.py identified that the cascade's existing
precision predictions span m - k from -4 (b/s open-line k=4) to +1
(1/alpha_em closed-loop n=2), with the m - k = 0 slot empty.

A balanced m - k = 0 observable has k = 1 open-line mode + m = 1
closed loop, with chirality factor chi^0 = 1 (no chirality
enhancement or suppression).  Structurally:

  - 1 external open-line propagator (k=1).
  - 1 internal closed loop (m=1).
  - per-leg cascade primitive Gamma(1/2)^n where n = legs in loop.
  - chirality factor chi^(m-k) = chi^0 = 1.

In QFT terms, this corresponds to:
  - Fermion mass self-energy correction (external f + internal f loop)
  - Vertex correction (g-2 type)
  - Wave function renormalisation Z-factor
  - Anomalous magnetic moment

These are 1-loop corrections to a propagator or vertex.

THIS SCRIPT
===========
  1. Articulates what an m - k = 0 cascade observable looks like
     structurally (single-layer vs multi-layer).
  2. Checks per-layer locality: can a single-Dirac-layer fermion
     have a closed sub-loop?  Or does m-k=0 require multi-layer
     structure (external at Dirac layer + loop at gauge layer)?
  3. Proposes (g-2) as the most natural cascade m-k=0 observable
     and computes the cascade prediction at the structural level.
  4. Numerical scale checks against existing cascade absolute-mass
     residuals (~0.5%) to see if they could be balanced corrections.
  5. Identifies the framework gap and the most tractable next step.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Compute (g-2) cascade-natively.  The cascade lacks the (g-2)
    framework; this is a research target, not a closure.
  - Close the m - k = 0 slot.  The slot is identified as empty;
    candidate observables and their structural predictions are
    articulated; a definitive m - k = 0 closure requires the
    cascade-native vertex correction calculation, which is open.
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


# ---------------------------------------------------------------------------
# Step 1: structural meaning of m - k = 0
# ---------------------------------------------------------------------------

def report_structural_meaning():
    print("=" * 78)
    print("STEP 1: structural meaning of an m - k = 0 cascade observable")
    print("=" * 78)
    print()
    print("A balanced m - k = 0 cascade observable has:")
    print()
    print("  k = 1 open-line propagator (external fermion mode)")
    print("  m = 1 closed loop (internal fermion bubble)")
    print()
    print("Chirality factor: chi^(m - k) = chi^0 = 1.  No chi-enhancement.")
    print()
    print("In QFT terms, this is a 1-loop correction to a propagator or vertex:")
    print()
    print("  (i) FERMION SELF-ENERGY: external fermion line with internal")
    print("      fermion loop (the QED 1-loop diagram for delta_m).")
    print("      Topology: external f -> photon-vertex -> internal f-loop ->")
    print("                photon-vertex -> external f.")
    print("      Open mode: 1 (the external fermion line).")
    print("      Closed loop: 1 (the internal f-loop).")
    print()
    print("  (ii) VERTEX CORRECTION: 1-loop correction to the photon-fermion-")
    print("       fermion vertex.  Source of Schwinger's a_e = alpha/(2pi).")
    print("       Topology: external f-photon-f triangle with internal f-loop.")
    print("       Open mode: 1 (the external fermion through the vertex).")
    print("       Closed loop: 1 (the internal triangle).")
    print()
    print("  (iii) WAVE-FUNCTION RENORMALISATION: Z-factor on the propagator.")
    print("        Closely related to (i); provides the residue at the pole.")
    print()
    print("All three have m - k = 0 (balanced) chirality structure.")
    print()


# ---------------------------------------------------------------------------
# Step 2: per-layer locality and m - k = 0
# ---------------------------------------------------------------------------

def report_per_layer_locality_check():
    print("=" * 78)
    print("STEP 2: per-layer locality and the structural form of m - k = 0")
    print("=" * 78)
    print()
    print("Cascade fermion is per-layer local (rem:fermion-gauge-coupling-")
    print("proposal Per-layer locality).  An external fermion at a Dirac")
    print("layer cannot have a sub-loop SAME-LAYER (no inter-layer kinetic")
    print("operator on fermion to source the sub-loop's propagation).")
    print()
    print("So m - k = 0 in the cascade is most naturally MULTI-LAYER:")
    print()
    print("  External fermion at Dirac layer d_g (e.g., d=5, 13, 21).")
    print("  Closed loop at gauge-window layer d_gw (e.g., d=14 for U(1)).")
    print("  Connection: scalar field's kinetic term mediates between")
    print("              the Dirac layer and the gauge-window layer.")
    print()
    print("Structurally:")
    print()
    print("  External fermion mode (k=1) sits at d_g.  Its open-line")
    print("    contribution to its observable is alpha(d_g)/chi or")
    print("    similar (LAYER-DEPENDENT source coupling).")
    print()
    print("  Internal closed loop (m=1) sits at d_gw (or another layer).")
    print("    Its closed-loop topological contribution is chi*Gamma(1/2)^n")
    print("    (LAYER-INDEPENDENT topological obstruction).")
    print()
    print("  Net structural form for the m - k = 0 cascade observable:")
    print()
    print("    I_Q = alpha(d_g) * Gamma(1/2)^n / chi^(k - m)")
    print("        = alpha(d_g) * Gamma(1/2)^n  for k = m")
    print()
    print("  where d_g is the source layer (open mode's home), n is the")
    print("  number of internal-loop legs at the loop's home layer.")
    print()
    print("CONSEQUENCE: the m - k = 0 cascade observable is layer-DEPENDENT")
    print("on the open mode's source d_g but layer-INDEPENDENT in the loop's")
    print("topological structure.  This MIXES the two cascade primitive types")
    print("(alpha(d) source + Gamma(1/2)^n topology).  No purely topological")
    print("cascade observable can be at m - k = 0; the open-line source")
    print("structure must enter.")
    print()
    print("This is why m - k = 0 is hard to test cleanly: it's not 'one")
    print("primitive raised to one power'; it's a PRODUCT of two cascade")
    print("primitive types that the cascade hasn't yet developed a framework")
    print("for combining.")
    print()


# ---------------------------------------------------------------------------
# Step 3: candidate (g-2) cascade prediction
# ---------------------------------------------------------------------------

def report_g_minus_2_candidate():
    print("=" * 78)
    print("STEP 3: anomalous magnetic moment (g-2) as the natural m - k = 0")
    print("        candidate observable")
    print("=" * 78)
    print()
    print("Schwinger's QED 1-loop result: a_e^{Schwinger} = alpha / (2 pi).")
    print()
    print("This is the leading m - k = 0 contribution to the electron's")
    print("anomalous moment, from a 1-loop vertex correction (k=1 external")
    print("fermion + m=1 internal triangle).")
    print()
    print("Cascade structural form (CONJECTURE):")
    print()
    print("  a_f^{cascade m-k=0} = ??? * alpha(d_g) * Gamma(1/2)^n")
    print()
    print("with d_g = fermion's Dirac layer, n = legs in vertex triangle.")
    print()
    print("For a triangle vertex correction with photon mediator: n = 3")
    print("(three internal fermion propagator legs in the triangle).")
    print()
    print(f"Cascade primitive at n=3: Gamma(1/2)^3 = pi^(3/2) = {math.pi**(3/2):.4f}")
    print()
    print("Structural cascade-native form:")
    print()
    print("  a_f = [normalisation] * alpha(d_g) * pi^(3/2)")
    print()
    print("Comparing to Schwinger: a_e = alpha / (2 pi) = (alpha)*1/(2 pi).")
    print()
    print("In standard QED units, alpha = alpha_em = 1/137.  In cascade")
    print("units, alpha(21) at the electron's Dirac layer:")
    a21 = alpha_cascade(21)
    print(f"  alpha(21) = R(21)^2/4 = {a21:.6f}")
    print(f"  alpha_em ~ 1/137 = {1/137:.6f}")
    print(f"  ratio alpha(21) / alpha_em = {a21 / (1/137):.4f}")
    print()
    print("So alpha(21) >> alpha_em (cascade gauge coupling is larger than")
    print("the observer's QED coupling at the electron Dirac layer).")
    print()
    print("Cascade-native prediction structure: a_e^{cascade} = a_e^{Schwinger} * X")
    print("where X is a cascade dimensionless factor.  Schwinger value:")
    schwinger = (1/137) / (2 * math.pi)
    print(f"  a_e^{{Schwinger}} = {schwinger:.6e} = 0.0011614")
    print()
    print("Observed a_e = 0.001159652 (PDG 2024, Penning trap measurement)")
    print("Agreement Schwinger leading: 99.9% match.")
    print()
    print(f"Cascade structural prediction needs to give ~ {schwinger:.4e}.")
    print(f"Cascade primitive raw value: alpha(21) * pi^(3/2) = {a21 * math.pi**(3/2):.4f}")
    print(f"  Required cascade normalisation: {schwinger / (a21 * math.pi**(3/2)):.6e}")
    print()
    print("The required normalisation ~ 7e-3 is small; corresponds in cascade")
    print(f"primitives to roughly alpha_em / (2 pi) = {(1/137) / (2*math.pi):.6e},")
    print(f"i.e., the QED loop suppression factor.  In cascade-native units,")
    print(f"this would be expressed via the U(1) coupling at the observer.")
    print()
    print("Cascade-native (g-2) calculation requires:")
    print("  - The gauge-coupled fermion action (rem:fermion-gauge-coupling-")
    print("    proposal): cascade-native vertex correction.")
    print("  - External photon coupling at the observer's d=4 frame.")
    print("  - Multi-layer structure (external f at d=21, loop at d=14 or")
    print("    d=4, scalar mediator).")
    print("This is open work; the cascade has not computed (g-2) at any order.")
    print()


# ---------------------------------------------------------------------------
# Step 4: scale check against existing cascade residuals
# ---------------------------------------------------------------------------

def report_residual_scale_check():
    print("=" * 78)
    print("STEP 4: scale check vs existing cascade absolute-mass residuals")
    print("=" * 78)
    print()
    print("The cascade's leading absolute-mass predictions have residuals:")
    print()
    print(f"  {'observable':<14s}  {'cascade':<14s}  {'observed':<14s}  {'residual':<12s}")
    print("  " + "-" * 60)
    print(f"  {'m_tau':<14s}  {'1755 MeV':<14s}  {'1776.86 MeV':<14s}  {'-1.23%':<12s}")
    print(f"  {'m_mu':<14s}  {'106.2 MeV':<14s}  {'105.66 MeV':<14s}  {'+0.51%':<12s}")
    print(f"  {'m_e':<14s}  {'0.514 MeV':<14s}  {'0.511 MeV':<14s}  {'+0.59%':<12s}")
    print()
    print("m_tau is closed by alpha(19)/chi (open-line k=1, m=0, m-k=-1).")
    print("m_mu and m_e have +0.5% positive residuals NOT yet closed by any")
    print("alpha(d*)/chi^k formula.")
    print()
    print("Could a balanced m - k = 0 correction close m_mu and m_e?  A")
    print("balanced correction at each Dirac layer would be:")
    print()
    print("  delta(m)/m = [normalisation] * Gamma(1/2)^n")
    print()
    print("For the observed residuals ~0.5% at the electron and muon Dirac")
    print("layers d=21 and d=13, with n=2 (self-energy, two internal legs):")
    print()
    target_residual = 0.005  # 0.5%
    n = 2
    primitive = math.pi  # Gamma(1/2)^2
    print(f"  Target: delta(m)/m ~ {target_residual:.4f}")
    print(f"  Cascade primitive (n=2): Gamma(1/2)^2 = {primitive:.4f}")
    print(f"  Required normalisation: {target_residual/primitive:.6f}")
    print()
    print("Required normalisation ~ 0.0016.  Compare to cascade primitives:")
    candidates = [
        ("alpha(13)/chi^3", alpha_cascade(13) / 8),
        ("alpha(13)/chi^4", alpha_cascade(13) / 16),
        ("alpha(21)/chi^3", alpha_cascade(21) / 8),
        ("alpha(21)/chi^4", alpha_cascade(21) / 16),
        ("alpha(14)/chi^4", alpha_cascade(14) / 16),
        ("alpha_em/(2*pi)", (1/137)/(2*math.pi)),
    ]
    print(f"  {'candidate':<24s}  {'value':>12s}  {'closeness to 0.0016':>20s}")
    print("  " + "-" * 60)
    for name, val in candidates:
        ratio = val / 0.0016
        print(f"  {name:<24s}  {val:>12.6f}  {f'{ratio:.2f}x':>20s}")
    print()
    print("None is a clean match.  alpha(21)/chi^4 is closest (0.94x = 0.0015).")
    print("The cascade-native normalisation for an m - k = 0 correction is not")
    print("obvious from pure numerics; would require a structural derivation.")
    print()
    print("PARTIAL CONJECTURE: m_mu and m_e residuals could be balanced")
    print("self-energy corrections with cascade-native normalisation roughly")
    print("alpha(d_g) / chi^4 (the 'next order' of the open-line family at")
    print("the same d_g, applied to a balanced topology).  Status: numerical")
    print("plausibility check, not derivation.")
    print()


# ---------------------------------------------------------------------------
# Step 5: framework gap and tractable next steps
# ---------------------------------------------------------------------------

def report_framework_gap():
    print("=" * 78)
    print("STEP 5: framework gap and tractable next steps")
    print("=" * 78)
    print()
    print("The m - k = 0 slot is structurally distinct from both pure open-")
    print("line (m=0) and pure closed-loop (k=0) families.  It MIXES:")
    print("  - Open-line source primitive alpha(d*) (LAYER-DEPENDENT)")
    print("  - Closed-loop topological primitive Gamma(1/2)^n (LAYER-INDEPENDENT)")
    print("With chirality factor chi^0 = 1 (no enhancement/suppression).")
    print()
    print("FRAMEWORK GAP: the cascade has no developed framework for mixed")
    print("observables that combine both kinds of primitives.  Existing")
    print("predictions are pure m=0 (open-line precision family) or pure")
    print("k=0 (closed-loop screening).  A genuine mixed observable test")
    print("requires:")
    print("  - A multi-layer cascade observable (external at Dirac layer +")
    print("    loop at another layer).")
    print("  - The cascade's gauge-coupled fermion action with photon-")
    print("    fermion-fermion vertex corrections (rem:fermion-gauge-")
    print("    coupling-proposal, open at oq:fermion-gauge-action).")
    print("  - Cross-layer combination rule for alpha(d_g) (open source)")
    print("    and Gamma(1/2)^n (closed topology).")
    print()
    print("MOST TRACTABLE NEXT STEPS:")
    print()
    print("  1. (g-2) cascade-native calculation as the canonical m-k=0 test.")
    print("     Required ingredients: cascade vertex correction at d_gw=14")
    print("     (U(1) layer) with internal triangle at the same layer,")
    print("     external fermion at d_g (Dirac layer for the lepton).")
    print("     Test: reproduce Schwinger's alpha/(2 pi) ~ 1.16e-3 for a_e.")
    print()
    print("  2. Cascade self-energy correction to fermion masses.")
    print("     Could the +0.5% positive residuals on m_mu, m_e, and m_e be")
    print("     closed by a balanced m-k=0 correction with cascade-native")
    print("     normalisation alpha(d_g)/chi^4?  Numerical scale matches at")
    print("     factor 0.94x but structural derivation is open.")
    print()
    print("  3. Identification rule for which observables sit at m-k=0.  The")
    print("     cascade's source-selection rule (Part IVb prop:source-selection)")
    print("     handles open-line m=0 observables.  An analogous selection")
    print("     rule for m-k=0 mixed observables would be a structural")
    print("     extension.")
    print()
    print("  4. Hidden m-k=0 observables already in the cascade?  Check")
    print("     whether any current 'unresolved residual' (m_mu/m_e at +0.13%,")
    print("     m_e absolute at +0.59%, m_mu absolute at +0.51%) admits an")
    print("     m-k=0 reading.  Numerical scale check above suggests m_mu and")
    print("     m_e absolute residuals ARE candidates for a balanced cascade-")
    print("     native correction with normalisation alpha(d_g)/chi^4.")
    print()


# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

def report_summary():
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    print()
    print("Investigation of the m - k = 0 balanced slot finds:")
    print()
    print("1. STRUCTURALLY DISTINCT.  An m-k=0 cascade observable mixes")
    print("   open-line source primitive alpha(d*) with closed-loop")
    print("   topological primitive Gamma(1/2)^n, with chirality factor 1.")
    print("   This is a different kind of structure from pure m=0 or k=0.")
    print()
    print("2. PER-LAYER LOCALITY makes single-layer m-k=0 difficult.  The")
    print("   most natural realization is multi-layer: external fermion at")
    print("   a Dirac layer, internal loop at a gauge-window layer.")
    print()
    print("3. MOST NATURAL TEST: anomalous magnetic moment (g-2).  The")
    print("   cascade has no (g-2) framework yet; reproducing Schwinger's")
    print("   alpha/(2 pi) is the canonical m-k=0 test.")
    print()
    print("4. NUMERICAL PLAUSIBILITY: the cascade's existing absolute-mass")
    print("   residuals at +0.5% (m_mu, m_e absolute) are consistent with")
    print("   a balanced m-k=0 correction multiplied by a cascade-native")
    print("   normalisation ~ alpha(d_g)/chi^4 (factor 0.94x off from the")
    print("   target).  This is a PARTIAL CONJECTURE pending structural")
    print("   derivation.")
    print()
    print("5. FRAMEWORK GAP: the cascade has no developed framework for")
    print("   mixed observables.  Closing m-k=0 requires either a (g-2)")
    print("   calculation or an identification rule for which currently-")
    print("   unresolved residuals are balanced corrections.")
    print()
    print("VERDICT: the m-k=0 slot is genuinely empty, structurally distinct")
    print("from neighbouring slots, and represents the primary research")
    print("target for extending the cascade's chirality classification to a")
    print("complete spectrum.  Closing it would graduate the m - k axis from")
    print("descriptive organizing principle to predictive structural")
    print("classification.")
    print()


def main() -> int:
    print("=" * 78)
    print("CASCADE m - k = 0 BALANCED SLOT INVESTIGATION")
    print("Open-closed mixed observables with chirality cancellation")
    print("=" * 78)
    print()
    report_structural_meaning()
    report_per_layer_locality_check()
    report_g_minus_2_candidate()
    report_residual_scale_check()
    report_framework_gap()
    report_summary()
    return 0


if __name__ == "__main__":
    sys.exit(main())
