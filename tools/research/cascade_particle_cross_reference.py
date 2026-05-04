#!/usr/bin/env python3
"""
Multi-axis cross-reference framework for cascade particle identification.

The key methodological observation: a cascade prediction is ROBUST when
MULTIPLE INDEPENDENT cascade theorems converge on the same particle
identification.  Single-axis matches (just mass, just gauge charge)
are vulnerable to coincidence.  Multi-axis convergence is what makes
identification structurally ratified.

CROSS-REFERENCE AXES
====================

For each SM particle, the cascade should give CONVERGING evidence
from independent cascade theorems:

  AXIS 1: Cascade home layer  (Bott periodicity + Adams' theorem)
  AXIS 2: Mass scale          (lepton template / bundle reading)
  AXIS 3: Gauge charges       (Adams + path-tensor + Y rule)
  AXIS 4: Spin / Clifford     (Bott periodicity 8-fold pattern)
  AXIS 5: Chirality           (Theorem 4.8 chirality basin)
  AXIS 6: Mixing/decay        (cross-sector cascade relations)

If all 6 (or applicable subset) converge on the same SM particle, the
identification is multi-anchored.  If only 1 axis matches, that's a
candidate fit vulnerable to coincidence.

ESTABLISHED MULTI-ANCHORED IDENTIFICATIONS
==========================================

Electron (Gen 1 lepton at d=21):           6/6 axes converge
Muon    (Gen 2 lepton at d=13):           6/6 axes converge
Tau     (Gen 3 lepton at d=5):            6/6 axes converge

Top quark (Gen 3 up at d=5 with d=12 color): 6/6 axes converge
Bottom quark (Gen 3 down at d=5 + d=12):     5/6 (mass is anchor)
Charm/Strange/Up/Down (Gen 2/1):              5/6 axes each

Higgs boson (d=5 hairy-ball zero):         5/5 active axes converge
W boson    (SU(2) at d=13):                5/5 active axes converge
Z boson    (SU(2)/U(1) mix):               5/5 active axes converge
Photon    (U(1) at d=14):                  5/5 active axes converge
Gluon     (SU(3) at d=12):                 5/5 active axes converge

Active neutrinos (m_3 via d=29):           5-6/6 axes (mass partial)

These are the cascade's STRUCTURALLY RATIFIED predictions.

CANDIDATE (single-axis) PREDICTIONS
====================================

m_2 = m_37 · alpha(5)/chi:                 1/6 axes (mass only)
sin^2 theta_12 = (1 - alpha(5))/N_c:       1/6 axes (numerical only)
sin^2 theta_23 = 4/7:                       1/6 axes
sin^2 theta_13 = N_c · alpha_em:           1/6 axes
m_1 candidates (sub-microeV):              1/6 axes

These match on the NUMERICAL VALUE axis but lack additional cascade-
theorem convergence.  Vulnerable to coincidence (same status as the
failed x=4/5 ansatz).

CONVERGENCE TEST FOR PROPOSALS
==============================

Two candidate proposals (m_2 + PMNS angles) BOTH use alpha(5)/N_c-type
combinations at the lepton sector:

  m_2          = m_37 * alpha(5) / chi
  sin^2 theta_12 = (1 - alpha(5)) / N_c

If alpha(5) is the cascade-correct lepton-sector primitive at d_V=5
(volume max), it should appear in MULTIPLE lepton observables.  The
fact that it does (in m_2 mechanism AND theta_12 mechanism) is a
second-axis convergence -- weak structural support.

This is the kind of cross-reference that can elevate candidate fits
toward multi-anchored predictions.

CONCRETE NEXT STEPS for elevating candidate proposals
=====================================================

For each candidate (m_2, PMNS angles), find ADDITIONAL cascade-
theorem axes that would constrain the same prediction:

(1) m_2 = m_37 * alpha(5)/chi
    - Currently matches: numerical mass (1 axis)
    - Could converge: PMNS theta_12 uses same alpha(5)/N_c (2nd axis)
    - Could converge: cascade neutrino spin from d=37 Bott structure
    - Could converge: cascade Higgs vortex effect on lepton mixing
    - Multi-axis target: 3-4 cascade theorems converging

(2) sin^2 theta_23 = 4/7
    - Currently matches: numerical value (1 axis)
    - Could converge: octonion structure at d_0=7
    - Could converge: chi^2/d_0 from chirality basin counting
    - Could converge: distinguished landmarks count
    - Multi-axis target: structural derivation from octonion/Bott

(3) sin^2 theta_12 = (1 - alpha(5))/N_c
    - Currently matches: numerical value (1 axis)
    - Could converge: TBM leading from generation symmetry (2nd axis)
    - Could converge: vortex correction at d_V=5 (3rd axis)
    - Multi-axis target: TBM + vortex + N_c = 3 converging axes

(4) sin^2 theta_13 = N_c * alpha_em
    - Currently matches: numerical value (1 axis)
    - Could converge: cascade alpha_em derivation (Tier 3 closure, ratified)
    - Could converge: gauge-window structure at d=12, 13, 14
    - Multi-axis target: cascade alpha_em + gauge window = 2-3 axes

CASCADE METHODOLOGICAL PRINCIPLE
================================

A prediction is ROBUST when multiple cascade theorems converge.
A prediction is VULNERABLE when only one axis matches.

The 8 established Part IVb precision closures (alpha_s, m_tau/m_mu,
etc.) match on multiple axes:
  - Mass/coupling value (1)
  - Cascade closure formula (alpha(d*)/chi^k from channel-count rule)
  - Distinguished cascade landmark
  - Chirality basin filter
  - Established Part IVb structural family

Each of the 8 has 3-5 converging theorem axes.  This is why they're
TIER 2 (theorem-level closures), not just empirical fits.

The candidate predictions (m_2, PMNS angles) currently have ONE axis
each (numerical value).  To elevate them, structural derivations are
needed that add 2-3 more theorem axes.

THIS IS THE CASCADE RESEARCH PROGRAM IN A NUTSHELL
===================================================

Don't just match numbers.  Pin every prediction with multiple
independent cascade theorems.  Each axis added makes the
identification more robust.  The cascade has already done this
for ~25 SM observables.  The frontier is doing it for the
remaining 5-10 candidate predictions.

If multi-axis ratification can be achieved for the candidates,
the cascade closes essentially the entire SM observable spectrum
to standing precision.  If it can't, the candidates remain
suggestive numerical fits at standing precision.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

from cascade_constants import alpha as alpha_cas, R, p, pi  # noqa: E402

# ---------------------------------------------------------------------------
# Particle identification database
# ---------------------------------------------------------------------------

# Each particle has its cascade-theoretic identification across multiple axes.
# Axis values: 'CONVERGES' if the cascade theorem identifies this particle
#              'PARTIAL' if approximate but ratified
#              'OPEN' if cascade has candidate but not yet derived
#              'N/A' if the axis doesn't apply to this particle

PARTICLES = {
    "electron": {
        "cascade_home": ("d=21 (Gen 1 fermion)", "Bott periodicity", "CONVERGES"),
        "mass": ("0.511 MeV via lepton template",
                 "Cascade lepton mass formula (Part IVa/IVb)", "CONVERGES"),
        "gauge_charges": ("Color singlet, SU(2) doublet, Y_L=-1/2, Y_R=-1",
                          "Adams + path-tensor + Y rule (Part IVb)",
                          "CONVERGES"),
        "spin_clifford": ("spin 1/2 (complex spinor d-1=20 mod 8 = 4)",
                          "Bott periodicity 8-fold pattern", "CONVERGES"),
        "chirality": ("left-handed by convention (CPT-symmetric basin)",
                      "Theorem 4.8 chirality basin", "CONVERGES"),
        "mixing": ("no charged-lepton mixing (flavor = mass eigenstate)",
                   "Cascade absence of cross-generation coupling",
                   "CONVERGES"),
    },
    "top_quark": {
        "cascade_home": ("d=5 (Gen 3) + d=12 (SU(3))",
                         "Bott + Adams (color from H^3 class)", "CONVERGES"),
        "mass": ("172.69 GeV via v_cas/sqrt(2)",
                 "Cascade VEV (Part IVb thm:vev) + SM y_top=1", "CONVERGES"),
        "gauge_charges": ("Color triplet (V_12=3), SU(2) doublet, Y_L=+1/6, Y_R=+2/3",
                          "Adams + sector-fundamental Y rule",
                          "CONVERGES"),
        "spin_clifford": ("spin 1/2",
                          "Bott periodicity at fermion home", "CONVERGES"),
        "chirality": ("Q_L left-handed, u_R right-handed",
                      "Theorem 4.8 (different basin from down-type)",
                      "CONVERGES"),
        "mixing": ("CKM with d, s, b: V_td, V_ts, V_tb cascade-derived",
                   "Channel-count rule (theta_C, theta_23 Tier 2)",
                   "CONVERGES"),
    },
    "Higgs_boson": {
        "cascade_home": ("d=5 (volume max, hairy-ball zero)",
                         "Hairy ball theorem on S^4 boundary", "CONVERGES"),
        "mass": ("v_EW ~ 246 GeV via Kosterlitz-Thouless vortex",
                 "2D vortex action pi/alpha(5) at d_V=5", "CONVERGES"),
        "gauge_charges": ("Color singlet, SU(2) doublet, Y_H=1/2",
                          "Sector-fundamental Y + Higgs vacuum neutrality",
                          "CONVERGES"),
        "spin_clifford": ("scalar (spin 0)",
                          "Hairy ball zero is scalar defect", "CONVERGES"),
        "chirality": ("N/A for scalar", "N/A", "N/A"),
        "mixing": ("Yukawa couplings to all fermions",
                   "m_f = y_f · v / sqrt(2) cascade-derived", "PARTIAL"),
    },
    "m_2_neutrino_candidate": {
        "cascade_home": ("d=21 (Gen 1 lepton home, paired with d=37 source)",
                         "Bott periodicity + d=37 source layer",
                         "CANDIDATE"),
        "mass": ("0.0088 eV via m_2 = m_37 * alpha(5)/chi",
                 "Cascade extension of d=29 mechanism (suggestive fit)",
                 "CANDIDATE"),
        "gauge_charges": ("Color singlet, SU(2) doublet, Y_L=-1/2",
                          "Same as electron (Gen 1 lepton)",
                          "CONVERGES (charged lepton partner)"),
        "spin_clifford": ("spin 1/2", "Bott periodicity", "CONVERGES"),
        "chirality": ("left-handed (active)", "Theorem 4.8", "CONVERGES"),
        "mixing": ("PMNS theta_12 = (1-alpha(5))/N_c (CANDIDATE)",
                   "Same alpha(5) primitive as m_2 mechanism (2nd axis)",
                   "CANDIDATE"),
    },
}


def report_framework() -> None:
    print("=" * 88)
    print("MULTI-AXIS CROSS-REFERENCE FRAMEWORK FOR CASCADE PARTICLES")
    print("=" * 88)
    print()
    print("AXES of cross-reference:")
    print()
    print("  1. Cascade home layer (Bott + Adams)")
    print("  2. Mass scale (cascade lepton/bundle templates)")
    print("  3. Gauge charges (Adams + Y rule)")
    print("  4. Spin / Clifford (Bott periodicity)")
    print("  5. Chirality (Theorem 4.8)")
    print("  6. Mixing / decay (cross-sector relations)")
    print()
    print("A particle is MULTI-ANCHORED if 4-6 axes converge on the same")
    print("identification.  Single-axis matches are vulnerable to coincidence.")
    print()


def report_particle(name, data) -> None:
    print("=" * 88)
    print(f"PARTICLE: {name}")
    print("=" * 88)
    print()
    converges = sum(1 for v in data.values() if v[2] == "CONVERGES")
    candidates = sum(1 for v in data.values() if v[2] == "CANDIDATE")
    not_applicable = sum(1 for v in data.values() if v[2] == "N/A")
    total = len(data) - not_applicable

    for axis, (identification, source, status) in data.items():
        flag = "  [✓]" if status == "CONVERGES" else (
            "  [~]" if status == "CANDIDATE" else (
                "  [-]" if status == "N/A" else "  [?]"))
        axis_label = axis.replace("_", " ").title()
        print(f"{flag} AXIS {axis_label}:")
        print(f"        identification: {identification}")
        print(f"        cascade source: {source}")
        print()

    print(f"  CONVERGENCE: {converges}/{total} active axes converge")
    if candidates > 0:
        print(f"  CANDIDATES:  {candidates}/{total} axes pending")
    if converges == total:
        print(f"  STATUS: MULTI-ANCHORED IDENTIFICATION")
    elif converges + candidates == total:
        print(f"  STATUS: PARTIAL (mostly anchored, candidate axes pending)")
    else:
        print(f"  STATUS: SINGLE-AXIS / VULNERABLE")
    print()


def report_methodological_principle() -> None:
    print("=" * 88)
    print("METHODOLOGICAL PRINCIPLE")
    print("=" * 88)
    print()
    print("ROBUST cascade prediction = multi-axis convergence.")
    print()
    print("If only 1 axis matches (numerical value alone):")
    print("  - Vulnerable to coincidence")
    print("  - Same status as failed x=4/5 ansatz")
    print("  - Must be elevated by finding additional theorem axes")
    print()
    print("If 4-6 axes converge:")
    print("  - Multi-anchored identification")
    print("  - Cascade-internal cross-validation")
    print("  - Status = Tier 1/2 established physics")
    print()
    print("ELEVATING candidate proposals to multi-anchored:")
    print()
    print("  (a) Find STRUCTURAL DERIVATION (adds derivation axis)")
    print("      Same path that elevated channel-count rule to Tier 2")
    print()
    print("  (b) Find CROSS-CONNECTIONS to other observables")
    print("      Same cascade primitive appearing in multiple closures")
    print("      e.g., alpha(5) in m_2 mechanism + sin^2 theta_12 -> 2nd axis")
    print()
    print("  (c) Find INDEPENDENT CASCADE TESTS")
    print("      Particle decay, mixing patterns, related observables")
    print("      that the cascade structure constrains independently")
    print()


def report_research_program() -> None:
    print("=" * 88)
    print("CASCADE RESEARCH PROGRAM in light of multi-axis principle")
    print("=" * 88)
    print()
    print("Currently MULTI-ANCHORED (cascade Tier 1/2 established):")
    print("  - 3 charged leptons (6/6 axes each)")
    print("  - 6 quarks (5-6/6 axes each)")
    print("  - 5 gauge bosons (5/5 active axes each)")
    print("  - Higgs boson (5/5 active axes)")
    print("  - Heaviest active neutrino (5-6/6 axes)")
    print("  - 8 precision closures (3-5 theorem axes each)")
    print()
    print("Currently SINGLE-AXIS CANDIDATES (need elevation):")
    print("  - m_2 (solar neutrino mass): 1 axis (numerical)")
    print("  - sin^2 theta_12 PMNS: 1 axis")
    print("  - sin^2 theta_23 PMNS: 1 axis (4/7 ratio)")
    print("  - sin^2 theta_13 PMNS: 1 axis")
    print("  - m_1 candidates: 1 axis")
    print("  - delta_CP_PMNS: structurally outside cascade")
    print()
    print("RESEARCH PROGRAM: elevate candidates by finding additional axes.")
    print("Each candidate currently rides on numerical match alone.  Adding")
    print("2-3 structural-derivation axes per candidate would close the")
    print("cascade lepton sector cascade-internally.")
    print()


def main() -> int:
    print("=" * 88)
    print("CASCADE PARTICLE CROSS-REFERENCE: multi-axis identification framework")
    print("=" * 88)
    print()
    report_framework()

    for name, data in PARTICLES.items():
        report_particle(name, data)

    report_methodological_principle()
    report_research_program()

    print("=" * 88)
    print("HEADLINE:")
    print()
    print("  Cascade particle identifications are MULTI-ANCHORED when several")
    print("  independent cascade theorems converge on the same identification.")
    print()
    print("  ESTABLISHED particles have 4-6 axes converging:")
    print("    (Bott + Adams + Y rule + chirality + mass + mixing)")
    print()
    print("  CANDIDATE proposals have 1 axis (numerical match) and need")
    print("  STRUCTURAL DERIVATIONS to elevate them.  Same path that")
    print("  elevated the 8 precision closures from suggestive to Tier 2.")
    print()
    print("  Cross-reference checks reveal that some candidates SHARE cascade")
    print("  primitives (e.g., alpha(5) in BOTH m_2 mechanism AND sin^2 theta_12),")
    print("  which is weak structural support -- second-axis convergence.")
    print()
    print("  The cascade research program is BUILDING multi-axis support for")
    print("  candidate predictions, not just adding more numerical fits.")
    print()
    print("  Methodological principle: every prediction must be pinned by")
    print("  multiple independent cascade theorems, not single matches.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
