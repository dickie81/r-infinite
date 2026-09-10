#!/usr/bin/env python3
"""
NEW PROPOSAL: m_2 (solar splitting neutrino) sourced from d=37 via alpha(5)/chi

CONTEXT
=======
The cascade's existing d=29 mechanism for active neutrino masses gives:
  m_nu(Gen g) = m_29 * alpha(d_g) / chi^(29-d_g)  for d_g in {5, 13, 21}

This gets m_3 (atmospheric splitting) RIGHT (~0.05 eV, -1.4% match) but
the lighter two neutrinos m_2 = 0.0087 eV and m_1 ~ 0 in normal
hierarchy come out 100-1000x too small.  This is the CLAUDE.md
acknowledged "cascade analogue of PMNS" open question.

cascade_higher_bott_tower.py identified the d=37 source mass at 0.193 eV.
Numerical exploration shows the empirical ratio:

  m_2 / m_37 = 0.0087 / 0.193 = 0.0450

matches the cascade primitive alpha(5)/chi to STANDING PRECISION:

  alpha(5)/chi = 0.0905/2 = 0.0453   (off +0.66% from m_2/m_37)

NEW PROPOSAL
============
m_2 = m_37 * alpha(5)/chi

Numerical prediction:
  m_2 cascade = 0.193 eV * 0.0905/2 = 0.00876 eV
  m_2 PDG     = 0.0087 eV
  match       = +0.66%   (STANDING PRECISION)

Combined with the established d=29 mechanism, the cascade now has a
candidate UNIFIED proposal for the active neutrino mass spectrum:

  m_3 = m_29 * alpha(21)/chi^8 = 0.0499 eV   (PDG 0.0506, dev -1.42%)
  m_2 = m_37 * alpha(5)/chi    = 0.00876 eV  (PDG 0.0087, dev +0.66%)
  m_1 = ? (cascade extrapolation gives few-micro-eV; consistent with
          normal hierarchy m_1 ≈ 0)

Both mass formulas use the same Part IVb alpha(d*)/chi^k correction
family.  The active neutrino mass sum:

  Sigma m_nu = m_3 + m_2 + m_1 ≈ 0.0586 eV

is well within DESI 2024 cosmological bound (0.072 eV).

WHY alpha(5)/chi IS CASCADE-NATURAL
====================================
alpha(5)/chi is a known cascade primitive that already appears in
Part IVb precision closures:
  - Part IVb section on chirality factorization (Theorem 4.8) uses
    alpha(5)/chi for the Higgs vacuum-neutrality argument
  - The cascade m_W formula has structural connections to alpha(5)/chi
  - Multiple precision closures use alpha(d*)/chi^k with k=1,2,3,4

So m_2 = m_37 * alpha(5)/chi sits in the SAME structural family as
the eight precision closures that match observation within precision (ell_A at -1.8 sigma).

Structurally meaningful: alpha(5) is the cascade volume-maximum
coupling (d=5 = d_V), and chi=2 is the Euler characteristic.
alpha(5)/chi means "volume-max coupling filtered through one
chirality basin" -- a natural cascade-internal projection from the
d=37 source onto observer-scale neutrino mass.

CAVEATS (honest framing)
========================
1. ONE DATA POINT.  m_2/m_37 fits alpha(5)/chi to 0.66%.  That's
   one observable matched to one cascade primitive -- same risk
   as the failed x=4/5 ansatz for m_b.

2. NOT YET DERIVED STRUCTURALLY.  Why d=37 sources m_2 (and not
   m_3 or m_1)?  Why alpha(5)/chi (and not a different filter)?
   The current proposal doesn't derive WHICH d_source pairs with
   WHICH active eigenstate via WHICH filter.

3. m_3 vs m_2 USE DIFFERENT TEMPLATES:
   - m_3: m_29 * alpha(21) * chi^(-8)  (large chi power, target = Gen 1 home)
   - m_2: m_37 * alpha(5)  * chi^(-1)  (small chi power, target = volume max)
   This isn't yet a UNIFIED single-formula prediction; it's a
   PATTERN that the cascade might ratify if the structural
   derivation succeeds.

4. m_1 IS UNCONSTRAINED.  Currently the cascade has no analogous
   formula for m_1.  Consistent with normal-hierarchy m_1 ≈ 0
   but not predictive.

5. STILL OPEN: cascade-internal proof that the cascade's PMNS-analog
   reproduces observed mixing angles theta_12, theta_23, theta_13.
   This proposal only addresses MASSES, not mixing structure.

WHAT THIS WOULD CLOSE IF DERIVED
=================================
If m_2 = m_37 * alpha(5)/chi is structurally derived:
  - Closes the cascade's "lighter neutrino mass gap" partially
    (m_2 closed; m_1 still open)
  - Promotes d=37 from "structural prediction at observational
    frontier" to "active sourcing layer for solar splitting"
  - Adds a 9th cascade observable to the precision closures family
    (current list: alpha_s, m_tau/m_mu, m_tau abs, ell_A,
     sin^2 theta_W, Omega_m, theta_C, b/s + theta_23 = 9)

Falsifiable:
  - Future Sigma m_nu measurement < 0.05 eV would constrain m_2
    and force re-examination
  - Discovery of a 4th active or sterile neutrino state at scales
    other than 0.193 eV would challenge the d=37 interpretation
  - Discovery of solar splitting different from current PDG would
    test the cascade m_2 prediction

WHY THIS MIGHT BE THE RIGHT MOVE
================================
Three structural arguments:
  (a) The cascade higher-Bott tower naturally has d=37 at 0.19 eV;
      the question "what does it do?" needed an answer.  Sourcing
      m_2 is the simplest one.
  (b) alpha(5)/chi is in the cascade's known correction family
      (Part IVb), not an ad-hoc factor.
  (c) The combined sum Sigma m_nu ~ 0.06 eV is within current
      cosmological bounds (DESI 0.072 eV) -- not in tension.

Three structural arguments AGAINST:
  (a) m_2 prediction uses different template than m_3 (different
      d_target, different chi power).  The mechanism is not yet
      unified.
  (b) The d=29 mechanism uses chi^(d_source - d_target) which is
      structurally clean; the d=37 -> m_2 mechanism uses chi^1
      regardless of layer distance.  Different rules.
  (c) One data point fitted to one cascade primitive is fragile
      (failed x=4/5 ansatz had similar precision before being
      refuted by universality probe).

CONCRETE NEXT STEPS
===================
To elevate this from "candidate fit" to "derived mechanism":
  1. Structural derivation of why d=37 sources m_2 (and not m_3)
  2. Structural derivation of why alpha(5)/chi is the right filter
  3. Cascade-internal prediction for m_1 and PMNS angles
  4. Test consistency with cascade gauge structure at d=12/13/14
  5. Compute cosmological N_eff prediction from d=37 thermalization

If these can be derived from cascade primitives without
introducing new free parameters, the cascade closes the
neutrino sector at standing precision.

If they cannot be derived and the proposal remains an empirical
fit, m_2 = m_37 * alpha(5)/chi joins the cascade's "suggestive
patterns" rather than its "structural predictions."

CONCLUSION
==========
A genuinely new candidate cascade closure: m_2 = m_37 * alpha(5)/chi
matches PDG at +0.66%.  The d=37 layer (5th Bott) MAY source the
solar-splitting neutrino mass via the cascade's standard
alpha(d*)/chi^k correction family.

This addresses the cascade's "lighter neutrino gap" partially.
Status: SUGGESTIVE FIT requiring structural derivation to be
elevated to predictive theorem.
"""

from __future__ import annotations

import math
import os
import sys

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)
sys.path.insert(0, os.path.join(TOOLS_DIR, "research"))

from cascade_constants import alpha as alpha_cas, R, p, pi  # noqa: E402
from cascade_gram_bott_tower import Phi_cascade  # noqa: E402

ALPHA_S = 0.1159
V_CAS = 243.7
TWO_SQRT_PI = 2 * math.sqrt(pi)
CHI = 2

M_NU_3_PDG = 0.0506
M_NU_2_PDG = 0.0087
SUM_NU_DESI = 0.072


def n_D_plus_1(d: int) -> int:
    return (d - 5) // 8 + 2


def m_source(d: int) -> float:
    return ALPHA_S * V_CAS / math.sqrt(2) * math.exp(-Phi_cascade(d)) * TWO_SQRT_PI ** (-n_D_plus_1(d))


def report_setup() -> None:
    print("=" * 88)
    print("STEP 1: cascade neutrino mass mechanism status")
    print("=" * 88)
    print()
    m_29 = m_source(29) * 1e9
    m_37 = m_source(37) * 1e9
    print(f"  Source masses (cascade Bott tower):")
    print(f"    d=29: {m_29:.2f} eV    (Part IVa Open Question source)")
    print(f"    d=37: {m_37:.4f} eV    (Option epsilon finding)")
    print()
    print(f"  Established d=29 mechanism (m_nu(d_g) = m_29*alpha(d_g)/chi^(29-d_g)):")
    for d_g in [21, 13, 5]:
        m_pred = m_29 * alpha_cas(d_g) / CHI ** (29 - d_g)
        print(f"    d_g={d_g}: m_pred = {m_pred:.4e} eV")
    print()
    print(f"  Maps to PDG (normal hierarchy):")
    print(f"    m_3 (Gen 1 home, atm split) = 0.0506 eV : matches d_g=21 to -1.4%")
    print(f"    m_2 (Gen 2 home, solar)     = 0.0087 eV : NOT MATCHED (28x too small)")
    print(f"    m_1 (Gen 3 home, ~0)         ~ 0      : approx OK (very small)")
    print()
    print(f"  Open: m_2 cascade-internally.  Subject of this script.")
    print()


def report_proposal() -> None:
    print("=" * 88)
    print("STEP 2: NEW PROPOSAL m_2 = m_37 * alpha(5)/chi")
    print("=" * 88)
    print()
    m_37 = m_source(37) * 1e9
    a5 = alpha_cas(5)
    pred = m_37 * a5 / CHI
    print(f"  m_37 (cascade Bott layer 5) = {m_37:.4f} eV")
    print(f"  alpha(5) (volume max coupling) = {a5:.6f}")
    print(f"  chi (Euler characteristic) = {CHI}")
    print()
    print(f"  m_2 = m_37 * alpha(5) / chi")
    print(f"      = {m_37:.4f} * {a5:.4f} / {CHI}")
    print(f"      = {pred:.4f} eV")
    print()
    print(f"  PDG m_2 = {M_NU_2_PDG} eV")
    print(f"  Match: {100*(pred - M_NU_2_PDG)/M_NU_2_PDG:+.3f}%   (STANDING PRECISION)")
    print()


def report_unified_spectrum() -> None:
    print("=" * 88)
    print("STEP 3: cascade neutrino spectrum (proposed multi-source PMNS-analog)")
    print("=" * 88)
    print()
    m_29 = m_source(29) * 1e9
    m_37 = m_source(37) * 1e9
    m_45 = m_source(45) * 1e9

    m_3 = m_29 * alpha_cas(21) / CHI**8
    m_2 = m_37 * alpha_cas(5) / CHI
    m_1_options = {
        "m_45 * alpha(5)/chi (5th Bott layer extension)": m_45 * alpha_cas(5) / CHI,
        "0 (normal hierarchy limit)": 0,
        "m_29 * alpha(5)/chi^8 (d=29 mechanism at d_g=5)": m_29 * alpha_cas(5) / CHI**8,
    }

    print(f"  Active neutrino spectrum (cascade prediction):")
    print()
    print(f"    m_3 = m_29 * alpha(21) / chi^8 = {m_3:.4e} eV  (PDG {M_NU_3_PDG}, dev {100*(m_3-M_NU_3_PDG)/M_NU_3_PDG:+.2f}%)")
    print(f"    m_2 = m_37 * alpha(5)  / chi   = {m_2:.4e} eV  (PDG {M_NU_2_PDG}, dev {100*(m_2-M_NU_2_PDG)/M_NU_2_PDG:+.2f}%)")
    print(f"    m_1: ?   (open; candidates below)")
    print()
    for name, val in m_1_options.items():
        print(f"      {name}: {val:.4e} eV")
    print()

    sigma_options = {
        "with m_1 = m_45 * alpha(5)/chi": m_3 + m_2 + m_45 * alpha_cas(5) / CHI,
        "with m_1 = 0": m_3 + m_2 + 0,
        "with m_1 = d=29 chi^8 contribution": m_3 + m_2 + m_29 * alpha_cas(5) / CHI**8,
    }
    print(f"  Sum Sigma m_nu (different m_1 hypotheses):")
    for name, val in sigma_options.items():
        flag = " (within DESI 0.072)" if val < SUM_NU_DESI else " (TENSION with DESI)"
        print(f"    {name}: {val:.4f} eV{flag}")
    print()


def report_caveats() -> None:
    print("=" * 88)
    print("STEP 4: caveats -- what's not yet derived")
    print("=" * 88)
    print()
    print("  1. ONE DATA POINT.  m_2/m_37 = alpha(5)/chi fits at +0.66%, but this")
    print("     is one observable matched to one cascade primitive.  Same risk as")
    print("     the failed x=4/5 ansatz for m_b.")
    print()
    print("  2. NOT UNIFIED.  m_3 uses chi^8 (Gen 1 home target); m_2 uses chi^1")
    print("     (volume max target).  Different cascade primitives joined by the")
    print("     same alpha(d*)/chi^k correction family.  Pattern, not yet theorem.")
    print()
    print("  3. m_1 OPEN.  Cascade has no derived formula for m_1.  Consistent")
    print("     with normal-hierarchy m_1 ~ 0 but not predictive.")
    print()
    print("  4. PMNS ANGLES UNCONSTRAINED.  This proposal addresses MASSES only;")
    print("     does not predict theta_12, theta_23, theta_13 mixing angles.")
    print()
    print("  5. WHY d=37 SOURCES m_2 SPECIFICALLY (and not m_3 or m_1)?  Why")
    print("     alpha(5) (and not alpha(7) or alpha(13))?  Cascade-internal")
    print("     derivation of these choices is REQUIRED to elevate this from")
    print("     'suggestive fit' to 'derived mechanism'.")
    print()


def report_status() -> None:
    print("=" * 88)
    print("STEP 5: status -- candidate cascade closure")
    print("=" * 88)
    print()
    print("  CANDIDATE FOUND:")
    print()
    print("    m_2 = m_37 * alpha(5) / chi = 0.00876 eV   (PDG 0.0087, +0.66%)")
    print()
    print("  Uses cascade-natural primitives:")
    print("    - m_37: 5th Bott source mass (Option epsilon prediction)")
    print("    - alpha(5)/chi: Part IVb correction family (used in 8 precision closures; ell_A -1.8 sigma; rest sub-sigma")
    print("      precision closures)")
    print()
    print("  STATUS: suggestive cascade closure at standing precision (one data")
    print("  point matched).  Same status as 'partial closures' in Part IVb")
    print("  before they were structurally derived.")
    print()
    print("  IF DERIVED: closes cascade's 'lighter neutrino mass gap' for m_2")
    print("  (ROADMAP item #5 partial closure).  Active neutrino spectrum")
    print("  cascade-internally derived to standing precision for m_3 and m_2.")
    print()
    print("  CONCRETE NEXT STEPS (research level):")
    print("    1. Structural derivation: why d=37 + alpha(5)/chi for m_2?")
    print("    2. Find cascade-internal m_1 mechanism (4th Bott or another)")
    print("    3. Predict cascade PMNS angles (theta_12, theta_23, theta_13)")
    print("    4. Cosmological N_eff and abundance from d=37")
    print("    5. Test against future neutrino mass measurements (DESI, KATRIN,")
    print("       CMB-S4)")
    print()


def main() -> int:
    print("=" * 88)
    print("CASCADE NEUTRINO MASS m_2 FROM d=37 PROPOSAL")
    print("Suggestive new cascade closure: m_2 = m_37 * alpha(5)/chi at +0.66%")
    print("=" * 88)
    print()
    report_setup()
    report_proposal()
    report_unified_spectrum()
    report_caveats()
    report_status()
    print("=" * 88)
    print("HEADLINE FINDING:")
    print()
    print("  Active neutrino mass m_2 (solar splitting) appears to source from")
    print("  the cascade d=37 layer via the standard Part IVb alpha(d*)/chi^k")
    print("  correction family:")
    print()
    print("    m_2 = m_37 * alpha(5) / chi = 0.00876 eV")
    print("    PDG m_2 = 0.0087 eV")
    print("    Match: +0.66% (standing precision)")
    print()
    print("  Combined with the established d=29 -> m_3 mechanism, this gives")
    print("  the cascade a candidate UNIFIED active neutrino mass spectrum:")
    print("    m_3 = m_29 * alpha(21)/chi^8 (PDG -1.4%)")
    print("    m_2 = m_37 * alpha(5)/chi    (PDG +0.66%)")
    print("    m_1 ~ 0 (consistent with normal hierarchy)")
    print()
    print("  Status: SUGGESTIVE FIT requiring structural derivation.  One data")
    print("  point matched at standing precision -- same caution as failed x=4/5")
    print("  ansatz.  But cascade-natural primitives (alpha(5)/chi is in Part IVb")
    print("  closure family) and consistent Sigma m_nu ~ 0.06 eV (within DESI")
    print("  0.072 bound) keep it on the table as a real research direction.")
    print()
    print("  If derived: closes ROADMAP #5 partially (m_2 cascade-internal).")
    print("  If refuted: another negative result that constrains future work.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
