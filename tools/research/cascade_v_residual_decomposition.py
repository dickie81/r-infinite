#!/usr/bin/env python3
"""
v_EW residual decomposition: NOT bundle/scalar gap stacking;
SAME Gram correction as the cosmological constant.

CONTEXT
=======
cascade_gap_mass_influence.py noted that the v_EW residual (-2.20%)
is suggestively 1.33x the bundle/scalar gap (1.66%), and proposed that
v might decompose as two stacked gap contributions through the Higgs
Yukawa coupling structure.

Hypothesis tested: v_residual = 2 * delta_BS, or v_residual = delta_BS +
some chi^k filter shift, or other gap-based combination.

RESULT (negative for hypothesis, positive structural finding)
==============================================================
The hypothesis is wrong.  v_EW residual decomposes cleanly via the
SAME Gram correction that closes the cosmological constant:

  v_lead = M_Pl,red * alpha_s_lead * exp(-pi/alpha(5)) = 240.72 GeV
  v_PDG  = 246.22 GeV
  Residual: -2.235%

  v_corrected = v_lead * exp(delta_path(5, 217))
              = 240.72 * 1.02131
              = 245.85 GeV
              -> dev -0.152%

This is the IDENTICAL Gram correction applied to the cosmological
constant:

  rho_Lambda residual:  -2.2%  ->  -0.07%  via delta_path(5, 217)
  v_EW residual:        -2.2%  ->  -0.15%  via delta_path(5, 217)

Both close via the same full-cascade Gram correction.  v and rho_Lambda
are SIBLING descent-dependent observables, not bundle/scalar-related.

WHY THE SAME GRAM AS CC
=======================
Both quantities are expressed against the reduced Planck mass M_Pl,red:
  rho_Lambda / M_Pl,red^4 (cascade invariant)
  v_EW / M_Pl,red          (electroweak / Planck ratio)

M_Pl,red itself is the cosmic gravitational scale set by the FULL
cascade descent.  Quantities expressed against M_Pl,red inherit the
full-cascade Gram correction delta_path(5, 217) -- the same one that
appears in the cascade invariant Omega_19 * Omega_217.

The bundle/scalar gap (mechanism 3) operates at gauge-home boundaries
within the cascade.  v_EW does not cross gauge-home boundaries in its
derivation: the cascade formula uses alpha(5) (volume max layer, no
gauge group) and exp(-pi/alpha(5)) (Kosterlitz-Thouless vortex action).
Neither involves bundle structure.

THE 1.33x COINCIDENCE
=====================
v_residual = 2.235%, bundle/scalar gap = 1.659%, ratio 1.347x.

Coincidence: both quantities happen to be ~2% in magnitude, but they
have different structural sources:
  - v_residual = delta_path(5, 217) = 2.13% (Gram, mech 1)
  - bundle/scalar gap = log(N_c * vol(SU(2)) / exp(Phi descent)) =
    1.66% (bundle, mech 3)

The 1.33x ratio is the ratio of these two unrelated cascade quantities,
not a structural relationship.

REVISED v CLOSURE STATUS
========================
Earlier framing (Part IVb thm:vev): "v_cas = 240.8 GeV with -2.2%
residual; partial closure pending higher-order corrections."

Revised framing: v_cas closes to -0.15% via the same Gram correction
as the cosmological constant.  Both are Tier-2-equivalent closures:

  rho_Lambda:  -0.07% (Planck 1-sigma compatible)
  v_EW:        -0.15% (essentially closed at standing precision)

The "partial closure" framing should be updated; v has the same
closure status as the cosmological constant under the Gram mechanism.

WHAT THIS MEANS
===============
1. The bundle/scalar gap does NOT influence v_EW.  This is consistent
   with the three-mechanism picture: v is in the descent regime,
   sister to rho_Lambda; bundle/scalar gap is at gauge-home boundaries.

2. v and rho_Lambda close TOGETHER via mechanism (1).  This unifies
   the two largest cascade quantities (the master mass scale and the
   cosmological constant) under a single first-order correction.

3. The cascade has THREE Gram-corrected closures now visible:
   - rho_Lambda: -0.07% (after delta_path(5, 217))
   - v_EW:       -0.15% (after delta_path(5, 217))
   - bundle/scalar gap at d=13->21: -0.05% (after delta_path(5, 21))

   All three are descent-dependent, all close via Gram path correlations.
   The d_max for each = the deepest layer relevant to the observable.

4. The bundle/scalar gap remains specific to gauge-home transitions
   in the quark sector.  It influences quark masses (-1.4% to +1.3%
   residuals) but NOT v, NOT rho_Lambda, NOT lepton masses.

UPDATED THREE-MECHANISM PICTURE
================================
The cascade's three correction mechanisms now have clearer scopes:

  (1) Gram path-correlation delta_path(5, d_max)
      Closes: rho_Lambda, v_EW (descent-dependent absolute scales)

  (2) Channel-count chi^k filter alpha(d*)/chi^k
      Closes: 8 precision closures (alpha_s, m_tau/m_mu, sin^2 theta_W,
      Omega_m, ell_A, m_tau abs, theta_C, b/s)

  (3) Gauge-bundle orbit measure vol(SU(N)) at gauge home
      Closes: quark mass ratios at gauge-home transitions
      (s/d, c/u, t/b)

Each mechanism has a clear domain.  No mechanism subsumes the others.
Each is sourced at distinguished cascade structure (full descent path
correlations; distinguished cascade landmarks; gauge-home Lie group
manifolds).
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
from cascade_gram_bott_tower import gram_path_sum, Phi_cascade  # noqa: E402

M_PL_RED = 2.435e18  # GeV
ALPHA_S_LEAD = 0.1159
ALPHA_S_FULL = 0.1179
V_PDG = 246.21965
N_C = 3
OMEGA_3 = 2 * math.pi ** 2


def v_cascade(alpha_s: float = ALPHA_S_LEAD) -> float:
    return M_PL_RED * alpha_s * math.exp(-pi / alpha_cas(5))


def report_setup() -> None:
    print("=" * 88)
    print("STEP 1: setup -- the v_EW residual under test")
    print("=" * 88)
    print()
    v_lead = v_cascade()
    print(f"  v_lead = M_Pl,red * alpha_s_lead * exp(-pi/alpha(5))")
    print(f"        = {M_PL_RED:.4e} * {ALPHA_S_LEAD} * exp(-{pi/alpha_cas(5):.4f})")
    print(f"        = {v_lead:.4f} GeV")
    print()
    print(f"  v_PDG = {V_PDG:.4f} GeV")
    print(f"  Residual = {100*(v_lead - V_PDG)/V_PDG:+.3f}%")
    print(f"  log shift needed = {math.log(V_PDG/v_lead):+.6f}")
    print()


def report_hypothesis_test() -> None:
    print("=" * 88)
    print("STEP 2: hypothesis -- is v_residual = 2 * bundle/scalar gap?")
    print("=" * 88)
    print()
    e_phi = math.exp(Phi_cascade(21) - Phi_cascade(13))
    target = N_C * OMEGA_3
    gap = math.log(target / e_phi)
    v_lead = v_cascade()
    needed = math.log(V_PDG / v_lead)

    print(f"  Bundle/scalar gap (log)  = {gap:+.6f}  ({100*(math.exp(gap)-1):.3f}%)")
    print(f"  2 * gap                  = {2*gap:+.6f}  ({100*(math.exp(2*gap)-1):.3f}%)")
    print(f"  v residual log shift     = {needed:+.6f}  ({100*(math.exp(needed)-1):.3f}%)")
    print()
    print(f"  Ratio (v shift / gap)    = {needed/gap:.4f}")
    print()
    print(f"  Test: v_lead * exp(2*gap) = {v_lead*math.exp(2*gap):.4f} vs PDG {V_PDG}")
    print(f"        Deviation         = {100*(v_lead*math.exp(2*gap) - V_PDG)/V_PDG:+.3f}%")
    print()
    print(f"  2 * gap OVERSHOOTS PDG by 1%.  Single gap UNDERSHOOTS.  Neither")
    print(f"  is the right correction.")
    print()


def report_correct_decomposition() -> None:
    print("=" * 88)
    print("STEP 3: the correct decomposition -- same Gram as rho_Lambda")
    print("=" * 88)
    print()
    v_lead = v_cascade()
    gram_full = gram_path_sum(5, 217)
    v_gram = v_lead * math.exp(gram_full)
    print(f"  delta_path(5, 217) = {gram_full:.6f}  ({100*(math.exp(gram_full)-1):.3f}%)")
    print(f"  This is the FULL-cascade Gram correction (observer host to")
    print(f"  cascade terminus), the same one used in the cosmological constant")
    print(f"  derivation.")
    print()
    print(f"  v_corrected = v_lead * exp(delta_path(5, 217))")
    print(f"              = {v_lead:.4f} * {math.exp(gram_full):.6f}")
    print(f"              = {v_gram:.4f} GeV")
    print(f"  vs PDG       {V_PDG} GeV")
    print(f"  Deviation:   {100*(v_gram - V_PDG)/V_PDG:+.3f}%")
    print()
    print("  v closes to -0.15% via the SAME Gram correction as rho_Lambda.")
    print()


def report_unified_closure() -> None:
    print("=" * 88)
    print("STEP 4: v and rho_Lambda are sibling descent-dependent observables")
    print("=" * 88)
    print()
    print("  Cosmological constant:")
    print("    rho_Lambda / M_Pl,red^4 leading: 6.996e-121  (-2.2% from Planck)")
    print("    + delta_path(5, 217)            : 7.145e-121  (-0.07% from Planck)")
    print()
    print("  Electroweak VEV:")
    print("    v_EW leading:                   240.72 GeV  (-2.24% from PDG)")
    print("    + delta_path(5, 217)            245.85 GeV  (-0.15% from PDG)")
    print()
    print("  IDENTICAL Gram correction closes both at standing precision.")
    print()
    print("  STRUCTURAL READING:")
    print()
    print("    Both quantities are expressed against the reduced Planck mass")
    print("    M_Pl,red.  M_Pl,red itself is the cosmic gravitational scale,")
    print("    set by the full cascade descent.  Quantities expressed against")
    print("    M_Pl,red inherit the full-cascade Gram correction delta_path(5, 217).")
    print()
    print("    The bundle/scalar gap (mechanism 3) operates at gauge-home")
    print("    boundaries WITHIN the cascade.  v does not cross gauge-home")
    print("    boundaries in its derivation -- exp(-pi/alpha(5)) is at d=5")
    print("    (volume max, no gauge group).  So bundle/scalar gap doesn't")
    print("    influence v.")
    print()


def report_revised_status() -> None:
    print("=" * 88)
    print("STEP 5: revised v closure status")
    print("=" * 88)
    print()
    print("  Earlier (Part IVb thm:vev): 'v_cas = 240.8 GeV, -2.2% residual,")
    print("  partial closure pending higher-order corrections.'")
    print()
    print("  Revised: v_cas closes to -0.15% via delta_path(5, 217) Gram")
    print("  correction.  Tier-2-equivalent closure, structurally parallel")
    print("  to the cosmological constant.")
    print()
    print("  Updated cascade closures (Tier 2 via Gram, mechanism 1):")
    print("    rho_Lambda:  -0.07% (Planck 1-sigma compatible)")
    print("    v_EW:        -0.15% (essentially closed at standing precision)")
    print()
    print("  The bundle/scalar gap remains specific to gauge-home transitions:")
    print("    quark mass ratios show ~1% systematic residuals (gap signature)")
    print("    leptons stay at ~0.1% (no gap)")
    print("    v and rho_Lambda are gap-free (descent regime, mechanism 1)")
    print()


def report_three_mechanism_update() -> None:
    print("=" * 88)
    print("STEP 6: updated three-mechanism scope")
    print("=" * 88)
    print()
    print("  Three independent first-order correction mechanisms with clearer")
    print("  domains after this finding:")
    print()
    print("  +-----------------------+----------------------------+")
    print("  | mechanism             | closes                     |")
    print("  +-----------------------+----------------------------+")
    print("  | (1) Gram path-corr    | rho_Lambda (-0.07%)        |")
    print("  |     delta_path(5, d)  | v_EW (-0.15%)              |")
    print("  |                       | bundle/scalar gap          |")
    print("  |                       | at d=13->21 (-0.05%)       |")
    print("  +-----------------------+----------------------------+")
    print("  | (2) chi^k filter      | 8 precision closures:      |")
    print("  |     alpha(d*)/chi^k   | alpha_s, m_tau/m_mu, ...   |")
    print("  +-----------------------+----------------------------+")
    print("  | (3) gauge-bundle vol  | quark mass ratios:         |")
    print("  |     vol(SU(N))        | s/d, c/u, t/b              |")
    print("  +-----------------------+----------------------------+")
    print()
    print("  Each mechanism closes a distinct residual class with a distinct")
    print("  structural source.  No mechanism subsumes the others.")
    print()


def main() -> int:
    print("=" * 88)
    print("v_EW RESIDUAL DECOMPOSITION (Option A test)")
    print("Hypothesis: v residual is bundle/scalar gap stacking.")
    print("Result:     NOT confirmed.  v closes via SAME Gram as cosmological")
    print("            constant, not via gap mechanism.")
    print("=" * 88)
    print()
    report_setup()
    report_hypothesis_test()
    report_correct_decomposition()
    report_unified_closure()
    report_revised_status()
    report_three_mechanism_update()
    print("=" * 88)
    print("HEADLINE:")
    print()
    print("  v_EW residual is NOT bundle/scalar gap stacking.")
    print()
    print("  v closes to -0.15% via delta_path(5, 217) -- the SAME Gram")
    print("  correction that closes the cosmological constant.  Both are")
    print("  full-descent quantities expressed against M_Pl,red, and both")
    print("  inherit the same first-order Gram correction.")
    print()
    print("  The 1.33x ratio between v_residual (2.24%) and bundle/scalar")
    print("  gap (1.66%) was a numerical coincidence, not a structural")
    print("  relationship.  Two unrelated cascade quantities that happen to")
    print("  be ~2% in magnitude.")
    print()
    print("  REVISED STATUS: v_EW promotes from 'partial closure with -2.2%")
    print("  residual' to 'closed at standing precision via Gram', sister to")
    print("  the cosmological constant.")
    print()
    print("  Bundle/scalar gap stays in its lane: quark masses + d=13->21")
    print("  span only.  v and rho_Lambda are descent-dependent (mech 1)")
    print("  not bundle (mech 3).")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
