#!/usr/bin/env python3
"""
Probe x = 4/5 universality across cross-sector mass ratios.

CONTEXT
=======
The cascade alpha_s formula structurally encodes RG running for couplings:

  alpha_s_cascade = alpha(12) * exp(Phi(12)) ~ alpha_s(M_Z)

This is established cascade structure: alpha(12) ~ alpha_s(M_GUT), and
the descent factor exp(Phi(12)) ~ 2.90 mirrors the QCD running factor
M_GUT -> M_Z (~2.95).  The Phi descent IS the running for couplings.

This led to a conjecture that the same descent generator with a different
exponent might give mass running:

  m_b / m_tau = exp(Phi(12))^x

Empirically, x = 4/5 matches m_b/m_tau to -0.4%:

  exp(Phi(12))^(4/5) = 2.344  (PDG m_b/m_tau = 2.353, match -0.37%)

with x = 4/5 = d_observer / d_host (4 = observer dim, 5 = host dim)
conjectured as the cascade mass-running exponent.  This script tests
whether the SAME exponent universally applies across other cross-sector
mass ratios.

RESULT
======
NOT confirmed.  Only m_b/m_tau matches at standing precision.  The
conjecture x=4/5 is essentially a one-parameter fit to one data point.

The cascade's REAL RG-running encoding is for COUPLINGS via the
alpha_s formula above (genuine structural feature).  Mass running
does NOT extend trivially from the same mechanism.

PROBE: required Phi(d) for each cross-sector ratio if x=4/5 universal
======================================================================

  ratio          PDG value      log(R)/0.8     closest cascade Phi(d)
  ------------------------------------------------------------------------
  m_b/m_tau      2.3525        +1.0693        Phi(12) = 1.065  <-- MATCH (SU(3) home)
  m_top/m_tau    97.1883       +5.7208        Phi(21) = 5.494  (off 4%)
  m_c/m_mu       12.0199       +3.1082        Phi(17) = 3.231  (d=17 not distinguished)
  m_s/m_mu       0.8840        -0.1541        Phi(6) = -0.132  (d=6 not distinguished)
  m_u/m_e        4.2270        +1.8019        Phi(14) = 1.830  (U(1) home, but cascade
                                                                 already gets this without running)
  m_d/m_e        9.1390        +2.7657        Phi(16) = 2.733  (d=16 not distinguished)

Only m_b/m_tau lands at a structurally distinguished cascade layer
(d=12, SU(3) home).  Other ratios either:
  (a) Don't match a distinguished layer (d=6, 16, 17 not cascade-natural)
  (b) Are already cascade-derived without running (m_top, m_c, m_s, m_u, m_d)

PROBE: with x=4/5 fixed and Phi at distinguished layers, what predictions?
==========================================================================

  Test: cascade prediction = exp(Phi(d_distinguished))^(4/5) for various d

  ratio                 PDG    Phi(d) used  cascade pred       dev
  -----------------------------------------------------------------------
  m_b/m_tau          2.3525        Phi(12)        2.3437   -0.37% MATCH
  m_top/m_tau       97.1883        Phi(21)       81.0259  -16.63% MISS
  m_c/m_mu          12.0199        Phi(14)        4.3222  -64.04% MISS
  m_s/m_mu           0.8840         Phi(5)        0.9150   +3.51% close-ish
  m_u/m_e            4.2270        Phi(14)        4.3222   +2.25% close-ish
  m_d/m_e            9.1390        Phi(14)        4.3222  -52.71% MISS

Two suggestive close matches (m_s/m_mu, m_u/m_e at Phi(5) and Phi(14))
but these could be coincidence -- the cascade already derives these
ratios via different routes with better precision.

HONEST INTERPRETATION
=====================
The x = 4/5 conjecture FAILS the universality test:

  - 1/6 ratios match at standing precision (m_b/m_tau)
  - 2/6 are suggestive but coincidence-likely
  - 3/6 fail by 16-64% (clear misses)

The strong reading "x = 4/5 is the universal cascade mass-running
exponent" is NOT supported.

Weaker reading "x = 4/5 with Phi(SU(3) home) is specifically the
running rule for m_b/m_tau" remains a one-parameter fit.

WHY THE CASCADE DOESN'T NEED RUNNING FOR OTHER RATIOS
=====================================================

The cascade already derives all other cross-sector ratios via
internal structure:

  m_top/m_tau = (v_cas/sqrt(2)) / m_tau ~ 97.1     (within 0.1%)
  m_c/m_mu    = (m_top / N_c·b/s) / m_mu ~ 12.17  (within 1.3%)
  m_s/m_mu    = (m_b / b/s) / m_mu ~ 0.886         (within 0.2%)
  m_u/m_e     = (m_c / 6pi^4) / m_e ~ 4.30        (within 1.7%)
  m_d/m_e     = (m_s / Omega_3) / m_e ~ 9.27       (within 1.4%)

Only m_b/m_tau lacks cascade-internal derivation -- the cascade
takes m_b as anchor, then derives m_b/m_tau from there.

So the question "can the cascade derive m_b cascade-internally" is
narrower than I'd framed.  It's really asking "can we eliminate the
m_b anchor by some specific cascade rule?"  The x = 4/5 conjecture is
ONE such rule that gives the right answer (within 0.4%), but with
only one constraint, ANY one-parameter rule could fit.

WHAT STRUCTURAL EVIDENCE WOULD STRENGTHEN THE CONJECTURE
=========================================================
For the x=4/5 conjecture to be elevated from "one-parameter fit" to
"structural rule," we'd need:

  (a) Independent confirmation: a SECOND mass-running observable that
      the cascade currently doesn't predict, and that x=4/5 matches.
      (Not found in this probe.)

  (b) Structural derivation: a cascade-internal proof that x = (d-1)/d
      = d_observer/d_host is forced.  Currently a suggestive reading
      (shell-to-bulk projection) without a derivation.

  (c) Reconciliation with QCD: cascade x=4/5 = 0.80 differs from QCD
      gamma_m/(2 b_0) = 12/23 = 0.52.  Either cascade differs from
      QCD here as a falsifiable prediction, or there's a mapping.

None of (a)-(c) are achieved.

CASCADE-NATIVE RG RUNNING STATUS
================================
Two distinct findings, with different status:

  REAL: cascade alpha_s formula structurally encodes RG running
        alpha_s_cascade = alpha(12) * exp(Phi(12)) ~  alpha_s(M_Z)
        This is established cascade structure that mirrors QCD running.

  SPECULATIVE: x = 4/5 mass running exponent is a one-parameter fit
        to m_b/m_tau alone.  Doesn't universalize across other cross-
        sector ratios.  No structural derivation.  Likely coincidence
        unless additional structural support is found.

Honest revision: cascade has REAL structural hints of coupling-running
(via Phi descent) but does NOT have a derived mass-running mechanism.
m_b cascade-internal derivation requires either:
  - New structural insight (not the simple x=4/5 ansatz)
  - External RG running infrastructure
  - Accepting m_b as cascade quark-sector anchor

CONCLUSION
==========
The probe is a NEGATIVE result for the x=4/5 universality claim.
The conjecture's strength was overstated by extrapolating from one
data point.  Honest current status: m_b cascade-internal derivation
remains open; the cascade's RG-running encoding for couplings is
real but doesn't extend trivially to masses.
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

PDG = {
    'm_e': 0.510998950e-3, 'm_mu': 105.6583755e-3, 'm_tau': 1.77686,
    'm_top': 172.69, 'm_b': 4.18, 'm_c': 1.27,
    'm_u': 2.16e-3, 'm_s': 93.4e-3, 'm_d': 4.67e-3,
}

V_CAS = 243.7
ALPHA_S_LEAD = 0.1159
TWO_SQRT_PI = 2 * math.sqrt(pi)
N_C = 3
B_OVER_S = 44.7436
OMEGA_3 = 2 * pi ** 2


def report_probe() -> None:
    print("=" * 88)
    print("STEP 1: required Phi(d) per cross-sector ratio if x=4/5 universal")
    print("=" * 88)
    print()
    ratios = [
        ('Gen 3', 'm_b/m_tau',   PDG['m_b'] / PDG['m_tau']),
        ('Gen 3', 'm_top/m_tau', PDG['m_top'] / PDG['m_tau']),
        ('Gen 2', 'm_c/m_mu',    PDG['m_c'] / PDG['m_mu']),
        ('Gen 2', 'm_s/m_mu',    PDG['m_s'] / PDG['m_mu']),
        ('Gen 1', 'm_u/m_e',     PDG['m_u'] / PDG['m_e']),
        ('Gen 1', 'm_d/m_e',     PDG['m_d'] / PDG['m_e']),
    ]
    distinguished = {5: 'host', 7: 'area max', 12: 'SU(3)', 13: 'SU(2)',
                     14: 'U(1)', 19: 'phase', 21: 'electron home'}
    print(f"  {'gen':<6s} {'ratio':<14s} {'PDG':>10s} {'log(R)/0.8':>12s} "
          f"{'closest d':>12s} {'distinguished?':>16s}")
    print("  " + "-" * 78)
    for gen, name, val in ratios:
        if val <= 0:
            continue
        needed = math.log(val) / 0.8
        best_d = min(range(5, 30), key=lambda d: abs(Phi_cascade(d) - needed))
        is_dist = distinguished.get(best_d, "no")
        print(f"  {gen:<6s} {name:<14s} {val:>10.4f} {needed:>+12.4f} "
              f"{f'Phi({best_d})':>12s} {is_dist:>16s}")
    print()
    print("  Only m_b/m_tau lands at a distinguished cascade layer (d=12, SU(3)).")
    print("  Other ratios match non-distinguished layers (d=6, 16, 17), making")
    print("  them likely coincidental rather than structural.")
    print()


def report_predictions_at_distinguished() -> None:
    print("=" * 88)
    print("STEP 2: x=4/5 predictions at distinguished cascade layers")
    print("=" * 88)
    print()
    distinguished_d = [5, 7, 12, 13, 14, 19, 21]
    ratios = [
        ('m_b/m_tau',   PDG['m_b'] / PDG['m_tau']),
        ('m_top/m_tau', PDG['m_top'] / PDG['m_tau']),
        ('m_c/m_mu',    PDG['m_c'] / PDG['m_mu']),
        ('m_s/m_mu',    PDG['m_s'] / PDG['m_mu']),
        ('m_u/m_e',     PDG['m_u'] / PDG['m_e']),
        ('m_d/m_e',     PDG['m_d'] / PDG['m_e']),
    ]
    print(f"  {'ratio':<14s} {'PDG':>10s} {'best d':>10s} {'cascade pred':>14s} {'dev':>10s} {'status':<14s}")
    print("  " + "-" * 78)
    for name, pdg_val in ratios:
        best = None
        best_dev = float('inf')
        for d in distinguished_d:
            phi = Phi_cascade(d)
            pred = math.exp(phi * 4/5)
            dev = abs(100 * (pred - pdg_val) / pdg_val)
            if dev < best_dev:
                best_dev = dev
                best = (d, pred)
        d, pred = best
        signed_dev = 100 * (pred - pdg_val) / pdg_val
        status = "MATCH" if best_dev < 2 else ("close" if best_dev < 10 else "MISS")
        print(f"  {name:<14s} {pdg_val:>10.4f} {f'Phi({d})':>10s} {pred:>14.4f} "
              f"{signed_dev:>+9.2f}% {status:<14s}")
    print()
    print("  1/6 MATCH (m_b/m_tau).  3/6 MISS by 16-64%.")
    print("  The conjecture x=4/5 is essentially a one-parameter fit.")
    print()


def report_cascade_already_predicts() -> None:
    print("=" * 88)
    print("STEP 3: cascade already derives most cross-sector ratios without running")
    print("=" * 88)
    print()
    m_e_cas = PDG['m_e']
    m_mu_cas = m_e_cas * 206.4958
    m_tau_cas = m_mu_cas * 16.81731
    m_top_cas = V_CAS / math.sqrt(2)
    m_c_cas = m_top_cas / (N_C * B_OVER_S)
    m_u_cas = m_c_cas / (6 * pi ** 4)
    m_b_cas = PDG['m_b']
    m_s_cas = m_b_cas / B_OVER_S
    m_d_cas = m_s_cas / OMEGA_3
    cas = {
        'm_e': m_e_cas, 'm_mu': m_mu_cas, 'm_tau': m_tau_cas,
        'm_top': m_top_cas, 'm_b': m_b_cas, 'm_c': m_c_cas,
        'm_u': m_u_cas, 'm_s': m_s_cas, 'm_d': m_d_cas,
    }
    ratios = [
        ('m_b/m_tau',   'uses m_b ANCHOR'),
        ('m_top/m_tau', '(v/sqrt(2)) / m_tau'),
        ('m_c/m_mu',    '(m_top / (N_c·b/s)) / m_mu'),
        ('m_s/m_mu',    '(m_b / b/s) / m_mu'),
        ('m_u/m_e',     '(m_c / 6pi^4) / m_e'),
        ('m_d/m_e',     '(m_s / Omega_3) / m_e'),
    ]
    print(f"  {'ratio':<14s} {'cascade':>12s} {'PDG':>12s} {'dev':>8s}  {'route'}")
    print("  " + "-" * 78)
    for name, route in ratios:
        num, den = name.split('/')
        cas_val = cas[num] / cas[den]
        pdg_val = PDG[num] / PDG[den]
        dev = 100 * (cas_val - pdg_val) / pdg_val
        print(f"  {name:<14s} {cas_val:>12.4f} {pdg_val:>12.4f} {dev:>+7.2f}%  {route}")
    print()
    print("  All cross-sector ratios except m_b/m_tau are cascade-derived")
    print("  WITHOUT invoking running.  Only m_b/m_tau lacks internal derivation.")
    print()
    print("  This means the x=4/5 conjecture isn't filling a universal gap --")
    print("  it's filling ONE gap (the m_b anchor) with a one-parameter rule.")
    print()


def report_status() -> None:
    print("=" * 88)
    print("STEP 4: revised status of cascade-native RG running")
    print("=" * 88)
    print()
    print("  REAL (established):")
    print()
    print("    Cascade alpha_s = alpha(12) * exp(Phi(12)) structurally encodes")
    print("    alpha_s RG running.  exp(Phi(12)) ~ 2.90 mirrors QCD M_GUT->M_Z")
    print("    running factor ~2.95.  This is genuine cascade structure that")
    print("    does the work of RG running for the strong coupling.")
    print()
    print("  SPECULATIVE (failed universality test):")
    print()
    print("    The x=4/5 mass-running exponent matches m_b/m_tau to -0.4% but")
    print("    fails for other cross-sector ratios.  Acting on ONE data point.")
    print("    No structural derivation.  Likely coincidence.")
    print()
    print("  WHAT CASCADE CAN AND CAN'T DO:")
    print()
    print("    CAN: structurally derive coupling running (alpha_s).")
    print("    CAN: derive most cross-sector mass ratios via internal structure")
    print("         without invoking running (m_top, m_c, m_s, m_u, m_d).")
    print("    CAN'T: derive m_b cascade-internally without anchor or new")
    print("           structural insight.")
    print()
    print("  m_b joins v_EW-residual and PMNS as standing-precision-open items.")
    print("  Closing m_b would require:")
    print("    (a) New structural insight specific to m_b (no candidate yet)")
    print("    (b) RG running infrastructure imported externally")
    print("    (c) Accepting m_b as cascade's quark-sector input")
    print()


def main() -> int:
    print("=" * 88)
    print("PROBE: does x=4/5 mass-running exponent universally apply?")
    print("RESULT: NO.  One-parameter fit to one data point (m_b/m_tau).")
    print("=" * 88)
    print()
    report_probe()
    report_predictions_at_distinguished()
    report_cascade_already_predicts()
    report_status()
    print("=" * 88)
    print("HEADLINE: x=4/5 conjecture FAILS universality.")
    print()
    print("  Only m_b/m_tau matches at standing precision; other cross-sector")
    print("  ratios already cascade-derived without running, or fail with x=4/5")
    print("  by 16-64%.")
    print()
    print("  The cascade's REAL RG-running encoding is via the alpha_s formula")
    print("  alpha_s = alpha(12) * exp(Phi(12)).  This is genuine structural")
    print("  feature mirroring QCD coupling running.  It does NOT extend to")
    print("  a simple universal mass-running rule.")
    print()
    print("  m_b cascade-internal derivation remains open.  The x=4/5 ansatz")
    print("  was over-promising.  Honest current status: cascade has 5/6")
    print("  quark masses internally derived; m_b is the irreducible anchor.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
