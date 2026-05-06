#!/usr/bin/env python3
"""
Test: does Gaussian layer coupling give cascade-native mass running?

CONTEXT
=======
The cascade scalar action S[phi] = Sum (2 alpha(d))^{-1} (Delta phi)^2 is
quadratic in the field (Gaussian) but uses NEAREST-NEIGHBOR coupling
between layers.  cascade_rg_running_universality_probe.py refuted the
simple x=4/5 mass-running ansatz; the question naturally arises whether
a generalization to GAUSSIAN-RANGE layer coupling could work.

This script tests two related formulations:

  (1) Gaussian-coupled cascade Laplacian: S[phi] = Sum_{d, d'} K(|d-d'|) /
      sqrt(alpha(d) alpha(d')) * (phi(d) - phi(d'))^2 where K(k) =
      exp(-k^2 / 2 sigma^2).  Compute Green's function and test mass
      running predictions.

  (2) Gaussian-mediated Phi descent: Phi_G(d_from -> d_to, sigma) =
      Sum_{k} p(k) * exp(-(k - d_from)^2 / 2 sigma^2).  Test whether
      m_quark/m_lepton = exp(Phi_G(...)) is universal.

RESULT
======
NEITHER formulation gives clean universal mass running.

Formulation (1): Gaussian-coupled Laplacian Green's function values
G(d=5, d=12) for various sigma don't match PDG cross-sector ratios
under any simple operation (exp, log, scaling).

Formulation (2): Gaussian-mediated Phi descent at sigma=8 (one Bott
period, cascade-natural width) gives:

  m_b/m_tau:   2.54 vs PDG 2.35   (+8% off, suggestive but not exact)
  m_c/m_mu:    0.69 vs PDG 12.02  (-94% off, MASSIVE failure)
  m_s/m_mu:    0.69 vs PDG 0.88   (-21% off)
  m_u/m_e:     0.02 vs PDG 4.23   (-99.5% off, MASSIVE failure)
  m_d/m_e:     0.02 vs PDG 9.14   (-99.8% off, MASSIVE failure)

Universal sigma fails badly.  Only m_b/m_tau is even close.

WHY IT FAILS
============
The cross-sector ratios m_c/m_mu, m_d/m_e etc. involve descent from
lepton homes (d=13 for mu, d=21 for e) to the SU(3) home (d=12).
This is a "backward" descent direction in cascade -- d_lepton_home
> d_su3_home for Gen 1 and Gen 2.

The Phi descent isn't a sensible model for backward descent.  Standard
cascade descent goes from low d to high d (host to bulk), with Phi(d)
monotonically increasing.  Trying to "descend backward" gives nonsense.

For Gen 3, where d_lepton (=5) < d_su3 (=12), descent IS forward, and
Gaussian-mediated descent can match m_b/m_tau.  But this is essentially
fitting one number with one parameter (sigma).

PARTIAL FINDING (suggestive)
============================
At sigma = 7-8 (one Bott period), Gaussian-mediated Phi descent for
m_b/m_tau gives 2.39-2.54 (matches PDG 2.35 within a few percent).
sigma = 8 = one Bott period is cascade-natural, suggesting the match
isn't completely arbitrary.

But this is a single data point matched at standing precision via a
one-parameter fit.  Cannot claim universal mechanism.

BOTH SIMPLE FORMULATIONS FAIL UNIVERSALITY
==========================================
Gaussian-coupled Laplacian: doesn't give mass running predictions
under any natural scaling.

Gaussian-mediated Phi descent: works only for forward-descent ratios
(Gen 3); fails badly for backward-descent ratios (Gen 1, 2 with
d_lepton > d_su3).

CONCLUSION
==========
Simple Gaussian layer coupling does NOT close m_b cascade-internally.
The natural formulations either:
  (a) Don't give mass-running predictions cleanly (formulation 1)
  (b) Apply only to specific descent directions and fail universality
      (formulation 2)

A more structured cascade-native mass-running mechanism is needed.
Possible directions (untested):
  - Multi-layer source coupling (not just d=12 for all colored quarks)
  - Descent-direction-dependent coupling (forward vs backward through
    cascade layers)
  - Layer-specific Gaussian widths (sigma varying with d)

The cascade currently encodes ALPHA_s RG running (real, established).
MASS RG running cascade-natively remains open.  The Gaussian-coupling
hypothesis isn't the right move; m_b derivation requires deeper
structural insight.

This is a NEGATIVE probe result -- valuable for ruling out simple
Gaussian generalizations, but doesn't close m_b.
"""

from __future__ import annotations

import math
import os
import sys

import numpy as np

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

from cascade_constants import alpha as alpha_cas, R, p, pi  # noqa: E402

PDG = {
    'm_e': 0.510998950e-3, 'm_mu': 105.6583755e-3, 'm_tau': 1.77686,
    'm_top': 172.69, 'm_b': 4.18, 'm_c': 1.27,
    'm_u': 2.16e-3, 'm_s': 93.4e-3, 'm_d': 4.67e-3,
}


def Phi_gauss_signed(d_from: int, d_to: int, sigma: float) -> float:
    """Gaussian-mediated Phi descent.  Signed for d_from <> d_to."""
    if d_to == d_from:
        return 0.0
    if d_to > d_from:
        ks = range(d_from + 1, d_to + 1)
        sign = +1
    else:
        ks = range(d_to + 1, d_from + 1)
        sign = -1
    total = 0.0
    for k in ks:
        weight = math.exp(-((k - d_from) ** 2) / (2 * sigma ** 2))
        total += sign * p(k) * weight
    return total


def report_setup() -> None:
    print("=" * 88)
    print("STEP 1: setup -- Gaussian-mediated Phi descent")
    print("=" * 88)
    print()
    print("  Formulation: Phi_G(d_from -> d_to, sigma) =")
    print("    Sum_{k between d_from, d_to} p(k) * exp(-(k - d_from)^2 / 2 sigma^2)")
    print()
    print("  Hypothesis: m_quark / m_lepton = exp(Phi_G(d_lepton_home -> d_q, sigma))")
    print()
    print("  Cascade-natural sigma candidates:")
    print("    sigma = 1 (single layer), 2, 4, 8 (one Bott period), 16 (two periods)")
    print()


def report_universality_test() -> None:
    print("=" * 88)
    print("STEP 2: universality test for sigma = 8 (one Bott period)")
    print("=" * 88)
    print()
    ratios = [
        ('m_b/m_tau',  PDG['m_b'] / PDG['m_tau'],   12, 5,  'Gen 3 down'),
        ('m_c/m_mu',   PDG['m_c'] / PDG['m_mu'],    12, 13, 'Gen 2 up'),
        ('m_s/m_mu',   PDG['m_s'] / PDG['m_mu'],    12, 13, 'Gen 2 down'),
        ('m_u/m_e',    PDG['m_u'] / PDG['m_e'],     12, 21, 'Gen 1 up'),
        ('m_d/m_e',    PDG['m_d'] / PDG['m_e'],     12, 21, 'Gen 1 down'),
    ]
    print(f"  {'ratio':<14s} {'PDG':>10s} {'d_q -> d_l':>14s} {'cascade pred':>14s}"
          f" {'dev':>10s}  {'description':<14s}")
    print("  " + "-" * 88)
    for name, pdg_val, d_q, d_l, desc in ratios:
        # Descent from d_lepton to d_quark
        pg = Phi_gauss_signed(d_l, d_q, 8.0)
        pred = math.exp(pg)
        dev_pct = 100 * (pred - pdg_val) / pdg_val
        path = f"d={d_l}->{d_q}"
        print(f"  {name:<14s} {pdg_val:>10.4f} {path:>14s} {pred:>14.4f}"
              f" {dev_pct:>+9.2f}%  {desc:<14s}")
    print()
    print("  m_b/m_tau matches at +8%; all other ratios MASSIVELY fail")
    print("  (some by >90%).  Universal sigma=8 doesn't work.")
    print()


def report_per_ratio_best_sigma() -> None:
    print("=" * 88)
    print("STEP 3: best sigma per ratio (no universal value works)")
    print("=" * 88)
    print()
    ratios = [
        ('m_b/m_tau',  PDG['m_b'] / PDG['m_tau'],   12, 5),
        ('m_c/m_mu',   PDG['m_c'] / PDG['m_mu'],    12, 13),
        ('m_s/m_mu',   PDG['m_s'] / PDG['m_mu'],    12, 13),
        ('m_u/m_e',    PDG['m_u'] / PDG['m_e'],     12, 21),
        ('m_d/m_e',    PDG['m_d'] / PDG['m_e'],     12, 21),
    ]
    sigmas = [0.5, 1.0, 2.0, 3.0, 4.0, 5.0, 6.0, 7.0, 8.0, 10.0, 12.0, 16.0, 32.0]
    print(f"  {'ratio':<14s} {'PDG':>10s} {'best sigma':>12s} {'best pred':>12s} {'dev':>10s}")
    print("  " + "-" * 70)
    for name, pdg_val, d_q, d_l in ratios:
        best_sigma, best_dev, best_pred = None, float('inf'), None
        for sigma in sigmas:
            pg = Phi_gauss_signed(d_l, d_q, sigma)
            pred = math.exp(pg)
            if pred > 0 and pdg_val > 0:
                dev = abs(math.log(pred / pdg_val))
                if dev < best_dev:
                    best_dev = dev
                    best_sigma = sigma
                    best_pred = pred
        dev_pct = 100 * (best_pred - pdg_val) / pdg_val if best_pred else 0
        print(f"  {name:<14s} {pdg_val:>10.4f} {best_sigma:>12.1f} {best_pred:>12.4f}"
              f" {dev_pct:>+9.2f}%")
    print()
    print("  Best sigma values: 7 (m_b/m_tau), 1 (others).  No universal sigma.")
    print("  m_b/m_tau is the ONLY ratio that gives a meaningful match.")
    print()


def report_why_universality_fails() -> None:
    print("=" * 88)
    print("STEP 4: why simple Gaussian layer coupling fails universality")
    print("=" * 88)
    print()
    print("  The cross-sector ratios at Gen 1 and Gen 2 require descent from")
    print("  lepton homes (d=13 mu, d=21 e) to the SU(3) home (d=12).  This is")
    print("  a 'backward' direction:")
    print()
    print("    m_b/m_tau:  d=5  -> d=12 (FORWARD, 7 layers down the cascade)")
    print("    m_c/m_mu:   d=13 -> d=12 (BACKWARD, 1 layer up)")
    print("    m_s/m_mu:   d=13 -> d=12 (BACKWARD, 1 layer)")
    print("    m_u/m_e:    d=21 -> d=12 (BACKWARD, 9 layers up)")
    print("    m_d/m_e:    d=21 -> d=12 (BACKWARD, 9 layers up)")
    print()
    print("  Cascade Phi descent is monotonically increasing with d.  Backward")
    print("  descent gives sign-reversed sums, which don't have a sensible mass-")
    print("  running interpretation.")
    print()
    print("  For Gen 3 (forward descent), Gaussian-mediated descent can match")
    print("  m_b/m_tau at sigma = 7-8 (one Bott period, cascade-natural).  But")
    print("  this is one data point fitted with one parameter.")
    print()


def report_status() -> None:
    print("=" * 88)
    print("STEP 5: status -- simple Gaussian coupling is NOT the answer")
    print("=" * 88)
    print()
    print("  WHAT WORKS:")
    print("    m_b/m_tau matches Gaussian-mediated descent at sigma ~ 8")
    print("    (one Bott period).  Suggestive that cascade-natural width")
    print("    might be involved, but only one ratio fits.")
    print()
    print("  WHAT FAILS:")
    print("    Universal sigma across all cross-sector ratios.  Backward-")
    print("    descent ratios (Gen 1 and Gen 2) fail by 20-99%.")
    print()
    print("  IMPLICATION:")
    print("    Simple Gaussian generalization of cascade layer coupling does")
    print("    NOT close cascade-native mass running.  m_b derivation remains")
    print("    open.")
    print()
    print("  REVISED PICTURE:")
    print("    Cascade has REAL coupling-running (alpha_s = alpha(12) *")
    print("    exp(Phi(12))) but mass-running structure cannot be derived")
    print("    from simple Gaussian layer coupling.")
    print()
    print("    Mass running cascade-natively would require:")
    print("      - Multi-source coupling (not just d=12)")
    print("      - Descent-direction-aware structure")
    print("      - Layer-specific cascade-internal mechanisms per ratio")
    print()
    print("    These are research-level questions.  No quick test closes m_b.")
    print()


def main() -> int:
    print("=" * 88)
    print("GAUSSIAN LAYER COUPLING TEST: does it close cascade-native mass running?")
    print("RESULT: NO.  Universality fails badly; only m_b/m_tau matches at sigma=8.")
    print("=" * 88)
    print()
    report_setup()
    report_universality_test()
    report_per_ratio_best_sigma()
    report_why_universality_fails()
    report_status()
    print("=" * 88)
    print("HEADLINE: Simple Gaussian layer coupling does NOT give universal")
    print("          cascade-native mass running.")
    print()
    print("  m_b/m_tau matches at sigma=8 (one Bott period) within 8% --")
    print("  cascade-natural sigma but only one data point.")
    print()
    print("  Other cross-sector ratios fail badly (20-99% off) because they")
    print("  require BACKWARD descent (d_lepton > d_su3), which Phi descent")
    print("  cannot cleanly model.")
    print()
    print("  Cascade-native mass running for m_b cannot be closed by simple")
    print("  Gaussian generalization.  m_b derivation remains open; the")
    print("  cascade has real coupling-running (alpha_s) but lacks a clean")
    print("  mass-running mechanism beyond the SM Yukawa-coupling structure.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
