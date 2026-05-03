#!/usr/bin/env python3
"""
Cascade-native RG running: structural hints, conjectural derivation.

CONTEXT
=======
Option C investigation (cascade_mb_internal_attempt.py) showed that
m_b cannot be derived cascade-internally via simple bundle reading at
d=12.  One of the obstacles identified was:

  "Cross-sector m_b/m_tau at observation involves QCD RG running, which
   is NOT cascade-internal."

This script asks: is RG running cascade-native?  Could the cascade's
layer-dependent quantities (Phi(d), alpha(d), Omega_d) encode what
QFT calls RG running?

STRUCTURAL HINT (REAL)
======================
The cascade alpha_s formula already does something RG-running-like:

  alpha_s_cascade = alpha(12) * exp(Phi(12)) = 0.040 * 2.90 = 0.116

This is structurally:
  - alpha(12) = cascade coupling 'at d=12 layer'  ~  alpha_s(M_GUT) ~ 0.04
  - exp(Phi(12)) = cascade descent factor d=12 -> d=5
  - alpha_s_cascade = 'alpha at observer scale'  ~  alpha_s(M_Z) ~ 0.118

The cascade Phi descent from d=12 to d=5 provides a running factor
exp(Phi(12)) = 2.90 structurally analogous to the QCD running
alpha_s(M_GUT) -> alpha_s(M_Z) by factor ~2.95.

This is the cascade implicitly encoding alpha_s running through its
descent generator -- a real, existing structural feature.

EXTENSION TO MASSES (CONJECTURAL)
==================================
QCD mass running has the form

  m(mu) = m(mu_0) * (alpha_s(mu) / alpha_s(mu_0))^(gamma_m / (2 b_0))

where gamma_m is the mass anomalous dimension and b_0 is the QCD beta-
function coefficient.  For N_f=5 (relevant for m_b GUT->2GeV), the
exponent gamma_m/(2 b_0) = 12/23 ~ 0.52.

If cascade encodes this as
  m(observer) = m(d-layer) * exp(Phi(d-layer))^x
for some cascade-natural x, the question is what x gives observation.

Empirical check (cascade m_tau given, target m_b/m_tau = 2.3525 at observation):

  exp(Phi(12))^x = 2.3525
  x = log(2.3525) / Phi(12) = 0.8035

Cascade-natural candidates near 0.8035:
  4/5 = 0.8000  (off 0.4%)  <-- CLEANEST
  (2*N_c-1)/(2*pi) = 0.7958
  1 - 1/(2*pi) = 0.8408
  ln(2.5) = 0.9163

The cleanest match is x = 4/5.  Numerically:
  exp(Phi(12))^(4/5) = 2.3437
  vs PDG m_b/m_tau   = 2.3525
  match: -0.37%      <-- STANDING PRECISION

POSSIBLE STRUCTURAL READING OF x = 4/5
=======================================
The ratio 4/5 = d_observer / d_host:
  - d=4 = observer (3 spatial + 1 time, observer's spacetime)
  - d=5 = cascade host (volume maximum, S^3 boundary of B^5)
  - 4/5 = 'shell-to-bulk' projection ratio at the volume maximum

If the cascade's mass-running exponent is structurally
  x = d_observer / d_host = 4/5

then mass running cascade-natively differs from QCD running (which gives
exponent 12/23 ~ 0.52 for N_f=5).  The cascade exponent 4/5 = 0.8 is
LARGER than the QCD value, meaning cascade predicts STRONGER mass
running than standard QCD.

Is this physically sensible?  Arguments for:
  - Cascade running incorporates ALL inter-layer correlations, not just
    QCD vertex corrections.  The full cascade descent is denser than
    pure QCD.
  - The exponent 4/5 = (d-1)/d at d=d_host is a natural cascade
    primitive (observer/host frame ratio).
  - Cascade alpha_s running uses x=1 (full Phi descent) for couplings;
    masses might use x=(d-1)/d for the 'shell-projection' factor.

Arguments against:
  - This conjectures a NEW structural rule (x = d_obs/d_host) without
    explicit derivation from cascade primitives.
  - The match to PDG is at 0.4% (one data point, prone to over-fitting).
  - QCD's structure (gamma_m, b_0) is well-tested; cascade conjecture
    differs from it.

TESTING THE CONJECTURE
======================
If cascade mass running uses x = 4/5 universally, it should give other
quark mass ratios at observation.  Let's check:

  m_top / m_tau = 172.69 / 1.77686 = 97.19  (PDG)

  Cascade structure: m_top is at v_cas/sqrt(2), m_tau at d=5 lepton home.
  m_top/m_tau cascade = (v_cas/sqrt(2)) / m_tau = 243.7/1.414/1.776 = 97.0

  This already matches without invoking RG running -- m_top is
  cascade-derived directly from v_cas, not from m_tau by RG.

  m_b / m_top = 4.18 / 172.69 = 0.0242

  Cascade structure: m_b = m_t * m_s/(N_c * m_c) (from (t/b)/(c/s)=N_c)
  Equivalently: m_b/m_top = m_s/(N_c * m_c) = (m_s/m_b)/(N_c * m_c/m_b)
  This is a within-quark-sector ratio, no obvious RG running role.

  m_b / m_c = 4.18 / 1.27 = 3.29  (PDG)

  Cascade: b/s = -alpha(7)/chi^4 = 44.74, so m_b/m_s = 44.74
           c/s × m_s = m_c, so m_b/m_c = (m_b/m_s)/(m_c/m_s) = 44.74/(c/s)
           with cascade c/s = m_c/m_s = (m_top/(N_c·b/s))/(m_b/(b/s))
                              = m_top/(N_c·m_b)
                              = circular if m_b is unknown
           Use PDG m_top, m_b: c/s = 172.69/(3*4.18) = 13.77
           Then m_b/m_c = 44.74/13.77 = 3.25
           PDG m_b/m_c = 3.29
           Match: -1.2%

So various within-quark ratios cascade-derive to standing precision.
The m_b/m_tau cross-sector ratio is the one that requires the running
factor exp(Phi(12))^(4/5).

WHAT WOULD CLOSE THIS
=====================
If the conjecture x = 4/5 = d_obs/d_host is right, m_b would be
cascade-derived as:

  m_b = m_tau * exp(Phi(12))^(4/5)

This requires:
  (a) Cascade-internal proof that x = d_obs/d_host is the structural
      mass-running exponent.  No proof yet; structural reading via
      shell-to-bulk projection is suggestive but not derived.
  (b) Cross-checking against other mass-running observables (e.g.,
      m_c at different scales).
  (c) Verifying that cascade alpha_s running uses x=1 while mass
      running uses x=(d-1)/d -- two distinct cascade RG rules.

Until (a)-(c) are closed, cascade-native RG running is a conjectural
HINT, not a derived mechanism.

CONCLUSION
==========
The cascade ALREADY structurally encodes alpha_s running via Phi
descent (x=1 case).  Extending to mass running with x = 4/5 =
d_observer/d_host MATCHES m_b/m_tau to 0.4% empirically.

This is suggestive but not derived.  Closing m_b cascade-internally
this way requires:
  1. Structural derivation of x = (d-1)/d (the "shell-projection"
     conjecture)
  2. Universal application to other mass-running observables
  3. Reconciliation with QCD's well-tested gamma_m / b_0 structure

If the conjecture holds, m_b at observation = m_tau * exp(Phi(12))^(4/5)
= 4.16 GeV (vs PDG 4.18, dev -0.37%).  This would close m_b cascade-
internally to standing precision via cascade-native RG running.

Status: STRUCTURAL HINT + EMPIRICAL MATCH + OPEN DERIVATION.

If derived, this would be a paper-level result -- cascade-native RG
running unifying alpha_s (descent) with mass running (shell-projected
descent) under a single layer-evolution mechanism.
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

# PDG values
PDG_M_TAU = 1.77686
PDG_M_B = 4.18
PDG_ALPHA_S_MZ = 0.1179


def report_alpha_s_running() -> None:
    print("=" * 88)
    print("STEP 1: cascade structurally encodes alpha_s RG running")
    print("=" * 88)
    print()
    alpha_12 = alpha_cas(12)
    phi_12 = Phi_cascade(12)
    alpha_s_cas = alpha_12 * math.exp(phi_12)
    print(f"  Cascade alpha_s formula:")
    print(f"    alpha_s_cascade = alpha(12) * exp(Phi(12))")
    print(f"                    = {alpha_12:.4f} * {math.exp(phi_12):.4f}")
    print(f"                    = {alpha_s_cas:.4f}")
    print(f"    PDG alpha_s(M_Z) = {PDG_ALPHA_S_MZ}")
    print()
    print(f"  STRUCTURAL READING:")
    print(f"    alpha(12) = 0.040  ~  QCD alpha_s(M_GUT) ~ 0.04")
    print(f"    exp(Phi(12)) = 2.90  ~  QCD running factor GUT->M_Z ~ 2.95")
    print(f"    alpha_s_cascade ~  QCD alpha_s(M_Z)")
    print()
    print(f"  -> Cascade Phi descent IS a structural analog of QCD running.")
    print(f"     The 'running' is the cascade descent through Phi(d).")
    print()


def report_mass_running_attempt() -> None:
    print("=" * 88)
    print("STEP 2: extending Phi descent to mass running")
    print("=" * 88)
    print()
    target_ratio = PDG_M_B / PDG_M_TAU
    phi_12 = Phi_cascade(12)
    x_needed = math.log(target_ratio) / phi_12
    print(f"  Target: m_b/m_tau = {target_ratio:.4f} (PDG)")
    print(f"  Cascade Phi(12) = {phi_12:.4f}, exp(Phi(12)) = {math.exp(phi_12):.4f}")
    print()
    print(f"  Hypothesis: m_b/m_tau = exp(Phi(12))^x")
    print(f"  Required x = log({target_ratio:.4f}) / Phi(12) = {x_needed:.4f}")
    print()
    print(f"  Cascade-natural candidates near {x_needed:.4f}:")
    candidates = [
        ("4/5 = d_observer / d_host = 0.800", 4/5),
        ("(d_host - 1)/d_host = 4/5 = 0.800", 4/5),
        ("(2N_c - 1)/(2pi) = 0.7958", (2*3 - 1)/(2*pi)),
        ("8/9 = 0.8889", 8/9),
        ("ln(N_c)/log_e(e^1) = 1.099/1 = 1.099", math.log(3)),
        ("12/23 (QCD gamma_m/(2 b_0), N_f=5)", 12/23),
        ("1/2 (naive sqrt)", 1/2),
        ("1 (full descent like alpha_s)", 1),
    ]
    print(f"    {'candidate':<48s} {'value':>10s} {'match to x':>12s}")
    print("    " + "-" * 72)
    for name, val in candidates:
        diff_pct = 100 * (val - x_needed) / x_needed
        flag = " <-- BEST" if abs(val - 4/5) < 0.001 else ""
        print(f"    {name:<48s} {val:>10.4f} {diff_pct:>+10.3f}%{flag}")
    print()


def report_cleanest_conjecture() -> None:
    print("=" * 88)
    print("STEP 3: the x = 4/5 conjecture")
    print("=" * 88)
    print()
    phi_12 = Phi_cascade(12)
    cas_ratio = math.exp(phi_12) ** (4/5)
    pdg_ratio = PDG_M_B / PDG_M_TAU
    cas_m_b = PDG_M_TAU * cas_ratio
    print(f"  Conjecture: m_b/m_tau = exp(Phi(12))^(4/5)")
    print(f"            = exp({phi_12:.4f})^(0.8)")
    print(f"            = {cas_ratio:.4f}")
    print()
    print(f"  vs PDG m_b/m_tau = {pdg_ratio:.4f}")
    print(f"  Match: {100*(cas_ratio - pdg_ratio)/pdg_ratio:+.3f}%")
    print()
    print(f"  m_b cascade prediction = m_tau * cascade ratio")
    print(f"                         = {PDG_M_TAU} * {cas_ratio:.4f}")
    print(f"                         = {cas_m_b:.4f} GeV")
    print(f"  vs PDG m_b = {PDG_M_B} GeV")
    print(f"  Match: {100*(cas_m_b - PDG_M_B)/PDG_M_B:+.3f}%  <-- standing precision")
    print()
    print(f"  STRUCTURAL READING of x = 4/5:")
    print(f"    4 = d_observer (3 spatial + 1 time)")
    print(f"    5 = d_host (cascade volume max)")
    print(f"    4/5 = observer/host dimension ratio")
    print(f"        = 'shell-to-bulk' projection at the volume maximum")
    print()
    print(f"  This conjectures TWO distinct cascade RG rules:")
    print(f"    Coupling running:  factor exp(Phi(d))^1 (full descent)")
    print(f"    Mass running:      factor exp(Phi(d))^(4/5) (shell-projected)")
    print()


def report_status() -> None:
    print("=" * 88)
    print("STEP 4: status -- conjectural, not derived")
    print("=" * 88)
    print()
    print("  WHAT IS ESTABLISHED:")
    print()
    print("  (i)  The cascade alpha_s formula structurally encodes alpha_s")
    print("       running.  alpha_s_cascade = alpha(12) * exp(Phi(12)).")
    print("       The factor exp(Phi(12)) ~ 2.90 mirrors the QCD running")
    print("       factor from M_GUT to M_Z.  REAL structural feature.")
    print()
    print("  (ii) Empirically, m_b/m_tau = exp(Phi(12))^(4/5) matches PDG")
    print("       at -0.37% (standing precision).  4/5 = d_obs/d_host is")
    print("       cascade-natural as the shell-to-bulk projection ratio.")
    print()
    print("  WHAT IS NOT ESTABLISHED:")
    print()
    print("  (a) Structural derivation that cascade mass running uses")
    print("      x = (d_host - 1)/d_host = 4/5.  Not yet a theorem; the")
    print("      shell-projection reading is suggestive but unproven.")
    print()
    print("  (b) Universality across other mass-running observables.")
    print("      Tested only against m_b/m_tau; one data point.")
    print()
    print("  (c) Reconciliation with QCD's gamma_m/(2 b_0) = 12/23 = 0.52.")
    print("      Cascade x = 4/5 = 0.80 is LARGER, predicting stronger")
    print("      mass running than standard QCD.  Either cascade differs")
    print("      from QCD here (a falsifiable cascade prediction) or there")
    print("      are corrections that bring them into agreement.")
    print()
    print("  (d) Why coupling and mass run with DIFFERENT cascade exponents")
    print("      (x=1 vs x=4/5).  Cascade-internal source of this")
    print("      asymmetry not yet identified.")
    print()
    print("  IMPLICATION IF DERIVED:")
    print()
    print("    m_b cascade-internal = m_tau * exp(Phi(12))^(4/5)")
    print("                         = 4.16 GeV (PDG 4.18, dev -0.37%)")
    print()
    print("    Closes m_b without external RG infrastructure.  Closes the")
    print("    quark hierarchy in pure cascade primitives + cascade-native")
    print("    RG running.  Paper-level result if derivation succeeds.")
    print()


def main() -> int:
    print("=" * 88)
    print("CASCADE-NATIVE RG RUNNING: structural hints and conjectures")
    print("Question: can cascade derive RG running from its layer structure?")
    print("=" * 88)
    print()
    report_alpha_s_running()
    report_mass_running_attempt()
    report_cleanest_conjecture()
    report_status()
    print("=" * 88)
    print("HEADLINE:")
    print()
    print("  The cascade STRUCTURALLY encodes alpha_s RG running via Phi descent:")
    print("    alpha_s_cascade = alpha(12) * exp(Phi(12)) ~  alpha_s(M_Z)")
    print()
    print("  Empirically, the same descent generator with exponent 4/5 closes")
    print("  m_b/m_tau:")
    print("    m_b/m_tau = exp(Phi(12))^(4/5) = 2.34, vs PDG 2.35, match -0.4%")
    print()
    print("  4/5 = d_observer/d_host = 'shell-to-bulk' projection ratio.")
    print("  Cascade-natural but not yet derived structurally.")
    print()
    print("  IF DERIVED: m_b cascade-internal = 4.16 GeV (-0.37%), closing the")
    print("  quark hierarchy in pure cascade primitives + cascade-native RG")
    print("  running.")
    print()
    print("  Status: STRUCTURAL HINT + EMPIRICAL MATCH (one observable) +")
    print("  OPEN DERIVATION.  Research-level next step.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
