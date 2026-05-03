#!/usr/bin/env python3
"""
Option C: derive m_b cascade-internally?  Investigation result: NOT TRACTABLE
with current cascade infrastructure.  Identifies the structural obstacle.

GOAL
====
Replace m_b as the only quark-side anchor with a cascade-derived value.
Test the bundle reading at d=12 (SU(3) home) plus Dirac amplification.
Expected (per earlier framing): cascade-derived m_b should have ~1.6%
residual from PDG (the bundle/scalar gap signature).

RESULT
======
The hypothesis fails at the structural level.  The cascade does NOT
have a clean d=12-based fermion mass formula analogous to the SU(2)
volume formula s/d = Omega_4.  The structural obstacle is identified
below.

INVESTIGATIONS PERFORMED
========================

1. LEPTON TEMPLATE AT d=12 with various Dirac amp counts:
     n_D=0: m_b = 1.94 GeV  (residual -53.5%)
     n_D=1: m_b = 0.55 GeV  (residual -86.9%)
     n_D=2: m_b = 0.15 GeV  (residual -96.3%)
   None match.  Lepton template at d=12 fails by factor 2-100x.

2. CROSS-SECTOR RATIO m_b / m_tau via cascade-natural factors:
     m_b/m_tau target = 2.354 (PDG)
     Candidates tested: N_c, N_c·(1-delta_BS), sqrt(3), sqrt(2pi),
                       pi^2/4, vol(SU(3))/vol(SU(2)) variants, etc.
     Best match: sqrt(2pi) = 2.507 (off +6.5%)
                 pi^2/4 = 2.467 (off +4.9%)
     No clean cascade-natural match.

3. CHANNEL-COUNT RULE alpha(d*)/chi^k for m_b/m_tau closure:
     log(m_b/m_tau / N_c) = log(0.785) = -0.243
     Need alpha(d*)/chi^k ~ 0.243 to close.
     Available cascade alpha(d*)/chi^k values: 0.004 to 0.045.
     CAN'T REACH 0.243 -- channel-count rule is too small a correction.

4. GUT-SCALE GEORGI-JARLSKOG with RG running:
     At M_GUT: m_b ~ m_tau (SU(5) GJ, NOT cascade-native)
     RG running brings down to observation scale by factor 2.35.
     Cascade does NOT have RG running infrastructure.
     This route requires SU(5) GJ + RG (both external to cascade).

STRUCTURAL OBSTACLE
===================

The cascade has clean bundle readings at d=13 (SU(2) home):

  s/d = vol(SU(2)) = Omega_4 = 2*pi^2  (-1.3% match)

This works because SU(2) is diffeomorphic to S^3 (the unit quaternions),
so vol(SU(2)) = surface area Omega_4 is a direct cascade primitive.

For SU(3) at d=12, the analog FAILS because:

  (a) SU(3) is 8-dimensional and NOT a sphere.  vol(SU(3)) = sqrt(3)·pi^5
      in standard bi-invariant normalization, not a simple Omega_d.

  (b) d=12 is NOT a fermion home.  Cascade fermion homes are at residue 5
      mod 8: d=5, 13, 21, 29.  m_b is at d=5 (Gen 3 fermion home) with
      SU(3) bundle structure on top, not at d=12 directly.

  (c) The cascade primitives at d=12 (alpha(12), R(12), Phi(12)) don't
      cleanly compose into a cross-sector mass formula for m_b/m_tau at
      observation scale.

  (d) Cross-sector m_b/m_tau at observation scale involves QCD RG running
      from GUT (where m_b ~ m_tau) to observation (where m_b ~ 2.35 m_tau).
      This running is not cascade-internal -- it's standard QCD physics
      that the cascade currently doesn't reproduce.

The asymmetry SU(2)≅S^3 vs SU(3)≇S^anything creates the difficulty.
For SU(2), the bundle reading factors cleanly into a single sphere area.
For SU(3), the bundle structure has 8 dimensions of orbit and no clean
single-Omega match.

WHAT THIS MEANS FOR THE QUARK HIERARCHY
=======================================

The current cascade quark hierarchy:
  - m_b: empirical anchor (input)
  - m_s = m_b / (b/s)
  - m_d = m_s / vol(SU(2))
  - m_top = v_cas / sqrt(2)  (cross-sector via cascade VEV + SM y_top=1)
  - m_c = m_top / (N_c · b/s)
  - m_u = m_c / (6·pi^4)

The "bundle reading" as a unifying principle works at d=13 (SU(2)) but
NOT at d=12 (SU(3)).  This is a STRUCTURAL ASYMMETRY in the cascade,
not a flaw -- it reflects the geometric fact that SU(2) is a sphere and
SU(3) isn't.

The quark hierarchy needs ONE empirical anchor (m_b currently), AND that
anchor relates to the cross-sector lepton mass via QCD running which is
external to the cascade.  This is HONEST FRAMING:

  - Lepton sector: derived cascade-internally from descent + Dirac
  - Down-quark sector: requires m_b anchor, then bundle reading at d=13
    gives s/d
  - Up-quark sector: derived from cascade VEV + SM y_top=1
  - SU(3) bundle structure: NOT cascade-internally simple at d=12

POSSIBLE WAYS FORWARD (not pursued in this script)
===================================================

(a) RG running infrastructure: implement QCD running of m_b cascade-
    internally.  This is significant new infrastructure but standard
    physics.  Would close m_b in cascade × external RG framework.

(b) New cascade structural relation: identify a cascade-native
    cross-sector mass relation that bypasses RG running.  No obvious
    candidate; would require new structural insight.

(c) Accept m_b as the cascade's structural anchor: just as the cascade
    accepts G_Newton (M_Pl,red) as input, the cascade could explicitly
    accept m_b as the "down-quark scale" input.  This makes the cascade
    have ONE quark-side empirical input (parallel to the cosmological
    constant input), not zero.

Reading (c) is most honest given current cascade structure.  It puts the
cascade at "zero free parameters except for the m_b anchor for the
quark sector" rather than fully zero.  Comparable to "v_EW residual at
-1% post-Gram" -- the cascade has standing-precision predictions and
some open structural pieces.

CONCLUSION
==========
Option C as originally framed is NOT a quick test.  The cascade does
not have a clean structural mechanism to derive m_b at observation
scale without external RG running.

This is informative: it identifies the SU(3) bundle as the cascade's
structurally weakest gauge-home, and points to QCD running as an
external piece the cascade currently doesn't reproduce.

The "complete the quark hierarchy in pure cascade primitives" framing
oversold the tractability.  Honest current status: 5 of 6 quark masses
follow from cascade primitives + 1 anchor (m_b).  Closing m_b requires
genuinely new infrastructure or structural insight.
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
PDG_M_B = 4.18
PDG_M_TAU = 1.77686
PDG_M_TOP = 172.69
TARGET_RATIO = PDG_M_B / PDG_M_TAU  # 2.3525

# Cascade primitives
ALPHA_S_LEAD = 0.1159
V_CAS = 243.7  # Gram-corrected
TWO_SQRT_PI = 2 * math.sqrt(pi)
N_C = 3


def report_target() -> None:
    print("=" * 88)
    print("STEP 1: target -- derive m_b cascade-internally")
    print("=" * 88)
    print()
    cas_m_tau = (
        ALPHA_S_LEAD * V_CAS / math.sqrt(2)
        * math.exp(-Phi_cascade(5))
        * TWO_SQRT_PI ** (-2)
    )
    print(f"  PDG m_b              = {PDG_M_B} GeV")
    print(f"  PDG m_tau            = {PDG_M_TAU} GeV")
    print(f"  m_b/m_tau (target)   = {TARGET_RATIO:.4f}")
    print()
    print(f"  Cascade m_tau (d=5)  = {cas_m_tau:.4f} GeV  (residual {100*(cas_m_tau-PDG_M_TAU)/PDG_M_TAU:+.3f}%)")
    print()


def report_d12_lepton_template() -> None:
    print("=" * 88)
    print("STEP 2: lepton template at d=12 (SU(3) home)")
    print("=" * 88)
    print()
    prefactor = ALPHA_S_LEAD * V_CAS / math.sqrt(2)
    exp_phi12 = math.exp(-Phi_cascade(12))
    print(f"  prefactor = (alpha_s · v / sqrt(2)) = {prefactor:.4f}")
    print(f"  exp(-Phi(12))                       = {exp_phi12:.4f}")
    print()
    print(f"  {'n_D':>4s} {'m_b candidate':>15s} {'residual':>12s} {'ratio to PDG':>14s}")
    for n_D in range(0, 4):
        topo = TWO_SQRT_PI ** (-(n_D + 1))
        m_b = prefactor * exp_phi12 * topo
        resid = 100 * (m_b - PDG_M_B) / PDG_M_B
        ratio = m_b / PDG_M_B
        print(f"  {n_D:>4d} {m_b:>13.4f} GeV {resid:>+11.2f}% {ratio:>13.3f}x")
    print()
    print("  NONE match.  d=12 lepton template fails by 2-100x.")
    print()


def report_cross_sector_factors() -> None:
    print("=" * 88)
    print("STEP 3: m_b = m_tau * bundle-factor candidates")
    print("=" * 88)
    print()
    print(f"  Target factor m_b/m_tau = {TARGET_RATIO:.4f}")
    print()
    candidates = [
        ("N_c = 3", 3.0),
        ("N_c · (1 - delta_BS)", 3.0 * (1 - 0.0166)),
        ("sqrt(N_c)", math.sqrt(3)),
        ("N_c · (2/pi)", 3 * (2 / pi)),
        ("sqrt(2*pi)", math.sqrt(2 * pi)),
        ("pi^2 / 4", pi ** 2 / 4),
        ("Omega_8/Omega_4 = pi^2/6", pi ** 2 / 6),
        ("vol(SU(3))/vol(SU(2)) = sqrt(3)*pi^3", math.sqrt(3) * pi ** 3),
    ]
    print(f"  {'candidate':<40s} {'value':>10s}  {'ratio to target':>15s}")
    print("  " + "-" * 70)
    for name, val in candidates:
        ratio = val / TARGET_RATIO
        print(f"  {name:<40s} {val:>10.4f}  {ratio:>15.4f}")
    print()
    print("  No clean cascade-natural match.  Closest: sqrt(2*pi) +6.5% off,")
    print("  pi^2/4 +4.9% off.  None at standing precision.")
    print()


def report_channel_count_rule() -> None:
    print("=" * 88)
    print("STEP 4: channel-count rule m_b/m_tau = N_c · exp(-alpha(d*)/chi^k)?")
    print("=" * 88)
    print()
    needed = math.log(TARGET_RATIO / N_C)
    print(f"  log(m_b/m_tau / N_c) = log({TARGET_RATIO/N_C:.4f}) = {needed:+.4f}")
    print(f"  Need alpha(d*)/chi^k ~ {-needed:.4f} to close.")
    print()
    candidates = [
        ("alpha(5)/chi^3", alpha_cas(5) / 8),
        ("alpha(7)/chi^2", alpha_cas(7) / 4),
        ("alpha(14)/chi", alpha_cas(14) / 2),
        ("alpha(19)/chi", alpha_cas(19) / 2),
        ("alpha(7)/chi^4", alpha_cas(7) / 16),
        ("alpha(12)/chi", alpha_cas(12) / 2),
        ("alpha(5)/chi", alpha_cas(5) / 2),
    ]
    print(f"  Available alpha(d*)/chi^k:")
    for name, val in candidates:
        print(f"    {name:<22s} {val:+.6f}")
    print()
    print(f"  All values < 0.05.  CAN'T REACH {-needed:.4f}.")
    print(f"  Channel-count rule (mechanism 2) is too small for m_b/m_tau.")
    print()


def report_obstacle() -> None:
    print("=" * 88)
    print("STEP 5: structural obstacle")
    print("=" * 88)
    print()
    print("  The cascade has clean SU(2) bundle reading at d=13:")
    print()
    print("    s/d = vol(SU(2)) = Omega_4 = 2*pi^2  (-1.3% match)")
    print()
    print("  This works because SU(2) ≅ S^3 -- vol(SU(2)) = sphere area Omega_4")
    print("  is a direct cascade primitive.")
    print()
    print("  The analog at d=12 (SU(3) home) FAILS because:")
    print()
    print("  (a) SU(3) is 8-dim and NOT a sphere.  vol(SU(3)) = sqrt(3)*pi^5")
    print("      in standard normalization, not a simple cascade Omega_d.")
    print()
    print("  (b) d=12 is NOT a fermion home.  Fermion homes at d=5,13,21,29")
    print("      by Bott periodicity (residue 5 mod 8).  m_b is at d=5")
    print("      (Gen 3 home) with SU(3) bundle structure on top, not at")
    print("      d=12 directly.")
    print()
    print("  (c) Cross-sector m_b/m_tau at observation scale involves QCD RG")
    print("      running, which is NOT cascade-internal.  At GUT scale GJ")
    print("      gives m_b ~ m_tau, but cascade doesn't run from GUT to obs.")
    print()
    print("  (d) The cascade's three correction mechanisms (Gram, chi^k,")
    print("      gauge-bundle) all give corrections at most ~5%.  m_b/m_tau")
    print("      needs ~135% correction (factor 2.35x).  Out of mechanism")
    print("      reach.")
    print()
    print("  STRUCTURAL ASYMMETRY: SU(2) ≅ S^3 makes its bundle reading clean.")
    print("  SU(3) ≇ S^anything makes its bundle reading non-trivial.  This is")
    print("  geometric fact, not a cascade flaw -- but it limits what cascade")
    print("  can derive cleanly at the SU(3) gauge home.")
    print()


def report_status() -> None:
    print("=" * 88)
    print("STEP 6: revised status")
    print("=" * 88)
    print()
    print("  Option C result: NOT a quick test.  Cascade m_b cannot be")
    print("  derived cascade-internally at observation scale via the simple")
    print("  bundle-reading approach analogous to s/d = Omega_4.")
    print()
    print("  Honest current status of cascade quark hierarchy:")
    print()
    print("    - 5 of 6 quark masses derive from cascade primitives + m_b anchor")
    print("    - m_b: empirical anchor (only quark-side input)")
    print("    - The 'pure cascade primitives' framing requires either:")
    print("      (a) RG running infrastructure (significant)")
    print("      (b) New cascade-native cross-sector relation (no candidate yet)")
    print("      (c) Accepting m_b as cascade's quark-sector input")
    print()
    print("  Comparable scope to other cascade open items:")
    print("    - v_EW: closed at standing precision via Gram, not experimental")
    print("    - PMNS / lighter neutrinos: open structural mechanism")
    print("    - Omega_b derivation: weakest cascade derivation, needs strengthening")
    print()
    print("  m_b joins these as a 'standing-precision open item' rather than")
    print("  a 'closed at experimental precision' result.")
    print()


def main() -> int:
    print("=" * 88)
    print("OPTION C: cascade-internal m_b derivation -- INVESTIGATION RESULT")
    print("Hypothesis: m_b can be derived from bundle reading at d=12 + Dirac amp")
    print("Result:     NOT a quick test.  Identified structural obstacle.")
    print("=" * 88)
    print()
    report_target()
    report_d12_lepton_template()
    report_cross_sector_factors()
    report_channel_count_rule()
    report_obstacle()
    report_status()
    print("=" * 88)
    print("HEADLINE:")
    print()
    print("  Option C as framed is NOT tractable.  Cascade does not have a")
    print("  clean d=12-based fermion mass formula analogous to s/d=Omega_4.")
    print()
    print("  Structural obstacle: SU(2) ≅ S^3 (clean), SU(3) ≇ sphere (not")
    print("  clean).  Plus d=12 isn't a fermion home (residue 5 mod 8 is).")
    print("  Plus cross-sector m_b/m_tau at observation needs RG running.")
    print()
    print("  Three correction mechanisms can give ~5% at most; m_b/m_tau needs")
    print("  ~135% correction (factor 2.35).  Out of mechanism reach.")
    print()
    print("  m_b remains the cascade's quark-sector anchor.  Closing it requires")
    print("  RG running infrastructure or a NEW cascade-native cross-sector")
    print("  relation.  This is research-level work, not a quick verification.")
    print()
    print("  Updated honest framing: 5 of 6 quark masses cascade-derived;")
    print("  m_b at standing-precision-open status, comparable to v_EW.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
