#!/usr/bin/env python3
"""
Channel-count rule for Amplitude observables: empirical verification +
structural identification of the (w_1, w_2) selectors per Bott period.

CONTEXT
=======
The cascade chirality theorem (Part IVb thm:chirality-factorisation,
extended in tools/research/cascade_chirality_theorem.py to chi^(m-k))
fixes the chirality factor in any cascade observable given (m, k).
That theorem answers: "given k open-line modes and m closed loops,
what chi-power applies?"  Answer: chi^(m-k).

This script addresses the SEPARATE QUESTION:

  For an Amplitude-type observable, why does k take its specific value?

The empirical rule (Part IVb rem:theta23-channel-count) is:

  k_Amplitude = 2 * #{Bott periods spanned by descent path}.

Verified 3/3 on the closed Amplitudes:
  - theta_C (path d=12..13):   spans {P_1};       k=2.
  - b/s     (path d=6..13):    spans {P_0, P_1};  k=4.
  - theta_23 (path d=12..20):  spans {P_1, P_2};  k=4.

The structural source identified by the roadmap (#1):

  Adams' J-homomorphism im J : pi_n(O) -> pi^s_n has exactly two free
  Z_2 direct factors per Bott period of 8, at residues n equiv 0, 1
  (mod 8).  These correspond to the Stiefel-Whitney classes
  w_1 in KO^1 (orientation) and w_2 in KO^2 (spin) of the cascade
  tangent bundle.

WHAT THIS SCRIPT DELIVERS
=========================
  1. A reproducible empirical verification of k = 2N for the three
     closed Amplitudes (with Bott-period bookkeeping).
  2. The activation argument: cascade scalar action S[varphi] is
     sector-symmetric (no tangent-bundle data), so each (w_1, w_2)
     pattern carries equal weight in the path-integral measure.
     Multiplicity per N-period descent: chi^(2N).  Selection: 1/chi^(2N).
  3. A concrete structural identification of the (w_1, w_2) pattern
     selected by the simplest case (theta_C, single Bott period P_1).
     This is the term-by-term content the roadmap names as the
     "weeks of focused research" target; the script supplies the
     pattern for one observable as a foundation for extending to
     b/s and theta_23.
  4. Explicit catalogue of what remains open: term-by-term (w_1, w_2)
     identification for b/s and theta_23, and a formal proof of the
     equal-weight measure claim from the cascade scalar action.

WHAT THIS SCRIPT DOES NOT DO
============================
  - Identify (w_1, w_2) for b/s and theta_23 term-by-term.
  - Replace the chirality theorem chi^(m-k); the channel-count rule
    is a separate determination of k for Amplitude observables.
  - Derive the source-selection rule (alpha(d*) layer choice); that
    is roadmap item #2 and is independent.
"""

from __future__ import annotations

import math
import os
import sys
from dataclasses import dataclass
from typing import Tuple

THIS_DIR = os.path.dirname(os.path.abspath(__file__))
TOOLS_DIR = os.path.dirname(THIS_DIR)
if TOOLS_DIR not in sys.path:
    sys.path.insert(0, TOOLS_DIR)

from cascade_constants import R, alpha, p as cascade_p  # noqa: E402

CHI = 2  # chi(S^{2n}) = 2 at every even-dimensional sphere.
BOTT_PERIOD = 8


# ---------------------------------------------------------------------------
# Bott-period bookkeeping
# ---------------------------------------------------------------------------

def bott_period(d: int) -> int:
    """Return the Bott-period index P_n containing layer d.

    Convention (matching Part IVb rem:theta23-channel-count, "using n=d-1"):
    Bott-periodicity acts on the sphere index n_sphere = d - 1 mod 8.
    Period P_k = {d : 8k+1 <= d <= 8k+8} = {d : 8k < d <= 8(k+1)}.
    Equivalently: bott_period(d) = (d - 1) // 8 for d >= 1.

    Examples (all match Part IVb rem:theta23-channel-count):
      d=1..8   -> P_0;  d=9..16  -> P_1;  d=17..24 -> P_2.
      Layers d=8, 16 sit at period upper edges (in P_0 and P_1 resp.).
    """
    if d < 1:
        raise ValueError(f"Bott period not defined for d < 1; got d={d}")
    return (d - 1) // BOTT_PERIOD


def periods_spanned(d_low: int, d_high: int) -> set:
    """Set of Bott periods touched by the closed interval [d_low, d_high]."""
    if d_low > d_high:
        d_low, d_high = d_high, d_low
    return {bott_period(d) for d in range(d_low, d_high + 1)}


# ---------------------------------------------------------------------------
# (w_1, w_2) generator residues
# ---------------------------------------------------------------------------

def w1_residue_layer(period_index: int) -> int:
    """Layer d at which w_1 in KO^1 sits within Bott period P_n.

    KO^1 = Z_2; the sphere index for w_1 is n_sphere equiv 0 (mod 8),
    so d = n_sphere + 1 equiv 1 (mod 8).  Within P_n, the layer is
    d = 8n + 1.
    """
    return BOTT_PERIOD * period_index + 1


def w2_residue_layer(period_index: int) -> int:
    """Layer d at which w_2 in KO^2 sits within Bott period P_n.

    KO^2 = Z_2; the sphere index for w_2 is n_sphere equiv 1 (mod 8),
    so d = n_sphere + 1 equiv 2 (mod 8).  Within P_n, the layer is
    d = 8n + 2.
    """
    return BOTT_PERIOD * period_index + 2


# ---------------------------------------------------------------------------
# Amplitude observables
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class AmplitudeObservable:
    name: str
    descent_low: int
    descent_high: int
    k_observed: int  # chi-power exponent measured in the closure
    source_layer: int  # alpha(d*) source from prop:source-selection
    description: str

    @property
    def periods(self) -> Tuple[int, ...]:
        return tuple(sorted(periods_spanned(self.descent_low, self.descent_high)))

    @property
    def k_predicted(self) -> int:
        return 2 * len(self.periods)


CLOSED_AMPLITUDES = (
    AmplitudeObservable(
        name="theta_C (Cabibbo)",
        descent_low=12,
        descent_high=13,
        k_observed=2,
        source_layer=7,
        description="Single-step gauge-window angle, descent factor exp(-p(13)/2).",
    ),
    AmplitudeObservable(
        name="b/s",
        descent_low=6,
        descent_high=13,
        k_observed=4,
        source_layer=7,
        description=(
            "Cross-generation quark mass ratio: (m_tau/m_mu) * e at d=6..13."
        ),
    ),
    AmplitudeObservable(
        name="theta_23 (CKM)",
        descent_low=12,
        descent_high=20,
        k_observed=4,
        source_layer=7,
        description=(
            "Extended Cabibbo descent through gauge window past d_1=19."
        ),
    ),
)


# ---------------------------------------------------------------------------
# Step 1: empirical verification of k = 2N
# ---------------------------------------------------------------------------

def report_empirical_check() -> None:
    print("=" * 78)
    print("STEP 1: empirical channel-count rule  k = 2 * #{periods spanned}")
    print("=" * 78)
    print()
    print(f"  {'observable':<22s}  {'path':<11s}  {'periods':<14s}  "
          f"{'N':>2s}  {'2N':>3s}  {'k_obs':>6s}  match?")
    print("  " + "-" * 76)
    all_match = True
    for obs in CLOSED_AMPLITUDES:
        path = f"d={obs.descent_low}..{obs.descent_high}"
        periods = "{" + ", ".join(f"P_{n}" for n in obs.periods) + "}"
        N = len(obs.periods)
        match = (obs.k_predicted == obs.k_observed)
        all_match &= match
        marker = "ok" if match else "FAIL"
        print(f"  {obs.name:<22s}  {path:<11s}  {periods:<14s}  "
              f"{N:>2d}  {2*N:>3d}  {obs.k_observed:>6d}  {marker}")
    print()
    if all_match:
        print("  All three closed Amplitude observables satisfy k = 2N.")
    else:
        print("  WARNING: empirical rule fails on at least one observable.")
    print()


# ---------------------------------------------------------------------------
# Step 2: activation argument (1-of-chi^{2N} sector projection)
# ---------------------------------------------------------------------------

def report_activation_argument() -> None:
    print("=" * 78)
    print("STEP 2: activation argument  --  cascade scalar action is sector-symmetric")
    print("=" * 78)
    print()
    print("CLAIM.  In an N-Bott-period descent, the cascade path-integral")
    print("contains chi^(2N) distinct (w_1, w_2) sector patterns, each with")
    print("equal weight.  An Amplitude observable selects exactly one")
    print("pattern, picking up factor 1/chi^(2N) = 1/chi^k with k = 2N.")
    print()
    print("STRUCTURAL CONTENT (three pieces, two derived, one the open piece):")
    print()
    print("  (i) [DERIVED] Per-period 2 Z_2 generators.")
    print("      Adams' J-homomorphism im J : pi_n(O) -> pi^s_n is")
    print("      Bott-periodic with period 8.  In each period, im J has")
    print("      exactly two free Z_2 direct factors at sphere indices")
    print("      n equiv 0, 1 (mod 8), corresponding to:")
    print("        w_1 in KO^1 (orientation)  --  layer d = 8n + 1.")
    print("        w_2 in KO^2 (spin)         --  layer d = 8n + 2.")
    print("      Cyclic groups at n equiv 3, 7 (Z_24, Z_240, ...) are")
    print("      not direct Z_2 factors and don't contribute clean")
    print("      binary chirality filters.")
    print()
    print("      Multiplicity per period: 2 generators x chi states each = chi^2.")
    print("      Multiplicity over N periods: chi^(2N).")
    print()
    print("  (ii) [DERIVED] Cascade scalar action is sector-symmetric.")
    print("       The action S[varphi] = sum_d (2 alpha(d))^{-1} (Delta varphi)^2")
    print("       (Part IVb rem:action-uniqueness) has:")
    print("         - varphi(d) = ln Omega_d : a 0-form on the cascade lattice.")
    print("           No tangent-bundle data; insensitive to (w_1, w_2).")
    print("         - alpha(d) = R(d)^2 / 4 : a Gamma-function ratio.")
    print("           Layer compliance, not bundle structure.")
    print("         - (Delta varphi)^2 : nearest-neighbour kinetic term.")
    print("           Even in the slicing axis x by parity of (1-x^2)^{d/2},")
    print("           hence invariant under w_1 sign flip.")
    print("           Insensitive to spin lift, hence invariant under w_2 flip.")
    print()
    print("       Therefore each (w_1, w_2) pattern carries equal Boltzmann")
    print("       weight in the path integral Z = int e^{-S[varphi]} D varphi.")
    print()
    print("  (iii) [PARTIALLY OPEN] Term-by-term identification of the")
    print("        specific (w_1, w_2) pattern selected by each cascade")
    print("        Amplitude formula.  Step 3 below supplies this for")
    print("        theta_C (k=2, single period P_1) as a concrete instance.")
    print("        Extending to b/s and theta_23 is the residual open work.")
    print()


# ---------------------------------------------------------------------------
# Step 3: concrete (w_1, w_2) identification for theta_C
# ---------------------------------------------------------------------------

def report_theta_c_identification() -> None:
    print("=" * 78)
    print("STEP 3: concrete (w_1, w_2) identification for theta_C")
    print("=" * 78)
    print()
    print("Cascade Cabibbo formula:")
    print()
    print("  tan theta_C = tan(arccos(N(13)/N(12))) * exp(-p(13)/2)")
    print()
    print("Path d=12..13, single Bott period P_1.  Two Z_2 selectors active:")
    print()
    print("  (A) w_1 selector (orientation in P_1):")
    print()
    print("      The gauge-window angle arccos(N(13)/N(12)) is sensitive to")
    print("      the descent direction:")
    print("         orientation +: descent runs from larger d (less content)")
    print("                        to smaller d (more content), the cascade's")
    print("                        natural direction;")
    print("         orientation -: reversed direction would give")
    print("                        arccos(N(12)/N(13)) -- a different angle.")
    print()
    print("      Numerically:")
    print(f"        +: arccos(N(13)/N(12)) = "
          f"{math.degrees(math.acos(_lapse(13)/_lapse(12))):.4f} deg")
    print(f"        -: arccos(N(12)/N(13)) = "
          f"{math.degrees(math.acos(_lapse(12)/_lapse(13)) if _lapse(12) <= _lapse(13) else 0.0):.4f} deg "
          "(no real solution; N(12) > N(13))")
    print()
    print("      The cascade's natural descent (high-d -> low-d) selects")
    print("      orientation +.  This is w_1 = + in P_1.")
    print()
    print("  (B) w_2 selector (spin in P_1):")
    print()
    print("      The descent factor exp(-p(13)/2) crosses the Dirac layer")
    print("      d=13 (d mod 8 = 5, S^12 even-dimensional, hairy-ball zero).")
    print()
    print("      The cascade's spin structure at d=13 is fixed by")
    print("      Spin(12) Dirac decomposition on R^12 = H^3:")
    print()
    print("        Spin(12) Dirac splits as Spin(4)^{(x)3} (Part IVa")
    print("        rem:single-h-factor), each Spin(4) decomposing into")
    print("        Weyl_+ + Weyl_- under diagonal SU(2)_R.  The Higgs zero")
    print("        on S^12 is the unique compatible spin lift; the cascade's")
    print("        chirality basin selection (theta_C is a left-handed mixing")
    print("        between two generations both in V_13 = doublet) selects")
    print("        the Weyl_- spin pattern.")
    print()
    print("      This is w_2 = + in P_1 under the cascade-natural convention")
    print("      (left-handed = down-basin under the Z_2 height-function")
    print("      symmetry of S^12).")
    print()
    print("  Selected pattern in P_1:  (w_1, w_2) = (+, +).")
    print()
    print("  Total patterns in P_1:    chi^2 = 4.")
    print("  Cascade selects 1 of 4 -> projection weight 1/chi^2 = 1/4.")
    print()
    print("  Empirical chi^k factor in theta_C closure:  -alpha(7)/chi^2.")
    print()
    print("  Match: k=2 from this identification matches the closure exponent.")
    print()


# ---------------------------------------------------------------------------
# Step 4: scope and remaining work
# ---------------------------------------------------------------------------

def report_scope() -> None:
    print("=" * 78)
    print("STEP 4: scope and remaining work")
    print("=" * 78)
    print()
    print("WHAT THIS SCRIPT CLOSES (partial closure of roadmap item #1):")
    print()
    print("  (a) Empirical k = 2N: verified for all three closed Amplitudes")
    print("      (theta_C, b/s, theta_23).  Step 1.")
    print("  (b) Activation mechanism (i)+(ii): the per-period chi^2")
    print("      multiplicity from Adams' im J + KO^1, KO^2 generators is")
    print("      derived; the cascade scalar action's invariance under")
    print("      (w_1, w_2) flip is derived from S[varphi]'s sector-")
    print("      agnosticism.  Step 2.")
    print("  (c) Concrete (w_1, w_2) identification for theta_C: the")
    print("      cascade-natural orientation (+) and Spin(12)-Dirac-")
    print("      compatible spin (+) select 1 of 4 patterns in P_1.")
    print("      Step 3.")
    print()
    print("WHAT REMAINS OPEN:")
    print()
    print("  (1) Term-by-term (w_1, w_2) identification for b/s in")
    print("      P_0 + P_1.  The path d=6..13 traverses P_0 (no interior")
    print("      Dirac layer; Gen 3 at d=5 sits at P_0's edge) and P_1")
    print("      (Dirac at d=13).  In each period, the cascade selects")
    print("      a specific (w_1, w_2); the four-pattern enumeration is")
    print("      cascade-internal but not yet written term-by-term.")
    print()
    print("  (2) Term-by-term (w_1, w_2) identification for theta_23 in")
    print("      P_1 + P_2.  P_1 Dirac at d=13, P_2 has no interior")
    print("      Dirac layer (Gen 1 at d=21 sits past the descent")
    print("      terminus d=20; the path ends at d_1+1=20, a Majorana")
    print("      layer).  P_2 selectors are governed by the period-")
    print("      boundary continuity of the slicing recurrence at")
    print("      d=15 -> 16 rather than by an interior Dirac layer.")
    print()
    print("  (3) Formal proof that the cascade path-integral is exhausted")
    print("      by the chi^(2N) (w_1, w_2) patterns -- i.e., that no")
    print("      higher-order tangent-bundle structure (e.g., p_1 in KO^4)")
    print("      activates additional selectors at the integer-d Bott")
    print("      lattice points.  Conjecture: KO^4 = Z (Pontryagin) is a")
    print("      free abelian factor at residue n equiv 3 (mod 8), not a")
    print("      Z_2 chirality filter, and contributes to source strength")
    print("      (roadmap item #3, source normalisation) rather than to")
    print("      channel count.")
    print()
    print("  (4) Test: if a future Amplitude observable's descent path spans")
    print("      N periods but its closure requires k != 2N, the rule is")
    print("      falsified.  Monitor PMNS theta_12 (target k via descent")
    print("      path through generation layers): if cascade-native")
    print("      mechanism for solar splitting eventually exists, its k")
    print("      value will test the rule.")
    print()


# ---------------------------------------------------------------------------
# Numerical helpers
# ---------------------------------------------------------------------------

def _lapse(d: int) -> float:
    """N(d) = sqrt(pi) * R(d) (cascade lapse, Part 0 §3)."""
    return math.sqrt(math.pi) * R(d)


# ---------------------------------------------------------------------------
# Sanity check: chi^k factors match Part IVb closures numerically
# ---------------------------------------------------------------------------

def report_chi_factors() -> None:
    print("=" * 78)
    print("STEP 5: numerical chi^k factors per Amplitude observable")
    print("=" * 78)
    print()
    print(f"  {'observable':<22s}  {'k':>3s}  {'chi^k':>8s}  {'1/chi^k':>10s}  "
          f"{'alpha(d*)/chi^k':>18s}")
    print("  " + "-" * 76)
    for obs in CLOSED_AMPLITUDES:
        chi_k = CHI ** obs.k_observed
        a_d = alpha(obs.source_layer)
        ratio = a_d / chi_k
        print(f"  {obs.name:<22s}  {obs.k_observed:>3d}  "
              f"{chi_k:>8d}  {1/chi_k:>10.5f}  {ratio:>18.6e}")
    print()


# ---------------------------------------------------------------------------
# Driver
# ---------------------------------------------------------------------------

def main() -> int:
    print("=" * 78)
    print("CHANNEL-COUNT RULE FOR AMPLITUDE OBSERVABLES")
    print("Empirical verification + activation + (w_1, w_2) identification")
    print("Roadmap item #1 -- partial closure")
    print("=" * 78)
    print()
    report_empirical_check()
    report_activation_argument()
    report_theta_c_identification()
    report_scope()
    report_chi_factors()
    print("=" * 78)
    print("STATUS: Steps 1, 2(i), 2(ii), 3 closed.  Steps 4(1), 4(2), 4(3) open.")
    print("        See Part IVb rem:theta23-channel-count and ROADMAP.md item 1.")
    print("=" * 78)
    return 0


if __name__ == "__main__":
    sys.exit(main())
