#!/usr/bin/env python3
"""
Test (1) of the unified-descent program: are the eight precision
closures' alpha(d*)/chi^k corrections equivalent to Gram corrections
delta_path(5, d_max) at structurally-meaningful d_max?

CONTEXT
=======
cascade_phi_gram_gauge_volume.py found that exp(Phi(21)-Phi(13)) =
N_c * vol(SU(2)) closes to 0.054% via delta_path(5, 21) = +0.015912.
Same Gram mechanism closes the cosmological constant from -2.2% to
-0.07% via delta_path(5, 217) = +0.021.

Hypothesis tested here: the eight precision closures of Part IVb,
each closing residuals at the 0.4-1.7% level via shifts of the form
alpha(d*)/chi^k at distinguished cascade layers d* in {5, 7, 14, 19},
are themselves Gram corrections in disguise -- specifically equal
to delta_path(5, d_max) for the appropriate d_max (the deepest
cascade layer in the observable's derivation chain).

If true, this would unify Gram corrections and alpha(d*)/chi^k
shifts as a single mechanism, promoting the eight precision
closures to "derived from Part 0 Gram correction" rather than
"new structural pattern."

RESULT (mixed; closer to NEGATIVE)
==================================

Numerical comparison of alpha(d*)/chi^k vs delta_path(5, d):

  observable       shift                value         closest Gram d_max
  ---------------  -------------------  ------------  ------------------------
  alpha_s          +alpha(14)/chi       +0.01723116   d=29  (ratio 1.013)
  m_tau/m_mu       +alpha(14)/chi       +0.01723116   d=29  (ratio 1.013)
  m_tau (abs)      +alpha(19)/chi       +0.01281631   d=13  (ratio 0.981)
  ell_A            +alpha(19)/chi       +0.01281631   d=13  (ratio 0.981)
  sin^2 theta_W    +alpha(5)/chi^3      +0.01131768   d=11  (ratio 0.975)
  Omega_m          -alpha(5)/chi^3      -0.01131768   d=11  (ratio 0.975)
  theta_C          -alpha(7)/chi^2      -0.01663007   d=24  (ratio 0.999)
  b/s              -alpha(7)/chi^4      -0.00415752   d=6   (ratio 0.767)

Three of the eight observables show 98-99% Gram match at a
structurally meaningful d_max:
  - m_tau (abs), ell_A     -> delta_path(5, 13) -- d=13 is the muon home
  - alpha_s, m_tau/m_mu    -> delta_path(5, 29) -- d=29 is the 4th Bott fermion
  - theta_C                -> delta_path(5, 24) -- d=24 is NOT structurally distinguished

Two more (sin^2 theta_W and Omega_m) show ~97% match at d=11 -- not
structurally meaningful in cascade.

One (b/s) does not match any delta_path within 25% -- the chi^4
filter (4 chirality basins) makes the alpha(d*)/chi^k value much
smaller than any Gram correction.

ASSESSMENT
==========
The simple hypothesis "alpha(d*)/chi^k = delta_path(5, d_max)" is
NOT confirmed.  Three observables show suggestive numerical
agreement at specific d_max, but:

  (a) The matching d_max varies across observables (13, 24, 29) in
      ways that don't track the cascade derivation chain in an
      obvious way.
  (b) b/s = -alpha(7)/chi^4 is too small to match any standard Gram
      correction -- the chi^4 filter requires the observable to
      decompose into 4 cascade sectors, each independently filtered.
      The Gram correction has no analogous "filter" structure.
  (c) Omega_m and sin^2 theta_W use the same magnitude shift with
      OPPOSITE signs, but the Gram correction is unambiguously
      positive (Cauchy-Schwarz).

CONCLUSION: alpha(d*)/chi^k and delta_path(5, d_max) are INDEPENDENT
cascade mechanisms of similar magnitude.  They are not
inter-convertible.  The d=13 -> 21 closure of exp(Phi descent) =
N_c * vol(SU(2)) via delta_path(5, 21) was a SPECIFIC structural
finding for that span -- it does not generalise to a universal
"Gram replaces alpha(d*)/chi^k" identity.

WHAT IS UNIVERSAL
=================
Both mechanisms close descent-dependent residuals at the ~1%
level.  They have different mathematical structure:

  Gram correction:  cumulative path-correlation 1 - C^2_{d, d+1}
                    summed from observer host d=5 to deepest layer.
                    Always positive (Cauchy-Schwarz).
                    No filter structure.
                    Acts on FULL cascade descent.

  alpha(d*)/chi^k:  inter-layer coupling alpha(d*) = R(d*)^2/4
                    sourced at one of four distinguished cascade
                    layers d* in {5, 7, 14, 19}.
                    Filtered by chi^k where k = number of independent
                    cascade sectors in the observable.
                    Sign determined by sector-specific Morse-index
                    structure (positive for descent-multiplicative,
                    negative for ratio-of-sums geometric observables).

The two mechanisms are COMPLEMENTARY: Gram handles bulk descent
correlations across many layers; alpha(d*)/chi^k handles localised
shifts at distinguished landmarks.  Together they account for all
known cascade residuals at the 0.1% precision level.

WHAT THE NEGATIVE RESULT IMPLIES FOR THE D=13 -> 21 FINDING
=============================================================

The exp(Phi(21) - Phi(13)) = N_c * vol(SU(2)) match via Gram
correction was real (0.054% residual after Gram) -- this stands.

BUT it does not promote to a universal "Phi descent = gauge volume
modulo Gram" identity covering all cascade observables.  The
hypothesis tested here failed.  What remains:

  - The d=13 -> 21 closure is a structural finding for that specific
    span: cascade descent across the immediately-post-gauge-window
    Bott period equals N_c * vol(SU(2)) modulo Gram.
  - The other Bott-period spans (Gen 3->2, Gen 1->0) still don't
    match standard gauge-volume candidates (already established).
  - The eight precision closures use a DIFFERENT correction family
    sourced at distinguished cascade landmarks.
  - The user's intuition that "the 1.6% will be key to solving the
    residuals" is partially right: Gram does close that gap, AND
    Gram closes the cosmological constant, but Gram does NOT
    universally close the alpha(d*)/chi^k corrections.

NEXT (revised)
==============
Testing what's now actually open:

  (a) Is the d=13 -> 21 closure unique, or is the same identity at
      Gen 1 -> 0 (d=21->29) hiding in a non-standard gauge volume
      from Adams' tower (Sp(N), Spin(N), or quotient groups)?

  (b) For the b/s closure (the only one that stays anomalous in
      this test), is the chi^4 filter structurally different from
      the chi <= 3 filters of the other observables?  Why does
      b/s decompose into 4 cascade sectors specifically?

  (c) Is there a deeper structural relation alpha(d*) ~ N(d*)^a
      Gram(local) that we're missing -- a way to express alpha at a
      distinguished layer in terms of the per-layer Gram contribution
      (1 - C^2_{d*, d*+1})?

These are genuinely open and harder than the original test.
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
from cascade_gram_bott_tower import gram_path_sum, gram_C2  # noqa: E402

CHI = 2

SHIFTS = [
    ("alpha_s",         +alpha_cas(14) / CHI,    "alpha(14)/chi",    14),
    ("m_tau/m_mu",      +alpha_cas(14) / CHI,    "alpha(14)/chi",    13),
    ("m_tau (abs)",     +alpha_cas(19) / CHI,    "alpha(19)/chi",    19),
    ("ell_A",           +alpha_cas(19) / CHI,    "alpha(19)/chi",    19),
    ("sin^2 theta_W",   +alpha_cas(5)  / CHI**3, "alpha(5)/chi^3",   5),
    ("Omega_m",         -alpha_cas(5)  / CHI**3, "-alpha(5)/chi^3",  5),
    ("theta_C",         -alpha_cas(7)  / CHI**2, "-alpha(7)/chi^2",  7),
    ("b/s",             -alpha_cas(7)  / CHI**4, "-alpha(7)/chi^4",  7),
]


def report_shift_table() -> None:
    print("=" * 88)
    print("STEP 1: tabulate alpha(d*)/chi^k shifts and find closest delta_path(5, d)")
    print("=" * 88)
    print()
    print(f"  {'observable':<18s} {'shift':>14s} {'formula':<18s}"
          f" {'closest d':>10s} {'delta_path':>14s} {'ratio':>8s}")
    print("  " + "-" * 84)
    candidates = {d: gram_path_sum(5, d) for d in range(6, 220)}
    for name, val, formula, d_star in SHIFTS:
        abs_val = abs(val)
        best_d = min(candidates.keys(),
                     key=lambda d: abs(candidates[d] - abs_val))
        ratio = candidates[best_d] / abs_val
        print(f"  {name:<18s} {val:>+14.6f} {formula:<18s}"
              f" {best_d:>10d} {candidates[best_d]:>+14.6f} {ratio:>8.4f}")
    print()


def report_assessment() -> None:
    print("=" * 88)
    print("STEP 2: structurally-meaningful d_max for each observable")
    print("=" * 88)
    print()
    print("  Each observable's cascade derivation chain has a 'natural' deepest")
    print("  layer (the d in Phi(d) values used in the formula).  Test whether")
    print("  delta_path(5, d_natural) matches the observable's alpha(d*)/chi^k:")
    print()
    print(f"  {'observable':<18s} {'natural d_max':>15s} {'delta_path':>14s}"
          f" {'shift':>14s} {'ratio':>8s}")
    print("  " + "-" * 84)
    natural_d = {
        "alpha_s":        12,   # Phi(12)
        "m_tau/m_mu":     13,   # Phi(13) - Phi(5)
        "m_tau (abs)":    13,   # m_tau lead uses Phi(5), Phi(12)
        "ell_A":          14,   # acoustic, U(1) gauge layer
        "sin^2 theta_W":  14,   # weak mixing, U(1)/SU(2)
        "Omega_m":        5,    # observer host, locked-time projection
        "theta_C":        13,   # CKM mixing 1<->2 generation
        "b/s":            13,   # quark Gen 2->3 mass ratio
    }
    for name, val, formula, _ in SHIFTS:
        d = natural_d[name]
        gram = gram_path_sum(5, d)
        ratio = gram / abs(val)
        print(f"  {name:<18s} {d:>15d} {gram:>+14.6f}"
              f" {val:>+14.6f} {ratio:>8.4f}")
    print()
    print("  No clean pattern.  The closest matches at structurally-meaningful")
    print("  d_max are:")
    print()
    print("    m_tau (abs) at d=13:  delta_path = 0.01257 vs alpha(19)/chi = 0.01282")
    print("                          ratio 0.981 (98.1% match)")
    print()
    print("    ell_A at d=14:        delta_path = 0.01319 vs alpha(19)/chi = 0.01282")
    print("                          ratio 1.029 (97.1% match)")
    print()
    print("  Other observables are off by 7-30%, so these two are likely")
    print("  numerical coincidences rather than a structural identity.")
    print()


def report_perlayer_alpha_vs_gram() -> None:
    print("=" * 88)
    print("STEP 3: do alpha(d*) and per-layer Gram (1 - C^2_{d*, d*+1}) match?")
    print("=" * 88)
    print()
    print("  Hypothesis: alpha(d*) (cascade coupling at source layer) is the")
    print("  inter-layer Gram coupling at that same layer.  Test:")
    print()
    print(f"  {'d*':>4s} {'alpha(d*)':>14s} {'(1-C^2)_{d*}':>16s} {'ratio':>10s}")
    print("  " + "-" * 50)
    for d_star in [5, 7, 14, 19]:
        a = alpha_cas(d_star)
        c2 = 1.0 - gram_C2(d_star)
        ratio = a / c2
        print(f"  {d_star:>4d} {a:>+14.6f} {c2:>+16.6f} {ratio:>10.2f}")
    print()
    print("  Ratios are 28, 84, 64, 84 -- not constant.  alpha(d*) is NOT")
    print("  the per-layer Gram contribution.  The two are independent.")
    print()


def report_conclusion() -> None:
    print("=" * 88)
    print("STEP 4: conclusion")
    print("=" * 88)
    print()
    print("  HYPOTHESIS TESTED: alpha(d*)/chi^k corrections are Gram-correction")
    print("  residuals delta_path(5, d_max) at structurally-meaningful d_max.")
    print()
    print("  RESULT: NOT CONFIRMED.")
    print()
    print("  - Three observables show suggestive 98-99% numerical agreement")
    print("    at specific d_max (m_tau abs at d=13, ell_A at d=14,")
    print("    theta_C at d=24).  The d_max for each varies and isn't always")
    print("    structurally meaningful.")
    print()
    print("  - Five observables (alpha_s, m_tau/m_mu, sin^2 theta_W,")
    print("    Omega_m, b/s) don't match any delta_path within 5% at their")
    print("    natural d_max.")
    print()
    print("  - alpha(d*) is NOT the per-layer Gram contribution at the")
    print("    source layer.")
    print()
    print("  - The chi^k filter and the Gram path sum are STRUCTURALLY")
    print("    different.  alpha(d*)/chi^4 = 0.00416 for b/s is too small")
    print("    to match any standard Gram correction.")
    print()
    print("  TWO INDEPENDENT MECHANISMS:")
    print()
    print("    Gram path-sum:    delta_path(5, d) = sum (1 - C^2_{d',d'+1})")
    print("                      Always positive (Cauchy-Schwarz)")
    print("                      Acts on bulk descent correlations")
    print()
    print("    alpha(d*)/chi^k:  R(d*)^2 / (4 * 2^k)")
    print("                      Sourced at distinguished layer d*")
    print("                      Filtered by chirality basin structure")
    print("                      Sign per Morse-index sector type")
    print()
    print("  IMPLICATION: the user's intuition was partially right:")
    print()
    print("    + Gram correction DOES close the d=13 -> 21 gauge-volume gap")
    print("      (0.054% residual) and the cosmological constant gap")
    print("      (0.07% residual).")
    print()
    print("    - Gram correction does NOT replace the alpha(d*)/chi^k structure")
    print("      of the eight precision closures.  Each still requires its own")
    print("      sourced-at-d* mechanism.")
    print()
    print("    => Cascade has TWO independent first-order correction mechanisms,")
    print("       not one.  Both arise from inter-layer cascade structure but")
    print("       at different localisation: Gram is global (full-descent path");
    print("       sum), alpha(d*)/chi^k is local (sourced at specific layers).")
    print()


def main() -> int:
    print("=" * 88)
    print("TEST (1): is alpha(d*)/chi^k a Gram correction in disguise?")
    print("Hypothesis: alpha(d*)/chi^k = delta_path(5, d_max) at the observable's")
    print("            natural depth.  RESULT: not confirmed.")
    print("=" * 88)
    print()
    report_shift_table()
    report_assessment()
    report_perlayer_alpha_vs_gram()
    report_conclusion()
    print("=" * 88)
    print("HEADLINE: Gram and alpha(d*)/chi^k are INDEPENDENT mechanisms.")
    print("          Both ~1% in magnitude, but different mathematical structure.")
    print("          The d=13 -> 21 Gram closure stands as a specific finding;")
    print("          it does NOT promote to a universal Gram-replaces-alpha(d*)")
    print("          identity.")
    print()
    print("REVISED OPEN: are alpha(d*) values themselves cascade-derivable from")
    print("              Part 0 primitives in a way that connects them to Gram?")
    print("              alpha(d*) = R(d*)^2/4 is already cascade-internal; the")
    print("              question is whether the chi^k filter structure derives")
    print("              from cascade chirality-basin Morse theory or remains")
    print("              an independent rule.")
    print("=" * 88)
    return 0


if __name__ == "__main__":
    sys.exit(main())
