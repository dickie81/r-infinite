#!/usr/bin/env python3
"""
The canonical-formula selection problem.

Background
----------
The categorical exhaustiveness theorem (source_selection_categorical.py)
proved that the cascade observable algebra has exactly four sub-algebra
membership classes, forced by an algebraic constraint.  The bijection to
{d_V=5, d_0=7, d_gw=14, d_1=19} is structurally compatible per Part IVb.

But applying the four-class classification to specific observables hits a
problem: the same observable admits MULTIPLE cascade-native expressions,
and different expressions land in different classes.  Example:
  alpha_s(M_Z) = N(12)^2 / (2*sqrt(pi))             [in A_static]
              = exp(2*Phi(11->12)) / (2*sqrt(pi))   [in A_noStatic]
The first form classifies as Observer (F3=T -> d_V=5).
The second form classifies as Gauge (F1=T -> d_gw=14).
Part IVb intends the Gauge classification.  How is the canonical choice made?

This script:
  1. Enumerates candidate canonical-formula selection rules.
  2. Tests each against the eight closed observables.
  3. Identifies which rules give Part IVb's intended classification and
     which fail.
  4. Reports an honest assessment of whether any rule is fully cascade-
     internal (i.e., requires no external interpretation).

Candidate rules:
  R1: Minimal-symbol form (fewest cascade primitive symbols).
  R2: Maximal-descent form (always prefer exp(Phi) over N(d) when both express
      the same value).
  R3: Green's function peak (canonical source d* is where the discrete Sturm-
      Liouville Green's function of the cascade action peaks for the observable's
      perturbation; canonical formula is one consistent with that d*).
  R4: Numerical residual matching (canonical d*, k is the (d*, k) that minimises
      |observed_residual - alpha(d*)/chi^k|).
  R5: Structural-role consistency (intersection of R3 + R4 + Part IVb structural
      compatibility).
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def R(d: int) -> float:
    return math.exp(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def alpha(d: int) -> float:
    return R(d) ** 2 / 4


CHI = 2
CANDIDATES = [(5, 1), (5, 2), (5, 3), (5, 4),
              (7, 1), (7, 2), (7, 3), (7, 4),
              (14, 1), (14, 2), (14, 3),
              (19, 1), (19, 2)]


def main() -> int:
    print("=" * 88)
    print("CANONICAL-FORMULA SELECTION RULE: ANALYSIS")
    print("=" * 88)
    print()
    print("Question: how is the 'canonical formula' for each observable selected")
    print("from cascade primitives, without external interpretation?")
    print()

    # ---- R1: Minimal-symbol form ----
    print("-" * 88)
    print("RULE R1: MINIMAL-SYMBOL FORM")
    print("-" * 88)
    print()
    print("Rule: choose the cascade-native expression with fewest primitive symbols.")
    print("Application:")
    print("  alpha_s = N(12)^2 / (2*sqrt(pi))            [3 symbols: N(12), 2, sqrt(pi)]")
    print("  alpha_s = exp(2*Phi(11->12)) / (2*sqrt(pi)) [4 symbols + descent]")
    print("  -> R1 picks the static form.")
    print()
    print("Result: alpha_s -> Observer class -> d=5.  WRONG (Part IVb says d=14).")
    print()
    print("Verdict: R1 fails.  Cascade-native minimisation prefers static forms,")
    print("which mismatches Part IVb's gauge-coupling reading.")
    print()

    # ---- R2: Maximal-descent form ----
    print("-" * 88)
    print("RULE R2: MAXIMAL-DESCENT FORM")
    print("-" * 88)
    print()
    print("Rule: always rewrite N(d) as exp(Phi(d-1->d)) when possible; prefer")
    print("descent-encoded forms over static forms.")
    print()
    print("Application:")
    print("  alpha_s = exp(2*Phi(11->12)) / (2*sqrt(pi))  -> contains gauge-")
    print("    window descent factor (12 in {12,13,14}, but length 1)")
    print("  Single-layer Phi(11->12) length is 1, not multi-layer (>=2).")
    print("  Per Part IVb's gauge-mediated definition: 'd_B - d_A >= 2 and the")
    print("    path crosses the gauge window'.  Single-layer doesn't qualify.")
    print("  -> R2 still classifies alpha_s as Amplitude (no gauge factor) -> d=7.")
    print()
    print("WRONG (Part IVb says d=14).  R2 also fails.")
    print()
    print("More aggressively: rewrite N(12) = exp(Phi(0->12)) to maximise descent")
    print("length.  Then Phi(0->12) has length 12 >= 2 and crosses {12}, so it's")
    print("a 'multi-layer gauge-window factor'.  alpha_s -> Gauge -> d=14.  CORRECT.")
    print()
    print("But this 'always-rewrite-to-Phi(0->d)' rule picks d=14 for ANY formula")
    print("containing N(12), regardless of whether the observable is gauge-related.")
    print("E.g., theta_C contains N(12), N(13) per Part IVb line 1246, but is")
    print("classified as Amplitude (d=7) because 'N(12), N(13) only as static")
    print("normalisations (inside an arccos), not as running couplings'.")
    print("R2 misclassifies theta_C as Gauge.")
    print()
    print("Verdict: R2 fails.  Maximal-descent rewriting is too aggressive: it")
    print("treats every N(d) as a running coupling, which contradicts Part IVb's")
    print("'static normalisation vs running coupling' distinction (interpretive!).")
    print()

    # ---- R3: Green's function peak ----
    print("-" * 88)
    print("RULE R3: GREEN'S FUNCTION PEAK")
    print("-" * 88)
    print()
    print("Rule: canonical d* is where the cascade action's discrete Sturm-")
    print("Liouville Green's function G(d=4, d*) peaks among {5, 7, 14, 19}.")
    print()
    print("Numerical computation (cascade_greens_function.py):")
    print("  G(4, d*) = sum_{k=d*}^{216} alpha(k)  (cumulative compliance)")
    print()
    print(f"{'d*':>5}  {'G(4, d*)':>14}")
    print("-" * 26)
    G_at = {}
    for d_star in [5, 7, 14, 19]:
        # Use a moderate upper cutoff for cumulative-compliance approximation
        G_val = sum(alpha(k) for k in range(d_star, 217))
        G_at[d_star] = G_val
        print(f"{d_star:>5}  {G_val:>14.6e}")
    print()
    print("G(4, d*) is monotonically decreasing in d*.  So R3 'peak' always")
    print("selects d*=5 -- the smallest candidate.  Doesn't differentiate observables.")
    print()
    print("Verdict: R3 fails as stated.  The naive Green's function peak rule")
    print("doesn't distinguish the four source layers; some observable-specific")
    print("perturbation modelling is needed, which reintroduces interpretation.")
    print()

    # ---- R4: Numerical residual matching ----
    print("-" * 88)
    print("RULE R4: NUMERICAL RESIDUAL MATCHING")
    print("-" * 88)
    print()
    print("Rule: canonical (d*, k) is the (d*, k) that minimises")
    print("  | observed_residual - alpha(d*)/chi^k |")
    print("over candidate (d*, k) in {5,7,14,19} x {1,2,3,4}.")
    print()
    print("This is a numerical fit using cascade-native quantities (alpha, chi)")
    print("and observed residuals.  The residual itself is empirical, so this")
    print("rule is NOT fully cascade-internal -- but it picks d* without recourse")
    print("to syntactic flags or canonical-formula choice.")
    print()
    # Test each observable
    obs_residuals = {
        "alpha_s(M_Z)":    -0.01696,    # leading 0.1159, observed 0.1179
        "m_tau/m_mu":       -0.01707,
        "m_tau (abs)":     -0.01228,
        "ell_A":            -0.01326,
        "sin^2(theta_W)":  -0.01118,
        "Omega_m":           0.01137,
        "theta_C":           0.01685,    # leading ~13.26 deg (PartIVb shift -alpha(7)/chi^2 closes to obs 13.04)
        "b/s":               0.00417,
    }
    expected = {
        "alpha_s(M_Z)":    (14, 1),
        "m_tau/m_mu":      (14, 1),
        "m_tau (abs)":     (19, 1),
        "ell_A":           (19, 1),
        "sin^2(theta_W)":  (5, 3),
        "Omega_m":         (5, 3),
        "theta_C":         (7, 2),
        "b/s":             (7, 4),
    }
    print(f"{'observable':>16}  {'residual':>10}  {'best (d*, k)':>14}  "
          f"{'expected':>10}  {'match':>6}")
    print("-" * 72)
    matches = 0
    for name, r in obs_residuals.items():
        best = min(CANDIDATES, key=lambda dk: abs(abs(r) - alpha(dk[0]) / CHI ** dk[1]))
        exp_dk = expected[name]
        ok = (best == exp_dk)
        if ok:
            matches += 1
        print(f"{name:>16}  {r:>+10.5f}  {str(best):>14}  {str(exp_dk):>10}  "
              f"{'OK' if ok else 'FAIL':>6}")
    print()
    print(f"R4 numerical-match success rate: {matches}/{len(obs_residuals)}")
    print()
    if matches == len(obs_residuals):
        print("R4 succeeds: numerical residual match alone reproduces Part IVb's")
        print("(d*, k) assignments for all 8 closed observables.  No syntactic flag,")
        print("canonical-formula choice, or structural role required.")
        print()
        print("This is significant: the alpha(d*)/chi^k family closures are")
        print("UNIQUELY identified by numerical fit over the candidate set {d*=5,7,")
        print("14,19} x {k=1,2,3,4}.  Each observable's residual has a unique best")
        print("match -- no ambiguity.  R4 is therefore a CASCADE-INTERNAL VERIFIER")
        print("of Part IVb's assignments (the (d*, k) values are forced by the data).")
        print()
        print("What R4 is NOT: a derivation from F_Q alone.  It uses observed")
        print("residuals as input.  So R4 is empirical-verifying, not theory-")
        print("predicting -- but it does FORCE the (d*, k) values uniquely once the")
        print("observable's leading cascade prediction is known.")
    else:
        print("R4 partial: some observables don't have unique numerical match.")
    print()

    # ---- R5: Structural-role consistency ----
    print("-" * 88)
    print("RULE R5: STRUCTURAL-ROLE CONSISTENCY")
    print("-" * 88)
    print()
    print("Rule: canonical d* is the unique element of {5, 7, 14, 19} consistent")
    print("with all of (a) Green's function structural role, (b) numerical")
    print("residual match, (c) Part IVb structural compatibility (Remark 1255).")
    print()
    print("Per Part IVb Remark 1255 (line 1255-1264):")
    print("  d_1=19 is the only non-sink threshold on the Planck ladder")
    print("  d_V=5  is the only layer adjacent to observer (S^3 = boundary B^5)")
    print("  d_gw=14 is the highest layer of gauge window {12,13,14}")
    print("  d_0=7  is the unique remaining non-sink distinguished layer")
    print()
    print("This argument IS structural -- but it requires KNOWING the observable")
    print("class (Planck-anchored / observer-local / gauge-mediated / amplitude)")
    print("to apply.  Class assignment is the very thing we're trying to derive.")
    print()
    print("Verdict: R5 is self-consistent but not bootstrappable from cascade")
    print("primitives alone.  It requires the class assignment as an input.")
    print()

    # ---- Conclusion ----
    print("=" * 88)
    print("CONCLUSION: WHERE THE CANONICAL-FORMULA RULE STANDS")
    print("=" * 88)
    print()
    print("None of R1, R2, R3, R5 is fully cascade-internal in the strong sense")
    print("of 'derive d* from F_Q without external interpretation'.")
    print()
    print("R4 (numerical residual match) gets the right answer for all 8 closed")
    print("observables, but uses observed deviations as input -- so it's empirical")
    print("verification, not derivation.")
    print()
    print("The genuine residual content of the canonical-formula selection rule")
    print("is therefore: cascade-internally model each observable's PERTURBATION")
    print("LOCATION on the cascade tower.  Once the perturbation source is specified")
    print("cascade-internally (without 'gauge coupling', 'observer-local', etc.),")
    print("the four-class assignment follows from the algebraic theorem of")
    print("source_selection_categorical.py.")
    print()
    print("This is the SHARPEST refinement of Part IVb oq:source-selection-category:")
    print()
    print("    Refined OQ: For each cascade observable Q (defined as an element")
    print("    of the cascade primitive algebra), give a CASCADE-INTERNAL rule")
    print("    that determines the location of Q's natural perturbation source")
    print("    on the cascade tower {0, 1, ..., 217}, without reference to")
    print("    Standard Model physics interpretation.")
    print()
    print("    Once this rule is in place, the categorical theorem (Theorem 1 of")
    print("    source_selection_categorical.py) classifies Q to its source-class")
    print("    via sub-algebra membership, completing the cascade-internal")
    print("    derivation of the alpha(d*)/chi^k correction family.")
    print()
    print("Honest negative finding: the canonical-formula rule is not yet derivable.")
    print("Part IVb's framework is consistent, verified numerically (R4), and")
    print("structurally compatible (R5), but requires the perturbation-location")
    print("input that is currently external to the cascade algebra.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
