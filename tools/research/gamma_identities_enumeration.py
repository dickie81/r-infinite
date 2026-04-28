#!/usr/bin/env python3
"""
Enumeration of Gamma function identities and their cascade-native applications.

Audit context: cascade-geometric-topological-audit.md Section 11 lists 9
Gamma-related entries.  Several were marked IGN (cascade-forced but unused).
This script enumerates each identity, applies it to cascade slicing ratios
R(d) = Gamma((d+1)/2) / Gamma((d+2)/2), and reports whether a cascade-native
application emerges.

Cascade primitives at play:
  R(d) -- slicing ratio (Part 0)
  alpha(d) = R(d)^2 / 4 -- compliance (Part IVb Remark 4.6)
  N(d), Omega_d -- lapse / sphere area
  Phi(d) -- cumulative cascade potential (Part IVa)

Cascade-relevant identities have arguments that hit integers d in the
tower {0, 1, ..., 217} or half-integers (d+1)/2, (d+2)/2 for d integer.
"""

from __future__ import annotations

import math
import sys

from scipy.special import gammaln  # type: ignore[import-not-found]


def log_R(d: int) -> float:
    return float(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def R(d: int) -> float:
    return math.exp(log_R(d))


def main() -> int:
    print("=" * 78)
    print("GAMMA IDENTITIES: ENUMERATION + CASCADE APPLICATIONS")
    print("=" * 78)
    print()

    # ----------------------------------------------------------------
    # 11.1 Half-integer Gamma: Gamma(n + 1/2) = (2n)! sqrt(pi) / (4^n n!)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.1 HALF-INTEGER GAMMA EVALUATION")
    print("     Gamma(n + 1/2) = (2n)! sqrt(pi) / (4^n n!)")
    print("-" * 78)
    print("Cascade application: R at odd argument 2k-1 has closed form")
    print("    R(2k-1) = Gamma(k) / Gamma(k+1/2) = (k-1)! * 4^k * k! / ((2k)! * sqrt(pi))")
    print("Status: USED implicitly (Part IVb closure formulas evaluate at half-integers)")
    print()

    # ----------------------------------------------------------------
    # 11.2 Gamma recursion: Gamma(z+1) = z * Gamma(z)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.2 GAMMA RECURSION: Gamma(z+1) = z * Gamma(z)")
    print("-" * 78)
    print("Cascade application: R(d+2)/R(d) = (d+1)/(d+2)")
    print("    (Part 4b line 2014: 'exact Gamma recursion R(d+2)/R(d)=(d+1)/(d+2)')")
    print("Status: USED -- the foundational recursion of cascade slicing")
    print()

    # ----------------------------------------------------------------
    # 11.3 Beta function identities: B(a,b) = Gamma(a) Gamma(b) / Gamma(a+b)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.3 BETA FUNCTION IDENTITIES")
    print("-" * 78)
    print("Cascade application: B(1/2, n+1) = sqrt(pi) * R(2n+1)")
    print("    Gram entries reduce to slicing ratios via Beta-Gamma identity.")
    print("Status: USED -- foundational Gram-matrix structure")
    print()

    # ----------------------------------------------------------------
    # 11.4 Euler reflection: Gamma(z) Gamma(1-z) = pi / sin(pi z)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.4 EULER REFLECTION: Gamma(z) Gamma(1-z) = pi / sin(pi z)")
    print("-" * 78)
    print("Application to R: at z = (d+1)/2 with d integer,")
    print("    Gamma((d+1)/2) Gamma((1-d)/2) = pi / sin(pi(d+1)/2)")
    print("For d even, sin(pi(d+1)/2) = +/- 1, finite right-hand side.")
    print("For d odd, sin = 0, RHS infinite.")
    print()
    print("The argument (1-d)/2 for d >= 2 is a NEGATIVE half-integer,")
    print("which is OFF THE CASCADE TOWER (cascade has positive integer d).")
    print()
    print("Verdict: NO direct cascade application.  The reflection relates")
    print("Gamma at positive and negative half-integers; the cascade lives on")
    print("the positive side.  Status: IGN (correctly so).")
    print()

    # ----------------------------------------------------------------
    # 11.5 Gauss multiplication theorem -- LANDED in PR #96
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.5 GAUSS MULTIPLICATION (n=2): LEGENDRE DUPLICATION")
    print("     Gamma(2z) = (2pi)^{-1/2} 2^{2z-1/2} Gamma(z) Gamma(z+1/2)")
    print("-" * 78)
    print("Cascade application: R(2d-1) * R(2d) = 1/d  (Part 0 Lemma 2.2)")
    print("                     R(2d) * R(2d+1)  = 2/(2d+1)  (immediate corollary)")
    print("                     prod_{d=1}^{2N} R(d) = 1/N!  (telescoping)")
    print("Status: USED -- via Lemma `lem:R-duplication` in PR #96 (merged)")
    print()
    print("Verifying the corollary R(2d) * R(2d+1) = 2/(2d+1):")
    print(f"{'d':>4}  {'R(2d) R(2d+1)':>16}  {'2/(2d+1)':>14}  {'match':>6}")
    print("-" * 50)
    for d in [1, 2, 3, 5, 7, 10, 50]:
        prod = R(2*d) * R(2*d+1)
        target = 2.0 / (2*d + 1)
        ok = abs(prod - target) < 1e-12
        print(f"{d:>4}  {prod:>16.12f}  {target:>14.10f}  {'OK' if ok else 'FAIL':>6}")
    print()

    # ----------------------------------------------------------------
    # 11.5b Gauss multiplication n=3 (triplication)
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.5b GAUSS MULTIPLICATION (n=3): TRIPLICATION")
    print("     Gamma(3z) = (2 pi)^{-1} 3^{3z - 1/2} Gamma(z) Gamma(z+1/3) Gamma(z+2/3)")
    print("-" * 78)
    print("Application: triplication involves Gamma at THIRD-integer arguments")
    print("z + 1/3 and z + 2/3, which are NOT half-integer.  Cascade tower has")
    print("integer d, so R(d) involves Gamma at half-integers only.  Third-")
    print("integer Gamma arguments don't correspond to any cascade primitive.")
    print()
    print("Verdict: NO cascade application.  Status: IGN (correctly so).")
    print()

    # ----------------------------------------------------------------
    # 11.6 Wallis product: pi/2 = prod (2n)^2 / [(2n-1)(2n+1)]
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.6 WALLIS PRODUCT")
    print("     pi/2 = prod_{n=1}^{infty} (2n)^2 / [(2n-1)(2n+1)]")
    print("-" * 78)
    print("Cascade application: Wallis product is the asymptotic limit of cascade")
    print("slicing-ratio products.  Specifically, R(d) ~ sqrt(2/(d+1)) as d -> inf")
    print("(used in Theorem 14.2's overlap-deficit asymptotic 1/(8d^2)).  Stirling-")
    print("Wallis is implicit in this asymptotic.")
    print()
    print("Verdict: USED implicitly via Stirling asymptotics.  Status was IGN")
    print("'Implicit in R(d) ~ sqrt(2/d)'; the implicit reading is correct.")
    print()

    # ----------------------------------------------------------------
    # 11.7 Stirling
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.7 STIRLING'S FORMULA: log Gamma(z) = (z-1/2) log z - z + ...")
    print("-" * 78)
    print("Status: USED -- Part 0.0 Theorem 14.2 asymptotic 1 - C^2 ~ 1/(8 d^2)")
    print()

    # ----------------------------------------------------------------
    # 11.8 Continued fractions of Gamma ratios
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.8 CONTINUED FRACTIONS OF GAMMA RATIOS")
    print("-" * 78)
    print("Application: Lentz/Stieltjes continued-fraction expansions of Gamma")
    print("ratios are typically NUMERICAL tools (faster convergence than series).")
    print("They don't expose new structural identities -- the values are the same")
    print("as the closed-form Gamma ratios already in use.")
    print()
    print("Verdict: NO structural cascade application.  Status: IGN (correctly so).")
    print()

    # ----------------------------------------------------------------
    # 11.9 Zeta values at integer/half-integer
    # ----------------------------------------------------------------
    print("-" * 78)
    print("11.9 ZETA VALUES AT INTEGER / HALF-INTEGER")
    print("-" * 78)
    print("Application: zeta(2n) = (-1)^{n+1} B_{2n} (2 pi)^{2n} / (2 (2n)!)")
    print("relates zeta values at even integers to Bernoulli numbers and pi.")
    print()
    print("Cascade-specific check: zeta(2) = pi^2/6 appears implicitly in")
    print("Omega_b = 1/(2 pi^2) and similar geometric quantities (Part V).")
    print("zeta(2n) for n >= 2 (i.e., pi^4/90, pi^6/945, ...) is not invoked.")
    print()
    print("Verdict: zeta(2) IMPLICIT in some cosmological formulas; higher")
    print("zeta values not used.  Status: partially implicit.")
    print()

    # ----------------------------------------------------------------
    # SUMMARY
    # ----------------------------------------------------------------
    print("=" * 78)
    print("SUMMARY: CASCADE APPLICATIONS OF GAMMA IDENTITIES")
    print("=" * 78)
    print()
    print(f"{'Identity':>40}  {'Cascade use':>15}  {'Status':>15}")
    print("-" * 78)
    rows = [
        ("11.1 Half-integer Gamma evaluation", "Closed-form R", "USED"),
        ("11.2 Gamma recursion", "R(d+2)/R(d) = (d+1)/(d+2)", "USED"),
        ("11.3 Beta function", "Gram entries", "USED"),
        ("11.4 Euler reflection", "(off-tower)", "IGN [correctly]"),
        ("11.5 Legendre duplication (n=2)", "R(2d-1)R(2d)=1/d", "USED [PR #96]"),
        ("11.5b Triplication (n=3)", "(third-integer)", "IGN [correctly]"),
        ("11.6 Wallis product", "asymptotic", "implicit"),
        ("11.7 Stirling", "asymptotic deficit", "USED"),
        ("11.8 Continued fractions", "(numerical only)", "IGN [correctly]"),
        ("11.9 Zeta values", "zeta(2) only", "partially implicit"),
    ]
    for name, app, status in rows:
        print(f"{name:>40}  {app:>15}  {status:>15}")
    print()
    print("VERDICT:")
    print()
    print("Of 10 Gamma identities surveyed:")
    print("  - 5 are USED (recursion, half-integer eval, Beta, duplication, Stirling)")
    print("  - 2 are partially implicit (Wallis, zeta(2))")
    print("  - 3 are correctly IGN (off-tower or numerical-only):")
    print("       Euler reflection (negative half-integers, off-tower)")
    print("       Triplication (third-integer Gamma, no cascade primitive)")
    print("       Continued fractions (numerical, no new structure)")
    print()
    print("The audit's 11.x section now resolves cleanly: the unused entries")
    print("are unused for STRUCTURAL reasons (their arguments don't hit cascade")
    print("primitives), not for missed-opportunity reasons.")
    print()
    print("The Legendre duplication Lemma (PR #96) was the only substantive")
    print("missed opportunity.  No further Gamma-identity windfalls exist.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
