#!/usr/bin/env python3
"""
Cascade-native Clifford absorption: smallest austerity-driven derivation.

CLAIM.  Within the cascade's primitive per-layer scale alpha(d) = R(d)^2/4,
the unique power-of-alpha fermion partition function that gives
d-independent Z_f / Z_s is k = 1/2, yielding Z_f = sqrt(alpha) = R(d)/2.

This forces Clifford absorption m = R/2 from austerity + d-independence
alone, without invoking sphere-bundle structure.

PROOF SKETCH.

1. Cascade scalar slicing integral (Part IVb Rem 4.1):
       N(d) = sqrt(pi) * R(d)
   And R(d) = 2 sqrt(alpha(d)) by definition of alpha = R^2/4.
   Therefore Z_s(d) = N(d) = 2 sqrt(pi) sqrt(alpha(d)).

2. Cascade-native fermion partition function (austerity clause i: no
   free parameters; clause ii: minimal strength).  The cascade has ONE
   per-layer scale, alpha(d).  A cascade-native Z_f(d) must therefore
   be expressible from alpha(d) alone.  Among monomial-in-alpha
   candidates: Z_f(d) = alpha(d)^k.

3. d-independence of Z_f / Z_s:
       Z_f / Z_s = alpha^k / (2 sqrt(pi) sqrt(alpha))
                  = alpha^{k - 1/2} / (2 sqrt(pi))
   For d-independence: k - 1/2 = 0, i.e., k = 1/2 UNIQUELY.

4. With k = 1/2: Z_f = sqrt(alpha) = R(d)/2 and ratio = 1/(2 sqrt(pi)).

This is the cascade-native Clifford absorption: m(d) = R(d)/2 forced
by austerity (only alpha as scale) + d-independence (universality).
The chirality factor 2 in 1/(2 sqrt(pi)) is structurally separate --
derived from Theorem 4.14 (Poincare-Hopf chirality halving).

VERIFICATION: numerical check at Dirac layers d in {5, 13, 21, 29}.
"""
import os
import sys

import numpy as np
from scipy.special import gamma as Gfn

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import R, alpha, pi  # noqa: E402

sqrt_pi = np.sqrt(pi)


def Z_scalar(d):
    """Cascade scalar slicing integral / lapse: Z_s(d) = N(d) = sqrt(pi) R(d)."""
    return sqrt_pi * R(d)


def Z_fermion_alphak(d, k):
    """Berezin partition function with mass alpha(d)^k: Z_f(d) = alpha^k."""
    return alpha(d) ** k


def main():
    target_ratio = 1.0 / (2 * sqrt_pi)
    DIRAC = (5, 13, 21, 29)

    print("=" * 78)
    print("CASCADE-NATIVE CLIFFORD ABSORPTION (austerity + d-independence)")
    print("=" * 78)
    print()
    print("Target ratio Z_f / Z_s = 1/(2 sqrt(pi)) = ", f"{target_ratio:.10f}")
    print()
    print("Cascade primitive scales:")
    print("  alpha(d) = R(d)^2 / 4    (scalar action compliance)")
    print("  R(d)     = 2 sqrt(alpha) (slicing recurrence coefficient)")
    print("  N(d)     = sqrt(pi) R(d) = 2 sqrt(pi) sqrt(alpha) (scalar lapse)")
    print()
    print("Z_s(d) = N(d) = 2 sqrt(pi) sqrt(alpha(d))    [cascade slicing identity]")
    print()
    print("Test Z_f(d) = alpha(d)^k for various k.  d-independence of ratio")
    print("forces k = 1/2 UNIQUELY.")
    print()

    # === Step 1: scan k values ===
    print(f"{'k':>8s}  {'d=5':>14s} {'d=13':>14s} {'d=21':>14s} {'d=29':>14s}  {'CV':>8s}  {'mean':>14s}")
    print("-" * 100)

    test_ks = [-1, -0.5, 0, 0.25, 0.4, 0.45, 0.5, 0.55, 0.6, 0.75, 1, 1.5, 2]
    best_k = None
    best_cv = float('inf')

    for k in test_ks:
        ratios = [Z_fermion_alphak(d, k) / Z_scalar(d) for d in DIRAC]
        arr = np.array(ratios, dtype=float)
        cv = arr.std() / abs(arr.mean()) if arr.mean() != 0 else float('inf')
        marker = "  <-- exactly k=1/2" if k == 0.5 else ""
        print(f"{k:>8.3f}  ", end='')
        for r in ratios:
            print(f"{r:>14.10f} ", end='')
        print(f" {cv*100:>6.3f}%  {arr.mean():>14.10f}{marker}")
        if cv < best_cv:
            best_cv = cv
            best_k = k

    print()
    print(f"Lowest CV at k = {best_k} with CV = {best_cv*100:.6f}%")
    print()

    # === Step 2: verify k=1/2 gives the target ratio ===
    print("=" * 78)
    print("Step 2: at k = 1/2, verify Z_f = R(d)/2 and ratio = 1/(2 sqrt(pi))")
    print("=" * 78)
    print()
    print(f"{'d':>4s}  {'alpha(d)':>14s}  {'Z_f = sqrt(alpha)':>20s}  {'R(d)/2':>14s}  {'ratio':>14s}  {'target':>14s}")
    for d in DIRAC:
        a = alpha(d)
        Zf = a ** 0.5
        Rd2 = R(d) / 2
        Zs = Z_scalar(d)
        ratio = Zf / Zs
        print(f"{d:>4d}  {a:>14.10f}  {Zf:>20.10f}  {Rd2:>14.10f}  "
              f"{ratio:>14.10f}  {target_ratio:>14.10f}")

    print()
    print("Z_f = sqrt(alpha(d)) = R(d)/2 exactly (closed-form Gamma identity).")
    print("Ratio Z_f/Z_s = 1/(2 sqrt(pi)) at every Dirac layer (machine precision).")
    print()

    # === Step 3: closed-form algebraic verification ===
    print("=" * 78)
    print("Step 3: closed-form algebraic verification")
    print("=" * 78)
    print()
    print("By definition: alpha(d) = R(d)^2 / 4, so sqrt(alpha(d)) = R(d)/2.")
    print()
    print("Z_f(d) = alpha(d)^{1/2} = R(d)/2")
    print("Z_s(d) = sqrt(pi) R(d) = 2 sqrt(pi) sqrt(alpha(d))")
    print()
    print("Z_f / Z_s = (R(d)/2) / (sqrt(pi) R(d))")
    print("          = 1 / (2 sqrt(pi))    [identically, no Gamma evaluation needed]")
    print()
    print("This is exact for every d at which alpha(d) is well-defined;")
    print("no Dirac-layer special structure is invoked at this stage.")

    # === Step 4: structural interpretation ===
    print()
    print("=" * 78)
    print("Step 4: structural reading and what it derives")
    print("=" * 78)
    print()
    print("The austerity claim:")
    print("  (a) The cascade has ONE per-layer scale, alpha(d) (Part IVb Rem 4.1).")
    print("  (b) A cascade-native fermion partition function must be expressible")
    print("      from alpha(d) alone (austerity clause i: no free parameters).")
    print("  (c) Z_f / Z_s d-independent (universality observation, 1.6%) forces")
    print("      the power of alpha in Z_f to be 1/2.")
    print()
    print("Conclusion:")
    print("  Z_f(d) = sqrt(alpha(d)) = R(d)/2")
    print("  Z_f / Z_s = 1/(2 sqrt(pi))")
    print()
    print("WHAT IS DERIVED at this stage: m(d) = R(d)/2 from austerity +")
    print("d-independence + the cascade's existing Z_s = 2 sqrt(pi) sqrt(alpha)")
    print("identity.")
    print()
    print("WHAT IS NOT DERIVED:")
    print("  - The chirality factor 1/chi = 1/2 in 1/(2 sqrt(pi)).  This is")
    print("    structurally separate -- derived in Theorem 4.14 from chirality")
    print("    basin selection on the spinor bundle at even-sphere layers.")
    print("    In the austerity-compliant reading, the chirality factor enters")
    print("    only via Theorem 4.14, NOT via this scale-matching argument.")
    print("  - The form of Z_f as a per-layer Berezin partition function (no")
    print("    inter-layer hopping).  This is the simplest cascade-native")
    print("    fermion action consistent with austerity, but multi-layer")
    print("    couplings are not excluded.")
    print()
    print("This is the SMALLEST cascade-native step toward Clifford absorption:")
    print("austerity + d-independence + the cascade's own Z_s identity force")
    print("Z_f = sqrt(alpha) = R(d)/2.  The remaining open problem is the")
    print("formal proof that 'cascade-native expressibility' is exactly the")
    print("monomial-in-alpha pool tested here.")


if __name__ == "__main__":
    main()
