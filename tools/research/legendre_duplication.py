#!/usr/bin/env python3
"""
Verify the slicing-ratio duplication identity:

    R(2d-1) * R(2d) = 1/d  for all integer d >= 1

and the telescoping consequence

    prod_{d=1}^{2N} R(d) = 1/N!

These are the cascade-internal expression of the Legendre duplication
formula Gamma(2z) = (2 pi)^{-1/2} 2^{2z-1/2} Gamma(z) Gamma(z + 1/2),
specialised to integer z.

This script confirms the identity numerically across the cascade-physics
range (d = 1 to ~100) and the telescoping product up to N = 20.

References: Part 0 Lemma `lem:R-duplication`; cascade-geometric-topological-
audit.md entry 11.5 (Gauss multiplication theorem) -- the n=2 special case
is now USED.
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
    print("=" * 72)
    print("LEGENDRE DUPLICATION IDENTITY FOR CASCADE SLICING RATIOS")
    print("=" * 72)
    print()
    print("Identity 1: R(2d-1) * R(2d) = 1/d")
    print()
    print(f"{'d':>4}  {'R(2d-1)':>14}  {'R(2d)':>14}  {'product':>16}  "
          f"{'1/d':>14}  {'rel diff':>12}")
    print("-" * 72)
    failures: list[str] = []
    for d in [1, 2, 3, 5, 7, 14, 19, 50, 100, 217]:
        rs = R(2 * d - 1)
        rss = R(2 * d)
        prod = rs * rss
        target = 1.0 / d
        rel = abs(prod - target) / target if target != 0 else float("inf")
        if rel > 1e-12:
            failures.append(f"d={d}: rel diff {rel:.2e}")
        print(f"{d:>4}  {rs:>14.10f}  {rss:>14.10f}  {prod:>16.12f}  "
              f"{target:>14.10f}  {rel:>12.2e}")
    print()

    print("Identity 2 (telescoping): prod_{d=1}^{2N} R(d) = 1/N!")
    print()
    print(f"{'N':>4}  {'prod_{d=1..2N} R(d)':>22}  {'1/N!':>14}  {'rel diff':>12}")
    print("-" * 60)
    log_prod = 0.0
    for d in range(1, 41):
        log_prod += log_R(d)
        if d % 2 == 0:
            N = d // 2
            prod = math.exp(log_prod)
            factorial_inv = 1.0 / math.factorial(N)
            rel = abs(prod - factorial_inv) / factorial_inv
            if rel > 1e-12:
                failures.append(f"N={N}: rel diff {rel:.2e}")
            if N <= 20:
                print(f"{N:>4}  {prod:>22.14e}  {factorial_inv:>14.6e}  {rel:>12.2e}")
    print()

    if failures:
        print("FAIL:")
        for f in failures:
            print(f"  {f}")
        return 1
    print("Both identities verified to machine precision (rel diff < 1e-12).")
    print()
    print("Implication: the cascade tower's slicing ratios obey a fixed product")
    print("law at each odd-even pair, and the full-tower product is the inverse")
    print("factorial of the half-tower height.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
