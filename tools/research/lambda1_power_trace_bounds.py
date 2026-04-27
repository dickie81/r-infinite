#!/usr/bin/env python3
"""
Power-trace bound family for lambda_1(C).

For a positive-definite symmetric matrix C with eigenvalues
lambda_1 >= lambda_2 >= ... >= lambda_n > 0:
  tr(C^k) = sum_j lambda_j^k.
Since lambda_1 is the largest, tr(C^k)^{1/k} is an upper bound on lambda_1.
The bound tightens as k grows (it equals the operator norm in the limit
k -> infinity).

For the cascade matrix C, every tr(C^k) is closed-form in slicing ratios
(it's a polynomial sum of R-ratios), so every member of the family
   lambda_1 <= U_k(d_0, n) := tr(C^k)^{1/k}
is a cascade-native explicit upper bound on the dominant eigenvalue.

This script:
  1. Computes lambda_1(C) exactly (mpmath SVD via numpy at moderate precision).
  2. Computes U_k for k = 1, 2, 3, 4, 6 across (n, d_0) cascade-physics samples.
  3. Reports relative gap (U_k - lambda_1) / lambda_1 to identify the
     tightest cascade-native bound at each scale.

The hypothesis: U_2 = sqrt(tr(C^2)) is dramatically tighter than U_1 = n
(the trivial bound), and U_3, U_4, ... continue to tighten.  At cascade
scales (lambda_2 ~ 1% of lambda_1), U_3 should be tight to ~ 1e-4 and
U_4 to ~ 1e-6.

If the bound tightens fast enough, U_K for moderate K (say K = 5) could
serve as a *practically-exact* closed-form expression for lambda_1 in
cascade slicing ratios -- potentially closing OQ2's "richer cascade
primitives" loophole.
"""

from __future__ import annotations

import math
import sys

import mpmath as mp  # type: ignore[import-not-found]
import numpy as np

mp.mp.dps = 60


def R_mp(d: int) -> mp.mpf:
    return mp.gamma(mp.mpf(d + 1) / 2) / mp.gamma(mp.mpf(d + 2) / 2)


def build_C_mp(n: int, d0: int) -> mp.matrix:
    m = 2 * d0 + 1
    C = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            C[i, j] = R_mp(m + i + j) / mp.sqrt(R_mp(m + 2 * i) * R_mp(m + 2 * j))
    return C


def trace_Ck(C: mp.matrix, k: int) -> mp.mpf:
    """tr(C^k) using mpmath matrix multiplication."""
    n = C.rows
    Ck = mp.eye(n)
    for _ in range(k):
        Ck = Ck * C
    s = mp.mpf(0)
    for i in range(n):
        s += Ck[i, i]
    return s


def lambda1_mp(C: mp.matrix) -> mp.mpf:
    """Largest eigenvalue via numpy after conversion (sufficient precision)."""
    n = C.rows
    arr = np.array([[float(C[i, j]) for j in range(n)] for i in range(n)])
    return mp.mpf(float(np.linalg.eigvalsh(arr)[-1]))


def main() -> int:
    print("=" * 78)
    print("POWER-TRACE UPPER-BOUND FAMILY FOR LAMBDA_1")
    print("=" * 78)
    print()
    print("Bound family: U_k = tr(C^k)^{1/k} >= lambda_1, tightening as k -> infty.")
    print("Each U_k is closed-form in cascade slicing ratios (sum of R-ratio products).")
    print()

    cases = [(n, d0) for d0 in [5, 7, 14, 19] for n in [3, 4, 6, 8, 10]]

    print(f"{'n':>3} {'d_0':>4}  {'lambda_1':>14}  {'U_1=n':>8}  "
          f"{'U_2 gap':>12}  {'U_3 gap':>12}  {'U_4 gap':>12}  {'U_6 gap':>12}")
    print("-" * 95)
    for n, d0 in cases:
        C = build_C_mp(n, d0)
        lam1 = lambda1_mp(C)
        ks = [1, 2, 3, 4, 6]
        Us = []
        for k in ks:
            tk = trace_Ck(C, k)
            Uk = tk ** (mp.mpf(1) / k)
            Us.append(Uk)
        gaps = [(Uk - lam1) / lam1 for Uk in Us]
        print(
            f"{n:>3} {d0:>4}  {float(lam1):>14.10f}  {n:>8}  "
            f"{float(gaps[1]):>12.4e}  {float(gaps[2]):>12.4e}  "
            f"{float(gaps[3]):>12.4e}  {float(gaps[4]):>12.4e}"
        )
    print()

    # -----------------------------------------------------------------
    # Long path: rho_Lambda descent
    # -----------------------------------------------------------------
    print("-" * 78)
    print("LONG CASCADE PATHS")
    print("-" * 78)
    print(f"{'path':>20}  {'lambda_1':>14}  {'U_2 gap':>12}  {'U_3 gap':>12}  "
          f"{'U_4 gap':>12}  {'U_6 gap':>12}")
    print("-" * 90)
    for d_start, d_end, name in [(5, 12, "alpha_s"), (6, 13, "m_tau/m_mu"),
                                  (14, 21, "m_mu/m_e"), (5, 30, "long(d=5..30)")]:
        n = d_end - d_start + 1
        C = build_C_mp(n, d_start)
        lam1 = lambda1_mp(C)
        gaps = []
        for k in [2, 3, 4, 6]:
            Uk = trace_Ck(C, k) ** (mp.mpf(1) / k)
            gaps.append(float((Uk - lam1) / lam1))
        print(f"{name:>20}  {float(lam1):>14.10f}  {gaps[0]:>12.4e}  {gaps[1]:>12.4e}  "
              f"{gaps[2]:>12.4e}  {gaps[3]:>12.4e}")
    print()

    print("=" * 78)
    print("INTERPRETATION")
    print("=" * 78)
    print()
    print("Each U_k is a cascade-native explicit upper bound on lambda_1, computable")
    print("as a single sum of R-ratio products with no eigenvalue computation:")
    print("  U_1 = n                           (trivial; trace identity)")
    print("  U_2 = sqrt(sum_{ij} C_{ij}^2)     (Frobenius bound)")
    print("  U_k = (sum_{i_1,...,i_k} C_{i_1 i_2} ... C_{i_k i_1})^{1/k}")
    print()
    print("The bound tightens monotonically: U_1 >= U_2 >= U_3 >= ... >= lambda_1.")
    print("Convergence rate is geometric in (lambda_2 / lambda_1)^k.")
    print()
    print("This gives a one-parameter family of cascade-native closed-form")
    print("approximations to lambda_1 with explicit error decay -- a *practical*")
    print("closed form to any desired precision, even if a single exact closed-form")
    print("equality is obstructed by Abel-Ruffini at n >= 5.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
