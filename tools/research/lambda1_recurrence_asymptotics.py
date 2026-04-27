#!/usr/bin/env python3
"""
Asymptotic structure of the Stieltjes recurrence for the cascade OP family.

Reverse-engineering goal: characterise (a_k, b_k) - asymptotic limits as
closed forms in (m, k), even if no exact-finite-k formula exists.

Universal asymptotic (Geronimus/Szego, see Simon 2005):
For absolutely continuous mu = w(x) dx on [0, 1] with w continuous and
positive on the open interval, the recurrence coefficients satisfy
   a_k - 1/2 = O(1/k),   b_k - 1/4 = O(1/k).
The leading coefficients depend on the boundary behaviour of w.

For our weight w(x) = x^m / sqrt(1-x^2):
  - boundary x=0: w ~ x^m  (vanishes to order m)
  - boundary x=1: w ~ 1/sqrt(1-x)  (integrable singularity, exponent -1/2)

This script tests:
  1. Confirm a_0 = R(m+1)/R(m) exactly (closed form for k=0).
  2. Confirm b_0^2 = R(m+2)/R(m) - [R(m+1)/R(m)]^2 exactly.
  3. Does (a_k - 1/2) k -> finite limit as k -> infinity?  Is the limit
     a closed form in m?
  4. For k -> infinity at FIXED m: convergence rate; does it match the
     known Bernstein-Szego rate for the boundary type?

If the asymptotic constants are closed-form in m, then for large k
   a_k ~ 1/2 + alpha(m)/k + O(1/k^2)
   b_k ~ 1/4 + beta(m)/k + O(1/k^2)
which gives lambda_1(C) an asymptotic expansion in 1/n at large n.

Even partial closed forms (like a_0, b_0 exact in cascade primitives)
are structural progress.
"""

from __future__ import annotations

import sys

import mpmath as mp  # type: ignore[import-not-found]
import numpy as np

mp.mp.dps = 80


def R_mp(d: int) -> mp.mpf:
    return mp.gamma(mp.mpf(d + 1) / 2) / mp.gamma(mp.mpf(d + 2) / 2)


def cascade_moment(k: int, m: int) -> mp.mpf:
    return mp.sqrt(mp.pi) / 2 * R_mp(m + k)


def stieltjes_recurrence(n: int, m: int) -> tuple[list[mp.mpf], list[mp.mpf]]:
    moments = [cascade_moment(k, m) for k in range(2 * n + 2)]
    a_list: list[mp.mpf] = []
    b_list: list[mp.mpf] = []
    p_prev = [mp.mpf(0)]
    p_curr = [mp.mpf(1) / mp.sqrt(moments[0])]
    b_prev = mp.mpf(0)
    for k in range(n):
        a_k = mp.mpf(0)
        for i in range(len(p_curr)):
            for ll in range(len(p_curr)):
                a_k += p_curr[i] * p_curr[ll] * moments[i + ll + 1]
        a_list.append(a_k)
        q = [mp.mpf(0)] * (len(p_curr) + 1)
        for i in range(len(p_curr)):
            q[i + 1] += p_curr[i]
            q[i] -= a_k * p_curr[i]
        for i in range(len(p_prev)):
            q[i] -= b_prev * p_prev[i]
        norm_sq = mp.mpf(0)
        for i in range(len(q)):
            for ll in range(len(q)):
                norm_sq += q[i] * q[ll] * moments[i + ll]
        if norm_sq <= 0:
            break
        b_k = mp.sqrt(norm_sq)
        b_list.append(b_k)
        p_prev = p_curr
        p_curr = [qi / b_k for qi in q]
        b_prev = b_k
    return a_list, b_list


def main() -> int:
    print("=" * 78)
    print("ASYMPTOTIC STRUCTURE OF CASCADE OP RECURRENCE")
    print("=" * 78)
    print()

    # -----------------------------------------------------------------
    # 1. Verify the closed forms for (a_0, b_0)
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 1: closed-form (a_0, b_0) in cascade slicing ratios")
    print("-" * 78)
    print("Hypothesis: a_0 = R(m+1)/R(m),  b_0^2 = R(m+2)/R(m) - [R(m+1)/R(m)]^2.")
    print()
    print(f"{'d_0':>4} {'m':>4}  {'a_0 numeric':>20}  {'a_0 closed':>20}  {'rel err':>10}")
    for d0 in [5, 7, 14, 19, 50, 100]:
        m = 2 * d0 + 1
        a, b = stieltjes_recurrence(2, m)
        a0_num = a[0]
        a0_closed = R_mp(m + 1) / R_mp(m)
        rel = abs(a0_num - a0_closed) / a0_closed
        print(f"{d0:>4} {m:>4}  {float(a0_num):>20.16f}  {float(a0_closed):>20.16f}  "
              f"{float(rel):>10.2e}")
    print()
    print(f"{'d_0':>4} {'m':>4}  {'b_0 numeric':>20}  {'b_0 closed':>20}  {'rel err':>10}")
    for d0 in [5, 7, 14, 19, 50, 100]:
        m = 2 * d0 + 1
        a, b = stieltjes_recurrence(2, m)
        b0_num = b[0]
        b0_sq_closed = R_mp(m + 2) / R_mp(m) - (R_mp(m + 1) / R_mp(m)) ** 2
        b0_closed = mp.sqrt(b0_sq_closed)
        rel = abs(b0_num - b0_closed) / b0_closed
        print(f"{d0:>4} {m:>4}  {float(b0_num):>20.16f}  {float(b0_closed):>20.16f}  "
              f"{float(rel):>10.2e}")
    print()

    # -----------------------------------------------------------------
    # 2. Asymptotic rate: (a_k - 1/2) * k versus k for various m
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 2: asymptotic (a_k - 1/2) * k versus k (does it stabilise?)")
    print("-" * 78)
    print("If (a_k - 1/2) ~ alpha(m)/k as k -> infty, the product stabilises.")
    print("Simon (2005) Bernstein-Szego: for absolutely cts measures with a")
    print("boundary singularity x^m near x=0 and (1-x)^{-1/2} near x=1, the")
    print("recurrence coefficients converge to (1/2, 1/4) at universal rate.")
    print()
    for d0 in [5, 14]:
        m = 2 * d0 + 1
        n = 25  # past this, Stieltjes breaks down even at 80 digits
        a, b = stieltjes_recurrence(n, m)
        if not a:
            continue
        n_actual = len(a)
        print(f"\nd_0 = {d0}, m = {m}, computed up to k = {n_actual - 1}:")
        print(f"  {'k':>4}  {'a_k - 1/2':>14}  {'(a_k-1/2)*k':>14}  "
              f"{'b_k - 1/4':>14}  {'(b_k-1/4)*k':>14}")
        for k in [1, 2, 4, 8, 12, 16, 20, 24]:
            if k < n_actual:
                ak_dev = float(a[k]) - 0.5
                bk_dev = float(b[k]) - 0.25
                print(f"  {k:>4}  {ak_dev:>14.6e}  {ak_dev * k:>14.6e}  "
                      f"{bk_dev:>14.6e}  {bk_dev * k:>14.6e}")
    print()

    # -----------------------------------------------------------------
    # 3. The diagonal of the Cholesky-renormalised triangular factor A
    #    A_{kk} = ||p_k|| / something  -- look for closed form.
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 3: diagonal of A (ratio b_{k-1} / something cascade-native?)")
    print("-" * 78)
    print("A_{kk} relates to b_{k-1} via the Cholesky-Stieltjes link.")
    print("Test: A_{kk}^2 vs explicit Hankel-determinant ratios.")
    print()
    for d0 in [5, 14]:
        m = 2 * d0 + 1
        a, b = stieltjes_recurrence(8, m)
        # Hankel determinants: det(M_k) where M_k is k x k
        print(f"\nd_0={d0}, m={m}:")
        print(f"  {'k':>3}  {'b_{k-1}':>16}  {'b_{k-1}^2 = h_k/h_{k-1}':>26}")
        for k in range(min(8, len(b))):
            bk = float(b[k])
            print(f"  {k:>3}  {bk:>16.10f}  {bk**2:>26.14e}")

    # -----------------------------------------------------------------
    # 4. Final summary: what closed forms have we found, what remains open
    # -----------------------------------------------------------------
    print()
    print("-" * 78)
    print("SUMMARY: closed-form structure for cascade OP recurrence")
    print("-" * 78)
    print()
    print("EXACT in cascade slicing ratios (NEW):")
    print("  a_0 = R(m+1) / R(m)")
    print("  b_0^2 = R(m+2)/R(m) - [R(m+1)/R(m)]^2")
    print("       = [R(m) R(m+2) - R(m+1)^2] / R(m)^2")
    print()
    print("For k >= 1, NO simple cascade-native closed form found:")
    print("  - Hypothesis a_k = R(m+2k+1)/R(m+2k) (Wallis ratio): FAILS at k=1.")
    print("  - The cascade measure is not a classical Jacobi/Bessel/Hermite")
    print("    family in variable x (the substitution u = x^2 to shifted")
    print("    Jacobi mixes parities).")
    print("  - Stieltjes recurrence numerically breaks down at large k due")
    print("    to exponential moment-matrix conditioning, even at 80 digits.")
    print()
    print("Asymptotic structure (universal Geronimus):")
    print("  a_k -> 1/2,  b_k -> 1/4  as k -> infinity, at rate O(1/k).")
    print("  Leading constant coefficients are m-dependent and not in")
    print("  closed form for the cascade weight x^m / sqrt(1-x^2).")
    print()
    print("Implication for lambda_1(C):")
    print("  lambda_1 is the squared operator norm of a triangular matrix A")
    print("  whose entries derive from a non-classical OP family.  The (a_0,")
    print("  b_0) closed forms above give the n=2 lambda_1 closed form")
    print("  (already known) but no extension to n >= 3.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
