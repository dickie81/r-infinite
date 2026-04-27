#!/usr/bin/env python3
"""
Probe the three-term recurrence (Stieltjes / Jacobi matrix) of the OP family
for the cascade measure  dmu_m(x) = x^m / sqrt(1-x^2) dx  on  [0, 1].

Three-term recurrence (orthonormal):
   x p_k(x) = b_k p_{k+1}(x) + a_k p_k(x) + b_{k-1} p_{k-1}(x)
where (a_k, b_k) are the Jacobi-matrix entries.  In matrix form, the
restriction of multiplication-by-x to span{p_0, ..., p_{n-1}} is the
n x n tridiagonal symmetric Jacobi matrix
   J_n = tridiag(b_{k-1}, a_k, b_k).
The eigenvalues of J_n are the Gauss-quadrature nodes for mu_m.

This script:
  1. Uses Stieltjes' algorithm (mpmath, 60-digit precision) to compute
     (a_k, b_k) from the cascade moments  m_k = (sqrt(pi)/2) R(m+k).
  2. Looks for closed forms in (m, k):
       (a) Do (a_k, b_k) match Jacobi-matrix entries for the shifted
           Jacobi family in u = x^2 (so for some f(k), a_k = f_a(m, k),
           b_k = f_b(m, k))?
       (b) Asymptotic regime: as k -> infinity, do (a_k, b_k) approach
           the Chebyshev-of-the-first-kind limit (a -> 1/2, b -> 1/4)?
  3. Tests two candidate closed forms for a_k:
       (a) Jacobi formula for shifted Jacobi (alpha, beta) on [0,1]:
              a_k_jacobi = (alpha - beta) / ((2k + alpha + beta + 2)
                                            * (2k + alpha + beta))
                           + 1/2
       (b) Chebyshev limit a_k -> 1/2 as k -> infinity.
  4. Reports the relationship between Jacobi-matrix lambda_max and
     C-matrix lambda_max -- they are different operators on the same
     OP space (multiplication-by-x vs. Gram-of-normalised-monomials).
  5. Tests whether the cascade lambda_1 admits a closed form via the
     resolvent / Stieltjes transform of mu_m.

The Jacobi matrix J_n has known structure (it's the truncated
multiplication-by-x operator); the cascade matrix C has different
structure (it's the Gram of the renormalised dual basis).  We probe
whether they share spectral data.
"""

from __future__ import annotations

import math
import sys

import mpmath as mp  # type: ignore[import-not-found]
import numpy as np

mp.mp.dps = 60


def R_mp(d: int) -> mp.mpf:
    return mp.gamma(mp.mpf(d + 1) / 2) / mp.gamma(mp.mpf(d + 2) / 2)


def cascade_moment(k: int, m: int) -> mp.mpf:
    """m_k = (sqrt(pi)/2) R(m + k)."""
    return mp.sqrt(mp.pi) / 2 * R_mp(m + k)


def stieltjes_recurrence(n: int, m: int) -> tuple[list[mp.mpf], list[mp.mpf]]:
    """Stieltjes algorithm: compute (a_k, b_k) for k = 0, ..., n-1 from the
    moments via Gram-Schmidt-with-recurrence.

    Returns lists a (length n) and b (length n; b[-1] is past the end).
    """
    # Compute the polynomials p_k as coefficient vectors in the monomial basis.
    # The moments-only Stieltjes algorithm:
    #   p_{-1} = 0, p_0 = 1 / sqrt(m_0)
    #   x p_k = b_k p_{k+1} + a_k p_k + b_{k-1} p_{k-1}
    # We need <x p_k, p_k> = sum_{i,l} (p_k)_i (p_k)_l m_{i+l+1}
    #  and ||x p_k - a_k p_k - b_{k-1} p_{k-1}||^2.
    #
    # Coeffs as lists indexed 0..k.

    moments = [cascade_moment(k, m) for k in range(2 * n + 2)]

    a_list: list[mp.mpf] = []
    b_list: list[mp.mpf] = []

    p_prev = [mp.mpf(0)]  # zero polynomial
    p_curr = [mp.mpf(1) / mp.sqrt(moments[0])]  # p_0 = 1 / sqrt(m_0)
    b_prev = mp.mpf(0)  # convention: b_{-1} = 0

    for k in range(n):
        # a_k = <x p_k, p_k>
        a_k = mp.mpf(0)
        for i in range(len(p_curr)):
            for l in range(len(p_curr)):
                a_k += p_curr[i] * p_curr[l] * moments[i + l + 1]
        a_list.append(a_k)

        # Compute q = x p_k - a_k p_k - b_{k-1} p_{k-1}
        q = [mp.mpf(0)] * (len(p_curr) + 1)
        for i in range(len(p_curr)):
            q[i + 1] += p_curr[i]  # x p_k
            q[i] -= a_k * p_curr[i]  # -a_k p_k
        # extend p_prev to match length and subtract b_{k-1} p_{k-1}
        for i in range(len(p_prev)):
            q[i] -= b_prev * p_prev[i]

        # b_k = ||q|| = sqrt(<q, q>)
        norm_sq = mp.mpf(0)
        for i in range(len(q)):
            for l in range(len(q)):
                norm_sq += q[i] * q[l] * moments[i + l]
        b_k = mp.sqrt(norm_sq)
        b_list.append(b_k)

        # Update
        p_prev = p_curr
        p_curr = [qi / b_k for qi in q]
        b_prev = b_k

    return a_list, b_list


def main() -> int:
    print("=" * 78)
    print("STIELTJES / JACOBI-MATRIX COEFFICIENTS FOR cascade measure mu_m")
    print("=" * 78)
    print()
    print("Three-term recurrence: x p_k = b_k p_{k+1} + a_k p_k + b_{k-1} p_{k-1}")
    print("Probe: do (a_k, b_k) admit closed forms in (m, k)?")
    print()

    # -----------------------------------------------------------------
    # 1. Print (a_k, b_k) for small n, several m
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 1: numerical (a_k, b_k) for cascade-physics m = 2 d_0 + 1")
    print("-" * 78)
    for d0 in [5, 14, 19]:
        m = 2 * d0 + 1
        n = 12
        a, b = stieltjes_recurrence(n, m)
        print(f"\nd_0 = {d0},  m = {m}:")
        print(f"  {'k':>3}  {'a_k':>20}  {'b_k':>20}")
        for k in range(n):
            print(f"  {k:>3}  {float(a[k]):>20.14f}  {float(b[k]):>20.14f}")

    # -----------------------------------------------------------------
    # 2. Asymptotic check: for measure on [0, 1] with positive density at
    #    the boundary points, by Szego/Geronimus:
    #       a_k -> 1/2,  b_k -> 1/4  as k -> infinity.
    # -----------------------------------------------------------------
    print()
    print("-" * 78)
    print("PASS 2: Szego/Geronimus asymptotic check  (a_k -> 1/2, b_k -> 1/4)")
    print("-" * 78)
    for d0 in [5, 14, 19, 50]:
        m = 2 * d0 + 1
        n = 30
        a, b = stieltjes_recurrence(n, m)
        print(f"\nd_0 = {d0},  m = {m}:  (limits should be a -> 0.5, b -> 0.25)")
        print(f"  {'k':>4}  {'a_k - 0.5':>16}  {'b_k - 0.25':>16}")
        for k in [0, 1, 2, 4, 8, 12, 16, 20, 25, 29]:
            if k < n:
                ak_val = a[k]
                bk_val = b[k]
                # Detect numerical breakdown (negative norm sq -> complex)
                if isinstance(ak_val, mp.mpc) or isinstance(bk_val, mp.mpc):
                    print(f"  {k:>4}  [Stieltjes broke down at k={k}; precision exhausted]")
                    break
                print(f"  {k:>4}  {float(ak_val) - 0.5:>16.6e}  {float(bk_val) - 0.25:>16.6e}")

    # -----------------------------------------------------------------
    # 3. Compare cascade lambda_1(C) to spectral radius of the Jacobi matrix J_n
    # -----------------------------------------------------------------
    print()
    print("-" * 78)
    print("PASS 3: spectrum of the Jacobi matrix J_n (= mult-by-x truncated to deg<n)")
    print("-" * 78)
    print("Eigenvalues of J_n are Gauss-quadrature nodes for mu_m on [0,1].")
    print("They are NOT directly lambda_k(C) -- but compare for structural info.")
    print()
    print(f"{'n':>3} {'d_0':>4}  {'lambda_max(J_n)':>20}  {'lambda_1(C)':>14}")
    print("-" * 78)
    for d0 in [5, 14, 19]:
        m = 2 * d0 + 1
        for n in [4, 6, 8, 10]:
            a, b = stieltjes_recurrence(n, m)
            J = np.zeros((n, n))
            for k in range(n):
                J[k, k] = float(a[k])
                if k + 1 < n:
                    J[k, k + 1] = float(b[k])
                    J[k + 1, k] = float(b[k])
            lam_J = float(np.linalg.eigvalsh(J)[-1])

            # lambda_1(C) for comparison
            log_C = np.empty((n, n))
            for i in range(n):
                for j in range(n):
                    li = float(mp.log(R_mp(m + i + j)))
                    li -= 0.5 * float(mp.log(R_mp(m + 2 * i)))
                    li -= 0.5 * float(mp.log(R_mp(m + 2 * j)))
                    log_C[i, j] = li
            C = np.exp(log_C)
            lam_C = float(np.linalg.eigvalsh(C)[-1])
            print(f"{n:>3} {d0:>4}  {lam_J:>20.14f}  {lam_C:>14.10f}")
    print()

    # -----------------------------------------------------------------
    # 4. Test specific Jacobi-family closed-form for a_k
    #    For shifted Jacobi on [0,1] with weight u^alpha (1-u)^beta:
    #       a_k_in_u = ((beta^2 - alpha^2) / ((2k+alpha+beta) * (2k+alpha+beta+2))
    #                   + 1) / 2
    #    But our recurrence is in x, not u, so this is a similarity check.
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 4: compare a_k against shifted-Jacobi closed forms in u = x^2")
    print("-" * 78)
    print("If our OP recurrence in x were equivalent to shifted Jacobi in u,")
    print("we would have specific algebraic relations.  Test instead:")
    print("  a_k  vs  shifted Jacobi formula for u-recurrence at (alpha,beta)=((m-1)/2, -1/2)")
    print()
    for d0 in [5, 14, 19]:
        m = 2 * d0 + 1
        alpha = (m - 1) / 2.0
        beta = -0.5
        a, b = stieltjes_recurrence(8, m)
        print(f"\nd_0 = {d0},  m = {m}:")
        print(f"  {'k':>3}  {'a_k (cascade x)':>18}  {'a_k_jac u':>14}  {'ratio':>10}")
        for k in range(8):
            # Shifted Jacobi a_k for u^alpha (1-u)^beta on [0,1]:
            # a_k_jac = ((2k+alpha+beta+1)*(2k+alpha+beta+2)*0.5 +
            #            (alpha^2-beta^2)/(2*(2k+alpha+beta+2))) / (2k+alpha+beta+1)
            # Actually, simpler: for symmetric Jacobi parameters this is a standard
            # formula.  Use the most common form:
            denom1 = 2 * k + alpha + beta
            denom2 = 2 * k + alpha + beta + 2
            if denom1 == 0:
                a_jac = float("nan")
            else:
                a_jac = 0.5 + 0.5 * (beta ** 2 - alpha ** 2) / (denom1 * denom2)
            ratio = float(a[k]) / a_jac if a_jac != 0 else float("nan")
            print(f"  {k:>3}  {float(a[k]):>18.12f}  {a_jac:>14.6e}  {ratio:>10.6f}")
    print()

    # -----------------------------------------------------------------
    # 5. Test if (a_k, b_k) match the family for a specific simpler measure,
    #    e.g. Geronimus polynomials on [0, 1] with weight x^m sqrt(1-x^2)^{-1}.
    #    Look for pattern: a_k = (k + (m+1)/2) / (2k + m + 1)  (a guess)
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 5: ad hoc closed-form hypotheses for a_k")
    print("-" * 78)
    print("Testing whether (a_k, b_k) coincide with the Wallis-ratio family:")
    print("  hypothesis A: a_k = R(m + 2k + 1) / R(m + 2k)   (Wallis odd/even ratio)")
    print()
    for d0 in [5, 14, 19]:
        m = 2 * d0 + 1
        a, b = stieltjes_recurrence(8, m)
        print(f"\nd_0 = {d0},  m = {m}:")
        print(f"  {'k':>3}  {'a_k (numeric)':>18}  {'R(m+2k+1)/R(m+2k)':>22}  {'ratio':>10}")
        for k in range(8):
            hyp = float(R_mp(m + 2 * k + 1) / R_mp(m + 2 * k))
            ratio = float(a[k]) / hyp if hyp != 0 else float("nan")
            print(f"  {k:>3}  {float(a[k]):>18.12f}  {hyp:>22.14f}  {ratio:>10.6f}")
    print()

    # -----------------------------------------------------------------
    # 6. Hypothesis B: a_k as average of two adjacent R-ratios
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 6: hypothesis B for a_k  (average of two R-ratios)")
    print("-" * 78)
    print("  hypothesis B: a_k = (R(m+2k+1) + R(m+2k+3)/something) / 2")
    print("Numerically inspect: a_k - R(m+2k+1)/R(m+2k+something)")
    print()
    for d0 in [5, 14, 19]:
        m = 2 * d0 + 1
        a, b = stieltjes_recurrence(6, m)
        # Wallis ratios that bracket a_k
        for k in range(6):
            print(f"  d_0={d0}, k={k}, m={m}:")
            print(f"    a_k             = {float(a[k]):.12f}")
            print(f"    R(m+2k)         = {float(R_mp(m + 2*k)):.12f}")
            print(f"    R(m+2k+1)       = {float(R_mp(m + 2*k+1)):.12f}")
            print(f"    R(m+2k+2)       = {float(R_mp(m + 2*k+2)):.12f}")
            print(f"    R(m+2k+1)*R(m+2k+2)/R(m+2k) = {float(R_mp(m+2*k+1)*R_mp(m+2*k+2)/R_mp(m+2*k)):.12f}")

    return 0


if __name__ == "__main__":
    sys.exit(main())
