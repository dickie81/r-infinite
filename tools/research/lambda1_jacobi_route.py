#!/usr/bin/env python3
"""
Closed-form route for lambda_1(C) via the orthogonal polynomial / moment-matrix
factorisation of the cascade correlation matrix.

Setup
-----
The cascade correlation matrix is the Gram matrix of normalised monomials
{x^i / ||x^i||}, i = 0..n-1, in L^2([0,1], dmu_m) with
   dmu_m(x) = x^m / sqrt(1-x^2) dx,    m = 2 d_0 + 1.

Moment matrix:  M_{ij} = <x^i, x^j>_{mu_m} = (sqrt(pi)/2) R(m + i + j).
Diagonal:       D_{ii} = ||x^i|| = sqrt(M_{ii}).
Correlation:    C = D^{-1} M D^{-1}.

Cholesky factorisation
----------------------
Since M is positive-definite Hankel, M = L L^T with L lower triangular.
Then C = (D^{-1} L)(D^{-1} L)^T = A A^T with A = D^{-1} L lower triangular.

So C has eigenvalues = (singular values of A)^2,
and  lambda_1(C) = sigma_1(A)^2 = ||A||_op^2.

The columns of A are the *orthonormal polynomials* p_k(x) for mu_m,
expressed in the normalised monomial basis x^i / ||x^i||:
   p_k(x) = sum_{i=0}^{k} A_{ik} (x^i / ||x^i||).
So A_{ik} = <p_k, x^i / ||x^i||> = <p_k, x^i>/||x^i||.

This script:
  1. Builds M and A = chol-from-Hankel via the Stieltjes / Lanczos recurrence
     applied to monomials in mu_m -- i.e. Gram-Schmidts {x^0, ..., x^{n-1}}.
  2. Verifies A A^T = C to machine precision.
  3. Computes sigma_1(A) and inspects the dominant singular vector.
  4. Tests two structural closed-form hypotheses:
       (a) Dominant singular vector of A in the OP basis is e_0
           => sigma_1^2 = ||first column of A||^2 = sum_i C_{0i}^2.
       (b) sigma_1^2 = max_k ||k-th column of A||^2 = max_k sum_i (T_{ik})^2.
  5. If neither is exact, reports the exact decomposition of the dominant
     singular vector for pattern detection.
"""

from __future__ import annotations

import math
import sys

import mpmath as mp  # type: ignore[import-not-found]
import numpy as np
from scipy.special import gammaln  # type: ignore[import-not-found]

mp.mp.dps = 60  # 60 decimal digits for ill-conditioned Hankel matrices


# ------------------------------------------------------------------ cascade primitives
def log_R(d: float) -> float:
    return float(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def R(d: float) -> float:
    return math.exp(log_R(d))


def R_mp(d: int) -> mp.mpf:
    """Cascade slicing ratio in mpmath arbitrary precision."""
    return mp.gamma(mp.mpf(d + 1) / 2) / mp.gamma(mp.mpf(d + 2) / 2)


# ------------------------------------------------------------------ moment matrix
def build_M(n: int, d0: int) -> np.ndarray:
    """Moment matrix M_{ij} = <x^i, x^j>_{mu_m} (up to constant sqrt(pi)/2)."""
    m = 2 * d0 + 1
    M = np.empty((n, n))
    for i in range(n):
        for j in range(n):
            M[i, j] = R(m + i + j)
    return M


def build_C_direct(n: int, d0: int) -> np.ndarray:
    M = build_M(n, d0)
    diag_sqrt = np.sqrt(np.diag(M))
    return M / np.outer(diag_sqrt, diag_sqrt)


# ------------------------------------------------------------------ orthogonal polynomials
def gram_schmidt_OP(n: int, d0: int) -> tuple[np.ndarray, np.ndarray]:
    """Build matrix A and OP coefficients via mpmath-precision Gram-Schmidt.

    Returns A (n x n) lower triangular with A_{ik} = <p_k, x^i / ||x^i||>
    and Q (n x n) lower triangular with p_k(x) = sum_l Q_{lk} x^l.

    Uses 60-digit precision throughout to handle the Hankel matrix's
    exponential ill-conditioning (cond ~ exp(c n) at large n).
    """
    m = 2 * d0 + 1
    # Moments in mpmath: M[i, j] = R(m + i + j)
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            M[i, j] = R_mp(m + i + j)
    diag_sqrt = [mp.sqrt(M[i, i]) for i in range(n)]

    Q = mp.matrix(n, n)
    for k in range(n):
        v = mp.matrix(n, 1)
        v[k] = mp.mpf(1)
        for j in range(k):
            inner = mp.mpf(0)
            for ell in range(j + 1):
                inner += Q[ell, j] * M[k, ell]
            for ell in range(n):
                v[ell] -= inner * Q[ell, j]
        # norm_sq = v^T M v
        norm_sq = mp.mpf(0)
        for ell in range(n):
            for ll in range(n):
                norm_sq += v[ell] * v[ll] * M[ell, ll]
        norm = mp.sqrt(norm_sq)
        for ell in range(n):
            Q[ell, k] = v[ell] / norm

    A = mp.matrix(n, n)
    for i in range(n):
        for k in range(n):
            s = mp.mpf(0)
            for ell in range(k + 1):
                s += Q[ell, k] * M[i, ell]
            A[i, k] = s / diag_sqrt[i]

    # Convert to numpy float64 for downstream SVD analysis (entries are O(1)).
    A_np = np.array([[float(A[i, k]) for k in range(n)] for i in range(n)])
    Q_np = np.array([[float(Q[i, k]) for k in range(n)] for i in range(n)])
    return A_np, Q_np


# ------------------------------------------------------------------ analysis
def main() -> int:
    print("=" * 78)
    print("LAMBDA_1 VIA ORTHOGONAL POLYNOMIALS / CHOLESKY OF MOMENT MATRIX")
    print("=" * 78)
    print()
    print("Measure on x in [0,1]:  dmu_m(x) = x^m / sqrt(1-x^2) dx,  m = 2 d_0 + 1.")
    print("Cascade correlation matrix C is the Gram matrix of {x^i / ||x^i||}.")
    print("C = A A^T with A = D^{-1} L (L = Cholesky of moment matrix M).")
    print()

    cases = [(n, d0) for d0 in [5, 14, 19] for n in [2, 3, 4, 6, 8]]

    # -----------------------------------------------------------------
    # 1. Verify A A^T = C
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 1: verify A A^T = C")
    print("-" * 78)
    print(f"{'n':>3} {'d_0':>4}  {'||A A^T - C||_F':>18}  {'cond(C)':>14}")
    print("-" * 78)
    for n, d0 in cases:
        A, _ = gram_schmidt_OP(n, d0)
        C = build_C_direct(n, d0)
        err = float(np.linalg.norm(A @ A.T - C, ord="fro"))
        cond = float(np.linalg.cond(C))
        print(f"{n:>3} {d0:>4}  {err:>18.3e}  {cond:>14.6e}")
    print()

    # -----------------------------------------------------------------
    # 2. Singular spectrum of A; lambda_1 = sigma_1^2
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 2: spectrum of A; verify sigma_k(A)^2 = lambda_k(C)")
    print("-" * 78)
    print(f"{'n':>3} {'d_0':>4}  {'sigma_1^2':>14}  {'lambda_1':>14}  "
          f"{'rel diff':>10}")
    print("-" * 78)
    for n, d0 in cases:
        A, _ = gram_schmidt_OP(n, d0)
        sigmas = np.linalg.svd(A, compute_uv=False)
        sigma1_sq = float(sigmas[0] ** 2)
        lam1 = float(np.linalg.eigvalsh(build_C_direct(n, d0))[-1])
        rel = abs(sigma1_sq - lam1) / lam1 if lam1 != 0 else float("nan")
        print(f"{n:>3} {d0:>4}  {sigma1_sq:>14.10f}  {lam1:>14.10f}  {rel:>10.3e}")
    print()

    # -----------------------------------------------------------------
    # 3. RIGHT singular vector of A in the OP basis
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 3: dominant right singular vector of A (in OP basis)")
    print("-" * 78)
    print("If this is close to e_0 = (1, 0, ..., 0), then sigma_1^2 = sum_i C_{0i}^2.")
    print()
    for n, d0 in [(4, 5), (4, 14), (6, 14), (8, 14), (10, 19), (8, 5)]:
        A, _ = gram_schmidt_OP(n, d0)
        U, S, Vt = np.linalg.svd(A)
        v_right = Vt[0]
        if v_right[0] < 0:
            v_right = -v_right
        print(f"  n={n}, d_0={d0}, sigma_1^2={S[0]**2:.10f}")
        print(f"    right SV in OP basis: {np.array2string(v_right, precision=4)}")
        # Test hypothesis (a)
        C = build_C_direct(n, d0)
        first_row_norm_sq = float(np.sum(C[0] ** 2))
        print(f"    sum_i C_{{0i}}^2 = ||first row||^2 = {first_row_norm_sq:.10f}")
        # Column norms of A
        col_norms_sq = (A ** 2).sum(axis=0)
        print(f"    column-norm^2 of A:   {np.array2string(col_norms_sq, precision=5)}")
        print(f"    max column-norm^2:    {col_norms_sq.max():.10f}")
        print()

    # -----------------------------------------------------------------
    # 4. Tightest hypothesis: column-norm bound vs sigma_1^2
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 4: column-norm closed-form lower bound, gap to sigma_1^2")
    print("-" * 78)
    print("max_k ||A e_k||^2 <= sigma_1(A)^2 (always).  Equality iff right SV = e_k.")
    print(f"{'n':>3} {'d_0':>4}  {'max ||col||^2':>18}  {'sigma_1^2':>14}  "
          f"{'gap':>12}  {'ratio':>10}")
    print("-" * 78)
    for n, d0 in cases:
        A, _ = gram_schmidt_OP(n, d0)
        col_max_sq = float((A ** 2).sum(axis=0).max())
        sigma1_sq = float(np.linalg.svd(A, compute_uv=False)[0] ** 2)
        gap = sigma1_sq - col_max_sq
        ratio = col_max_sq / sigma1_sq if sigma1_sq != 0 else float("nan")
        print(f"{n:>3} {d0:>4}  {col_max_sq:>18.12f}  {sigma1_sq:>14.10f}  "
              f"{gap:>12.4e}  {ratio:>10.6f}")
    print()

    # -----------------------------------------------------------------
    # 5. Closed form for sum_i C_{0i}^2 in cascade primitives
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 5: closed form for sum_i C_{0i}^2 (cascade-native)")
    print("-" * 78)
    print("C_{0i} = R(m + i) / sqrt(R(m) R(m + 2i))")
    print("sum_i C_{0i}^2 = sum_{i=0}^{n-1} R(m+i)^2 / [R(m) R(m+2i)]")
    print()
    print(f"{'n':>3} {'d_0':>4}  {'sum C_{0i}^2 closed':>22}  {'sum C_{0i}^2 numeric':>22}")
    print("-" * 78)
    for n, d0 in cases:
        m = 2 * d0 + 1
        # Closed form
        log_R_m = log_R(m)
        cf_sum = sum(
            math.exp(2 * log_R(m + i) - log_R_m - log_R(m + 2 * i))
            for i in range(n)
        )
        # Numeric
        C = build_C_direct(n, d0)
        num_sum = float(np.sum(C[0] ** 2))
        print(f"{n:>3} {d0:>4}  {cf_sum:>22.14e}  {num_sum:>22.14e}")
    print()

    # -----------------------------------------------------------------
    # 6. Final ratio table: how good is the closed-form lower bound?
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 6: lower bound from RIGHT-SV-near-e_0 hypothesis")
    print("-" * 78)
    print("Lower bound: lambda_1 >= sum_i C_{0i}^2  (Rayleigh at e_0 in OP basis).")
    print(f"{'n':>3} {'d_0':>4}  {'sum C_{0i}^2':>16}  {'lambda_1':>14}  "
          f"{'gap':>12}  {'ratio':>10}")
    print("-" * 78)
    for n, d0 in [(n, d0) for d0 in [5, 7, 14, 19] for n in [2, 4, 6, 8, 10, 20]]:
        m = 2 * d0 + 1
        log_R_m = log_R(m)
        cf_sum = sum(
            math.exp(2 * log_R(m + i) - log_R_m - log_R(m + 2 * i))
            for i in range(n)
        )
        lam1 = float(np.linalg.eigvalsh(build_C_direct(n, d0))[-1])
        gap = lam1 - cf_sum
        ratio = cf_sum / lam1 if lam1 != 0 else float("nan")
        print(f"{n:>3} {d0:>4}  {cf_sum:>16.10f}  {lam1:>14.10f}  "
              f"{gap:>12.4e}  {ratio:>10.6f}")
    print()

    return 0


if __name__ == "__main__":
    sys.exit(main())
