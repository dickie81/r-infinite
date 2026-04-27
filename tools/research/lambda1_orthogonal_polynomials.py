#!/usr/bin/env python3
"""
Study the orthogonal polynomials (OPs) for the cascade Gram measure

    d mu_m(x) = x^m / sqrt(1 - x^2) dx   on [0, 1]

where m = 2 d_0 + 1 indexes the cascade descent path starting at layer d_0.

Goal: determine whether the dominant eigenvalue lambda_1 of the cascade
correlation matrix C admits a closed form in the OP machinery (Jacobi
recurrence coefficients, Christoffel function, or shifted Jacobi
polynomial values).

Background:
  - C_{ij} = R(m+i+j) / sqrt(R(m+2i) R(m+2j)) is the Gram matrix of
    normalised monomials {x^i / ||x^i||} in L^2(mu_m).
  - Substituting t = x^2:  dmu_m = (1/2) t^{(m-1)/2} (1-t)^{-1/2} dt.
  - This is a Jacobi measure on [0,1] with (alpha, beta) = (-1/2, (m-1)/2)
    on the EVEN subspace of polynomials in x.
  - The full OP sequence in x interleaves even (Jacobi in t = x^2) and
    odd (x times Jacobi at shifted parameters) parts.

Computational pipeline (high precision, mpmath):
  1. Compute moments S_k = R(m+k) directly from log-Gamma.
  2. Hankel moment matrix M[i,j] = S_{i+j}.
  3. Cholesky M = L L^T  =>  L_{ij} = inner product structure of OPs.
  4. Read Jacobi recurrence (a_k, b_k) from L (or from Stieltjes).
  5. Compare to Jacobi(alpha=-1/2, beta=(m-1)/2) recurrence on the
     even subspace; check whether odd-indexed coefficients match a
     shifted Jacobi pattern.
  6. Compute lambda_1(C) and check candidate closed forms:
       (a) Christoffel function K_n(1) at the right endpoint.
       (b) p_n(1)^2 (squared Jacobi value at 1).
       (c) sum_{k} p_k(1)^2 / ||p_k||^2  (inverse Christoffel).
"""

from __future__ import annotations

import math
import sys
from typing import List

import numpy as np
from mpmath import mp, mpf, gammaprod, sqrt as msqrt, fabs as mfabs

mp.dps = 60  # 60 decimal digits


def R_mp(d: int):
    """Cascade slicing ratio R(d) = Gamma((d+1)/2) / Gamma((d+2)/2) at high precision."""
    return gammaprod([mpf(d + 1) / 2], [mpf(d + 2) / 2])


def cascade_moments(m: int, K: int) -> List:
    """Moment sequence S_k = (sqrt(pi)/2) * <x^k, 1>_{mu_m} = R(m+k).

    Up to overall constant; only ratios matter for OPs.
    """
    return [R_mp(m + k) for k in range(K)]


def ops_and_jacobi(moments: List) -> tuple[List[List], List, List]:
    """Construct monic OPs from moments via Stieltjes / Cholesky-equivalent.

    Returns (P, alphas, betas) where:
      P[k] = list of coefficients of monic p_k(x) (degree k),
      alphas[k] = recurrence coefficient a_k (also called b_k in some texts),
      betas[k] = squared norm ||p_k||^2 / ||p_{k-1}||^2  (a.k.a. b_k^2).

    Three-term recurrence (monic):
       p_0 = 1
       p_1 = x - alpha_0
       p_{k+1} = (x - alpha_k) p_k - beta_k p_{k-1}
    """
    K = len(moments)
    # Hankel matrix H[i,j] = moments[i+j]
    n = K // 2  # max OP degree we can compute
    P: List[List] = []
    alphas: List = []
    betas: List = []
    norm_sq: List = []  # ||p_k||^2

    # p_0 = 1
    P.append([mpf(1)])
    norm_sq.append(moments[0])  # = <1, 1>

    if n < 1:
        return P, alphas, betas
    # alpha_0 = <x p_0, p_0> / <p_0, p_0> = moments[1] / moments[0]
    alpha0 = moments[1] / moments[0]
    alphas.append(alpha0)
    # p_1 = x - alpha_0
    P.append([-alpha0, mpf(1)])
    # ||p_1||^2 = <p_1, p_1>
    np1 = inner_via_moments(P[1], P[1], moments)
    norm_sq.append(np1)
    betas.append(np1 / norm_sq[0])

    for k in range(1, n - 1):
        # x * p_k
        xp_k = [mpf(0)] + P[k]
        # alpha_k = <x p_k, p_k> / <p_k, p_k>
        ak = inner_via_moments(xp_k, P[k], moments) / norm_sq[k]
        alphas.append(ak)
        # p_{k+1} = (x - alpha_k) p_k - beta_k p_{k-1}
        # = x p_k - alpha_k p_k - beta_k p_{k-1}
        bk = betas[k - 1]  # we already have it; recompute via norm
        # Actually beta_k = ||p_k||^2 / ||p_{k-1}||^2
        bk = norm_sq[k] / norm_sq[k - 1]
        # Wait: convention is p_{k+1} = (x - a_k) p_k - b_k p_{k-1}
        # with b_k = ||p_k||^2 / ||p_{k-1}||^2
        next_p = poly_sub(poly_sub(xp_k, poly_scale(P[k], ak)), poly_scale(P[k - 1], bk))
        P.append(next_p)
        norm_next = inner_via_moments(next_p, next_p, moments)
        norm_sq.append(norm_next)
        betas.append(norm_next / norm_sq[k])

    return P, alphas, norm_sq


def poly_scale(p: List, c) -> List:
    return [c * a for a in p]


def poly_sub(p: List, q: List) -> List:
    n = max(len(p), len(q))
    pp = p + [mpf(0)] * (n - len(p))
    qq = q + [mpf(0)] * (n - len(q))
    return [a - b for a, b in zip(pp, qq)]


def inner_via_moments(p: List, q: List, moments: List):
    """<p, q> = sum_{i, j} p_i q_j moments[i+j]."""
    s = mpf(0)
    for i, pi in enumerate(p):
        if pi == 0:
            continue
        for j, qj in enumerate(q):
            if qj == 0:
                continue
            if i + j >= len(moments):
                continue
            s += pi * qj * moments[i + j]
    return s


def evaluate_poly(p: List, x):
    s = mpf(0)
    for k, c in enumerate(p):
        s += c * (mpf(x) ** k)
    return s


def report(d0: int, n: int) -> None:
    m = 2 * d0 + 1
    K = 2 * n + 4
    moments = cascade_moments(m, K)
    P, alphas, norm_sq = ops_and_jacobi(moments)

    print(f"\n--- d_0 = {d0}, m = 2 d_0 + 1 = {m}, max degree = {len(P) - 1} ---")
    print()
    print("Recurrence coefficients (monic OPs):")
    print(f"  {'k':>3}  {'alpha_k':>22}  {'beta_k = ||p_k||^2/||p_{k-1}||^2':>40}")
    for k, ak in enumerate(alphas):
        bk = norm_sq[k + 1] / norm_sq[k]
        print(f"  {k:>3}  {mp.nstr(ak, 16):>22}  {mp.nstr(bk, 16):>40}")
    print()

    # Compare alpha_k to shifted Jacobi (-1/2, (m-1)/2) recurrence.
    # For shifted Jacobi Q_k^{(alpha, beta)} on [0,1] with weight t^beta (1-t)^alpha:
    # standard recurrence (consult Szego). We'll instead compute it directly on the
    # even subspace and compare patterns.
    print("Conjectured connection: even-indexed OPs (degree 2k) should be")
    print("related to shifted Jacobi P_k^(alpha=-1/2, beta=(m-1)/2)(2 x^2 - 1).")
    print()

    # Check: p_2(x) = x^2 - alpha_0' = ?  on the even subspace, t = x^2.
    # Let's verify this directly.
    # Even-subspace inner product: <f(t), g(t)>_t = (1/2) int_0^1 f(t) g(t) t^{(m-1)/2} (1-t)^{-1/2} dt
    # First even OP is q_0 = 1.
    # Second even OP is q_1(t) = t - <t, 1>/<1,1>.
    # In x: p_2(x) = x^2 - c.
    # Compare to alpha_1 from the FULL OP sequence; they're not the same because
    # the full OPs see odd functions too.

    # Numerically: build the cascade correlation matrix C and find lambda_1.
    log_R_seq = [float(mp.log(R_mp(m + k))) for k in range(2 * n)]
    log_M = np.empty((n, n))
    for i in range(n):
        for j in range(n):
            log_M[i, j] = float(mp.log(moments[i + j]))
    log_d2 = np.array([float(mp.log(moments[2 * i])) for i in range(n)])
    log_C = log_M - 0.5 * (log_d2[:, None] + log_d2[None, :])
    C = np.exp(log_C)
    eigs = np.linalg.eigvalsh(C)
    print(f"lambda_1(C) (numerical, n = {n}): {float(eigs[-1]):.12f}")

    # Closed-form candidates from OPs:

    # Candidate 1: lambda_1 = sum_k (||p_k||^2 of monomial expansion) -- this is just
    # tr(C) = n, already known.

    # Candidate 2: Christoffel function value. K_n(x_*) = sum_k p_k(x_*)^2 / ||p_k||^2.
    # The min of 1/K_n over [0,1] gives min_x of sum p_k(x)^2/||p_k||^2.
    # For cascade C, the dominant mode peaks at x = 1 (the right endpoint) where all
    # monomials are aligned. So evaluate at x = 1.
    K_n_at_1 = mpf(0)
    for k in range(len(P)):
        if k > n - 1:
            break
        pk_at_1 = evaluate_poly(P[k], 1)
        K_n_at_1 += pk_at_1 ** 2 / norm_sq[k]

    # The reciprocal of K_n(x*) is the Christoffel function lambda_n(x*)
    # In Gram-matrix terms: min_v ||v|| s.t. v(x*) = 1 has lambda^2 = 1/K_n(x*).
    # Connection to lambda_1: not direct, but let's see.
    print(f"sum_k p_k(1)^2 / ||p_k||^2 (K_n at 1): {mp.nstr(K_n_at_1, 12)}")
    print(f"1 / K_n(1):                            {mp.nstr(1 / K_n_at_1, 12)}")
    print(f"Compare lambda_1 = {float(eigs[-1]):.10f}, n - lambda_1 = {n - float(eigs[-1]):.6e}")

    # Candidate 3: Largest eigenvalue of normalised moment matrix vs OP norms ratio.
    # Worth tabulating ||p_k||^2 / S_{2k} = product of (1 - alignment factors).
    print()
    print("Diagonal alignment factor: ||p_k||^2 / S_{2k} (closer to 1 = orthogonal-like)")
    for k in range(min(len(norm_sq), n)):
        S_2k = moments[2 * k]
        ratio = norm_sq[k] / S_2k
        print(f"  k={k}: ||p_k||^2 / S_{{{2*k}}} = {mp.nstr(ratio, 12)}")


def main() -> int:
    print("=" * 78)
    print("ORTHOGONAL POLYNOMIALS FOR THE CASCADE GRAM MEASURE mu_m")
    print("=" * 78)
    print("Measure: d mu_m(x) = x^m / sqrt(1 - x^2) dx on [0, 1], m = 2 d_0 + 1.")
    print("Goal: closed form for lambda_1(C) via OP machinery.")

    # First do small cases for clarity, then a larger n to test asymptotic
    for d0 in [5, 14, 19]:
        report(d0, n=6)
    report(d0=14, n=10)
    return 0


if __name__ == "__main__":
    sys.exit(main())
