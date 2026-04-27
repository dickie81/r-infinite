#!/usr/bin/env python3
"""
Closed-form search for the dominant eigenvalue lambda_1 of the cascade
correlation matrix C_{ij} = R(d_i+d_j+1) / sqrt(R(2d_i+1) R(2d_j+1)).

Structural read: with consecutive layers d_i = d_0 + i and m = 2 d_0 + 1,
   C_{ij} = R(m+i+j) / sqrt(R(m+2i) R(m+2j))
        = <phi_i, phi_j> / (||phi_i|| ||phi_j||)
where phi_i(x) = x^i and the inner product is
   <f, g> = (2/sqrt(pi)) int_0^1 f(x) g(x) x^m / sqrt(1-x^2) dx.

So C is the Gram matrix of normalised monomials {x^i / ||x^i||}_{i=0..n-1}.

This script:
  1. Computes lambda_1 (and lambda_n = smallest) for various (n, d_0).
  2. Tests candidate closed forms:
       (a) lambda_1 = (1/n) sum_{i,j} C_{ij}   (Rayleigh at uniform vector)
       (b) lambda_1 = sum_i C_{0i}^2            (rank-1 surrogate)
       (c) lambda_1 = max_i (C row sum)
       (d) Stieltjes/Christoffel function values
  3. Inspects dominant eigenvector v_1: does it have a closed form
     v_1[i] = ||x^i||?   (i.e. v_1 ~ sqrt(diag M) up to normalisation)
  4. Reports the trace identity tr C = n (always exact) and
     tr C^2 = sum lambda_k^2 = ||C||_F^2.

If a closed form exists, the script will identify it within tolerance.
"""

from __future__ import annotations

import math
import sys

import numpy as np
from scipy.special import gammaln  # type: ignore[import-not-found]


def log_R(d: int) -> float:
    return float(gammaln((d + 1) / 2.0) - gammaln((d + 2) / 2.0))


def R(d: int) -> float:
    return math.exp(log_R(d))


def build_C(n: int, d0: int) -> np.ndarray:
    """Build the n x n cascade correlation matrix for layers d0, d0+1, ..., d0+n-1."""
    m = 2 * d0 + 1
    log_S = np.array([log_R(m + k) for k in range(2 * n)])  # k = 0..2n-1
    # M_{ij} = S_{i+j} = R(m + i + j)
    log_M = np.empty((n, n))
    for i in range(n):
        for j in range(n):
            log_M[i, j] = log_R(m + i + j)
    # D^2_{ii} = S_{2i} = R(m + 2i)
    log_D2 = np.array([log_R(m + 2 * i) for i in range(n)])
    log_C = log_M - 0.5 * (log_D2[:, None] + log_D2[None, :])
    return np.exp(log_C)


def candidate_uniform_rayleigh(C: np.ndarray) -> float:
    """Lower bound: Rayleigh quotient at uniform vector v = 1/sqrt(n)."""
    n = C.shape[0]
    return float(C.sum()) / n


def candidate_max_row_sum(C: np.ndarray) -> float:
    """Perron-like bound: max row sum (always >= lambda_1 for non-neg C? No: equals
    only for row-stochastic; here it's an upper bound by Perron-Frobenius? Actually
    rho(C) <= max row sum for non-negative C)."""
    return float(np.max(C.sum(axis=1)))


def candidate_diag_sqrt_eigenvector(C: np.ndarray, n: int, d0: int) -> tuple[float, float]:
    """Test eigenvector hypothesis: v_1[i] proportional to ||x^i|| = sqrt(R(m+2i)).

    Returns (Rayleigh value, residual ||Cv - lambda v||/||v||).
    """
    m = 2 * d0 + 1
    v = np.array([math.sqrt(R(m + 2 * i)) for i in range(n)])
    v /= np.linalg.norm(v)
    Cv = C @ v
    lam = float(v @ Cv)
    residual = float(np.linalg.norm(Cv - lam * v))
    return lam, residual


def candidate_polynomial_root(C: np.ndarray, n: int, d0: int) -> tuple[float, float]:
    """Test eigenvector hypothesis: v_1[i] = sqrt(M_{ii}) * a^i for some scalar a.

    This corresponds to the dominant eigenvector being a geometric sequence in the
    *scaled* basis. Find the best a numerically and report the Rayleigh + residual.
    """
    m = 2 * d0 + 1
    diag_sqrt = np.array([math.sqrt(R(m + 2 * i)) for i in range(n)])

    best_lam = -np.inf
    best_a = 1.0
    best_res = float("inf")
    for a in np.linspace(0.1, 10.0, 500):
        v = diag_sqrt * (a ** np.arange(n))
        v /= np.linalg.norm(v)
        Cv = C @ v
        lam = float(v @ Cv)
        if lam > best_lam:
            best_lam = lam
            best_a = float(a)
            best_res = float(np.linalg.norm(Cv - lam * v))
    return best_lam, best_res


def main() -> int:
    print("=" * 78)
    print("DOMINANT EIGENVALUE lambda_1 OF CASCADE CORRELATION MATRIX")
    print("=" * 78)
    print()
    print("Structural read: C is the Gram matrix of normalised monomials in")
    print("                 L^2([0,1], x^m / sqrt(1-x^2) dx),  m = 2 d_0 + 1.")
    print()

    cases = []
    for d0 in [5, 7, 14, 19]:
        for n in [2, 3, 4, 5, 6, 8, 10]:
            cases.append((n, d0))

    # -----------------------------------------------------------------
    # Pass 1: numerical eigendecomposition + uniform-Rayleigh comparison
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 1: lambda_1 vs uniform Rayleigh quotient (sum C_{ij}/n)")
    print("-" * 78)
    print(f"{'n':>3} {'d_0':>4}  {'lambda_1':>14}  {'uniform R':>14}  "
          f"{'gap':>10}  {'lambda_n':>14}")
    print("-" * 78)
    for n, d0 in cases:
        C = build_C(n, d0)
        eigs = np.linalg.eigvalsh(C)
        lam1, lamn = float(eigs[-1]), float(eigs[0])
        uniform = candidate_uniform_rayleigh(C)
        gap = lam1 - uniform
        print(f"{n:>3} {d0:>4}  {lam1:>14.10f}  {uniform:>14.10f}  "
              f"{gap:>10.3e}  {lamn:>14.10e}")
    print()
    print("Observation: uniform Rayleigh is a strict lower bound (gap > 0); not exact.")
    print()

    # -----------------------------------------------------------------
    # Pass 2: eigenvector structure — test diag-sqrt hypothesis
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 2: dominant eigenvector v_1 — test hypotheses")
    print("-" * 78)
    print("Hypothesis A: v_1[i] proportional to sqrt(R(m+2i)) = ||x^i||.")
    print(f"{'n':>3} {'d_0':>4}  {'lambda_1':>14}  {'R(diag sqrt)':>14}  {'residual':>10}")
    print("-" * 78)
    for n, d0 in cases:
        C = build_C(n, d0)
        eigs = np.linalg.eigvalsh(C)
        lam1 = float(eigs[-1])
        ray, res = candidate_diag_sqrt_eigenvector(C, n, d0)
        print(f"{n:>3} {d0:>4}  {lam1:>14.10f}  {ray:>14.10f}  {res:>10.3e}")
    print()

    # -----------------------------------------------------------------
    # Pass 3: actual eigenvector inspection
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 3: actual dominant eigenvector — pattern inspection")
    print("-" * 78)
    print("Print v_1[i] / sqrt(R(m+2i)) (the 'unscaled' coefficient).")
    print("If this is approximately a geometric sequence, lambda_1 admits a")
    print("polynomial-root closed form.")
    print()
    for n, d0 in [(4, 5), (4, 14), (4, 19), (6, 14), (8, 14), (10, 19)]:
        m = 2 * d0 + 1
        C = build_C(n, d0)
        eigvals, eigvecs = np.linalg.eigh(C)
        v1 = eigvecs[:, -1]
        if v1[0] < 0:
            v1 = -v1
        diag_sqrt = np.array([math.sqrt(R(m + 2 * i)) for i in range(n)])
        unscaled = v1 / diag_sqrt
        unscaled /= unscaled[0]
        print(f"  n={n}, d_0={d0}, m={m}, lambda_1={eigvals[-1]:.10f}")
        print(f"    v_1 / ||x^i|| (normalised to first=1): {np.array2string(unscaled, precision=6)}")
        # Test geometric-sequence: is unscaled[i+1]/unscaled[i] roughly constant?
        ratios = unscaled[1:] / unscaled[:-1]
        print(f"    ratios (unscaled[i+1]/unscaled[i]):    {np.array2string(ratios, precision=6)}")
        print()

    # -----------------------------------------------------------------
    # Pass 4: trace / Frobenius identities (always exact)
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 4: exact trace identities")
    print("-" * 78)
    print(f"{'n':>3} {'d_0':>4}  {'tr C':>14}  {'tr C^2':>14}  "
          f"{'sum lam':>14}  {'sum lam^2':>14}")
    print("-" * 78)
    for n, d0 in cases:
        C = build_C(n, d0)
        eigs = np.linalg.eigvalsh(C)
        tr1 = float(np.trace(C))
        tr2 = float(np.trace(C @ C))
        s1 = float(eigs.sum())
        s2 = float((eigs ** 2).sum())
        print(f"{n:>3} {d0:>4}  {tr1:>14.10f}  {tr2:>14.10f}  "
              f"{s1:>14.10f}  {s2:>14.10f}")
    print()
    print("tr C = n exactly (each diagonal is 1).")
    print("tr C^2 = sum_{i,j} C_{ij}^2 — a closed-form sum of R-ratios.")
    print()

    # -----------------------------------------------------------------
    # Pass 5: dominant-eigenvalue asymptotic n -> infinity, fixed d_0
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 5: lambda_1(n) asymptotics, fixed d_0 = 14")
    print("-" * 78)
    print(f"{'n':>4}  {'lambda_1':>14}  {'lambda_1/n':>14}  {'1 - lam_1/n':>14}")
    print("-" * 78)
    for n in [2, 5, 10, 20, 40, 80]:
        C = build_C(n, 14)
        eigs = np.linalg.eigvalsh(C)
        lam1 = float(eigs[-1])
        print(f"{n:>4}  {lam1:>14.10f}  {lam1/n:>14.10f}  {1 - lam1/n:>14.6e}")
    print()

    return 0


if __name__ == "__main__":
    sys.exit(main())
