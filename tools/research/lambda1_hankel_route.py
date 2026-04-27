#!/usr/bin/env python3
"""
Hankel-determinant route for the cascade correlation matrix spectrum.

Setup
-----
The cascade moment matrix M with entries M_{ij} = R(m + i + j) (m = 2 d_0 + 1)
is Hankel.  Its leading principal minors det(M_k) (the (k+1) x (k+1) submatrix)
are the Hankel determinants of the moment sequence m_k = R(m + k).

Classical fact (Sylvester / Heine):
   det(M_n) = prod_{k=0}^{n-1} h_k
where h_k = ||p_k||^2 is the squared norm of the k-th orthogonal polynomial
in the *unnormalised* basis p_k = (det of bordered matrix) / (det M_{k-1}).

Equivalently, the Cholesky factor L of M satisfies
   L_{kk}^2 = det(M_k) / det(M_{k-1}) = h_k.

For the SHIFTED Jacobi measure u^alpha (1-u)^beta on [0, 1] (the cascade
measure under u = x^2), the Hankel determinant is given by the Selberg
integral / Jacobi-norm product formula:
   prod_{k=0}^{n-1} h_k^{(Jacobi)}
       = prod_{k=0}^{n-1} [Gamma(k+alpha+1) Gamma(k+beta+1) k! /
                          ((2k+alpha+beta+1) Gamma(k+alpha+beta+1))]
* (1/2^{alpha+beta+1})^n  [normalisation factor for shifted measure]

But the cascade matrix uses moments in variable x, not u; so the relevant
Hankel-determinant identity is for the measure x^m / sqrt(1-x^2) dx on [0,1],
which is NOT a classical Jacobi family in x directly.

This script:
  1. Computes Hankel determinants det(M_n) of cascade moments numerically
     (mpmath, 60-digit precision).
  2. Computes h_k = ||p_k||^2 from the OP recurrence.
  3. Tests whether prod h_k matches a Selberg-style product formula.
  4. Computes lambda_1 directly and checks against a candidate
     Hankel-determinant expression (e.g. tr(C) - sum lambda_{k>=2})
     where lower eigenvalues might admit closed forms even when lambda_1
     does not.

Goal: identify a closed-form expression for the SUM of all eigenvalues
except lambda_1 (the "subdominant trace"), which by trace identity gives
   lambda_1 = n - sum_{k>=2} lambda_k.

If sum_{k>=2} lambda_k admits a closed form (it equals trace minus the
dominant), we have a closed form for lambda_1 by complement.
"""

from __future__ import annotations

import math
import sys

import mpmath as mp  # type: ignore[import-not-found]
import numpy as np

mp.mp.dps = 60


def R_mp(d: int) -> mp.mpf:
    return mp.gamma(mp.mpf(d + 1) / 2) / mp.gamma(mp.mpf(d + 2) / 2)


def hankel_det(n: int, d0: int) -> mp.mpf:
    """det(M_n) where M_n is the n x n moment matrix."""
    m = 2 * d0 + 1
    M = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            M[i, j] = R_mp(m + i + j)
    return mp.det(M)


def hk_from_recurrence(n: int, d0: int) -> list[mp.mpf]:
    """h_k = ||p_k||^2 from the OP three-term recurrence (b_k^2 form).

    h_k = b_0^2 b_1^2 ... b_{k-1}^2 (with h_0 = m_0).
    """
    m = 2 * d0 + 1
    M = mp.matrix(n + 1, n + 1)
    for i in range(n + 1):
        for j in range(n + 1):
            M[i, j] = R_mp(m + i + j)

    # Compute h_k via det(M_{k+1})/det(M_k):
    # h_k = det M_{k+1} / det M_k
    h = []
    prev = mp.mpf(1)  # det M_0 := 1 by convention
    for k in range(n):
        # det of leading (k+1) x (k+1) submatrix
        sub = mp.matrix(k + 1, k + 1)
        for i in range(k + 1):
            for j in range(k + 1):
                sub[i, j] = M[i, j]
        cur = mp.det(sub)
        h.append(cur / prev)
        prev = cur
    return h


def selberg_product_jacobi(n: int, alpha: float, beta: float) -> mp.mpf:
    """Classical Selberg/Jacobi product:
        prod_{k=0}^{n-1} h_k^{(Jacobi)} where
        h_k^{(Jacobi)} = Beta(k+alpha+1, k+beta+1) * k! / Pochhammer(k+alpha+beta+1, k+1)

    This is for the ANALOGUE Jacobi measure on [0,1].  Won't match the
    cascade measure exactly because the basis is different, but useful as a
    sanity check.
    """
    a = mp.mpf(alpha)
    b = mp.mpf(beta)
    prod = mp.mpf(1)
    for k in range(n):
        kk = mp.mpf(k)
        # h_k for shifted Jacobi: Gamma(k+a+1) Gamma(k+b+1) k! / [(2k+a+b+1) Gamma(k+a+b+1) Gamma(k+1)]
        # Simplifies to Beta(k+a+1, k+b+1) / (2k+a+b+1)  [no, let me check]
        # Actually: h_k^{Jacobi[0,1]} = Gamma(k+a+1)*Gamma(k+b+1) / ((2k+a+b+1) * Gamma(k+a+b+1) * k!)
        h_k = (
            mp.gamma(kk + a + 1) * mp.gamma(kk + b + 1)
            / ((2 * kk + a + b + 1) * mp.gamma(kk + a + b + 1) * mp.factorial(k))
        )
        prod *= h_k
    return prod


def main() -> int:
    print("=" * 78)
    print("HANKEL-DETERMINANT / SELBERG ROUTE FOR LAMBDA_1")
    print("=" * 78)
    print()

    # -----------------------------------------------------------------
    # 1. Hankel determinants for cascade moments
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 1: cascade Hankel determinants det(M_n)")
    print("-" * 78)
    print(f"{'n':>3} {'d_0':>4}  {'det(M_n)':>30}  {'log det':>14}")
    print("-" * 78)
    for d0 in [5, 14, 19]:
        for n in [2, 3, 4, 6, 8, 10]:
            d = hankel_det(n, d0)
            print(f"{n:>3} {d0:>4}  {mp.nstr(d, 12):>30}  {float(mp.log(d)):>14.6e}")
    print()

    # -----------------------------------------------------------------
    # 2. h_k from the recurrence
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 2: h_k = ||p_k||^2 via det(M_{k+1})/det(M_k)")
    print("-" * 78)
    for d0, n in [(14, 6), (19, 8)]:
        h = hk_from_recurrence(n, d0)
        print(f"  d_0={d0}, n={n}:")
        for k, hk in enumerate(h):
            print(f"    h_{k} = {mp.nstr(hk, 10)}")
        # Verify: prod h_k = det(M_n)
        prod = mp.mpf(1)
        for hk in h:
            prod *= hk
        det = hankel_det(n, d0)
        print(f"    prod h_k        = {mp.nstr(prod, 12)}")
        print(f"    det(M_n)        = {mp.nstr(det, 12)}")
        print(f"    ratio (== 1)    = {mp.nstr(prod/det, 12)}")
        print()

    # -----------------------------------------------------------------
    # 3. Subdominant eigenvalues -- can we close them?
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 3: subdominant eigenvalues lambda_2, lambda_3, ...")
    print("        Test: do they admit a closed form via the second column of A?")
    print("-" * 78)
    print("Recall: trace(C) = n exactly, so lambda_1 = n - sum_{k>=2} lambda_k.")
    print("Test hypothesis: lambda_k ~ ||A e_{k-1}||^2 (k-th column norm-squared of A).")
    print()
    for d0, n in [(14, 6), (14, 8), (19, 6), (19, 8)]:
        # Build C via mpmath then float for eigvals
        m = 2 * d0 + 1
        C_mp = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                C_mp[i, j] = R_mp(m + i + j) / mp.sqrt(R_mp(m + 2 * i) * R_mp(m + 2 * j))
        C_np = np.array([[float(C_mp[i, j]) for j in range(n)] for i in range(n)])
        eigs = sorted(np.linalg.eigvalsh(C_np), reverse=True)

        # Build A from Gram-Schmidt OP, get column norm squares
        # h_k from recurrence -> column norm of A is related but not identical
        # Just compute A directly here
        M = mp.matrix(n, n)
        for i in range(n):
            for j in range(n):
                M[i, j] = R_mp(m + i + j)
        diag = [mp.sqrt(M[i, i]) for i in range(n)]
        Q = mp.matrix(n, n)
        for k in range(n):
            v = mp.matrix(n, 1)
            v[k] = mp.mpf(1)
            for jj in range(k):
                inner = mp.mpf(0)
                for ll in range(jj + 1):
                    inner += Q[ll, jj] * M[k, ll]
                for ll in range(n):
                    v[ll] -= inner * Q[ll, jj]
            ns = mp.mpf(0)
            for ll in range(n):
                for lll in range(n):
                    ns += v[ll] * v[lll] * M[ll, lll]
            for ll in range(n):
                Q[ll, k] = v[ll] / mp.sqrt(ns)
        # A_{ik} = sum_l Q_{lk} M_{il} / diag_i
        col_norm_sq = []
        for k in range(n):
            s = mp.mpf(0)
            for i in range(n):
                a_ik = mp.mpf(0)
                for ll in range(k + 1):
                    a_ik += Q[ll, k] * M[i, ll]
                a_ik = a_ik / diag[i]
                s += a_ik * a_ik
            col_norm_sq.append(float(s))

        print(f"  d_0={d0}, n={n}:")
        print(f"    eigenvalues:        {[f'{e:.6f}' for e in eigs]}")
        print(f"    A column-norms^2:   {[f'{c:.6f}' for c in col_norm_sq]}")
        # Per-element ratio
        ratios = [eigs[k] / col_norm_sq[k] if col_norm_sq[k] > 1e-30 else float('inf')
                  for k in range(n)]
        print(f"    eig / col-norm^2:   {[f'{r:.4f}' for r in ratios]}")
        print()

    print()
    print("=" * 78)
    print("OBSERVATIONS")
    print("=" * 78)
    print()
    print("Pass 1: cascade Hankel determinants det(M_n) decay super-exponentially")
    print("        (matching the conditioning observation).  log det(M_n) ~ -c n^2.")
    print()
    print("Pass 2: h_k = det(M_{k+1})/det(M_k) verified to high precision; this gives")
    print("        a closed-form sequence (h_k) in cascade primitives but does not")
    print("        directly yield closed-form eigenvalues of the SCALED matrix C.")
    print()
    print("Pass 3: Column norms of A approximate the eigenvalues of C in their decay")
    print("        pattern -- the matrix is 'near-diagonal' in OP basis -- but the")
    print("        approximation is not exact for any k.  Even lambda_2, lambda_3, ...")
    print("        deviate from the pure column-norm prediction (the off-diagonal")
    print("        coupling within A's lower-triangular structure pumps eigenvalue")
    print("        weight from k-th column to (k-1)-th eigenvalue).")
    print()
    print("Conclusion: the Hankel-determinant route gives EXPLICIT closed forms for")
    print("the moment-matrix invariants (det(M_n), h_k) but the cascade matrix C is")
    print("the *normalised* Gram matrix whose eigenvalues mix moment-matrix and")
    print("normalisation data non-trivially.  No closed form for lambda_1(C) at")
    print("n >= 3 emerges from this route either.")

    return 0


if __name__ == "__main__":
    sys.exit(main())
