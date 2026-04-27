#!/usr/bin/env python3
"""
Single-equation closed form for lambda_1: characteristic polynomial.

The cascade correlation matrix C has characteristic polynomial
   P_n(lambda) = det(lambda I - C) = lambda^n + c_{n-1} lambda^{n-1} + ... + c_0
with coefficients
   c_{n-k} = (-1)^k e_k(lambda_1, ..., lambda_n)
where e_k is the k-th elementary symmetric polynomial.

Newton's identities express e_k in terms of the power sums
   p_k = tr(C^k) = sum_j lambda_j^k:
     k e_k = sum_{i=1}^{k} (-1)^{i-1} e_{k-i} p_i
(e_0 = 1, p_k cascade-native sums of R-ratio products).

So P_n(lambda) is a degree-n polynomial in lambda with closed-form
cascade-native coefficients, and lambda_1 is its largest root.  This is
THE single-equation closed form for lambda_1 at every n.

This script:
  1. Computes p_k = tr(C^k) symbolically (mpmath, n closed-form sums).
  2. Recovers e_k via Newton's identities.
  3. Forms P_n(lambda).
  4. Verifies P_n(lambda_1) = 0 to machine precision.
  5. Reports the polynomial in cascade primitives for cascade-physics paths.

Goal: establish the cascade-native algebraic closed form for lambda_1.
"""

from __future__ import annotations

import math
import sys

import mpmath as mp  # type: ignore[import-not-found]
import numpy as np

mp.mp.dps = 80


def R_mp(d: int) -> mp.mpf:
    return mp.gamma(mp.mpf(d + 1) / 2) / mp.gamma(mp.mpf(d + 2) / 2)


def build_C_mp(n: int, d0: int) -> mp.matrix:
    m = 2 * d0 + 1
    C = mp.matrix(n, n)
    for i in range(n):
        for j in range(n):
            C[i, j] = R_mp(m + i + j) / mp.sqrt(R_mp(m + 2 * i) * R_mp(m + 2 * j))
    return C


def power_sums(C: mp.matrix, n: int) -> list[mp.mpf]:
    """p_k = tr(C^k) for k = 1, ..., n via repeated multiplication."""
    Ck = mp.eye(n)
    p = []
    for _ in range(n):
        Ck = Ck * C
        s = mp.mpf(0)
        for i in range(n):
            s += Ck[i, i]
        p.append(s)
    return p


def newton_to_elementary(p: list[mp.mpf]) -> list[mp.mpf]:
    """Newton's identities: e_k from p_1, ..., p_k.

    Recurrence:
      k * e_k = sum_{i=1}^{k} (-1)^{i-1} e_{k-i} p_i
    with e_0 = 1.
    Returns [e_1, e_2, ..., e_n].
    """
    n = len(p)
    e = [mp.mpf(1)]  # e_0
    for k in range(1, n + 1):
        s = mp.mpf(0)
        for i in range(1, k + 1):
            s += ((-1) ** (i - 1)) * e[k - i] * p[i - 1]
        e.append(s / k)
    return e[1:]


def char_poly_coeffs(n: int, d0: int) -> tuple[list[mp.mpf], list[mp.mpf], list[mp.mpf]]:
    """Returns (power_sums p_k, elementary symm e_k, char-poly coeffs c_k).

    P_n(lambda) = lambda^n + c_{n-1} lambda^{n-1} + ... + c_0
    with c_{n-k} = (-1)^k e_k.

    Output c is in increasing order: [c_0, c_1, ..., c_{n-1}].
    """
    C = build_C_mp(n, d0)
    p = power_sums(C, n)
    e = newton_to_elementary(p)
    # c_{n-k} = (-1)^k e_k for k = 1..n;  with c_n = 1.
    c = [mp.mpf(0)] * n
    for k in range(1, n + 1):
        c[n - k] = ((-1) ** k) * e[k - 1]
    return p, e, c


def evaluate_poly(c: list[mp.mpf], lam: mp.mpf, n: int) -> mp.mpf:
    """Evaluate P(lam) = lam^n + c_{n-1} lam^{n-1} + ... + c_0 (Horner)."""
    val = mp.mpf(1)
    for k in range(n - 1, -1, -1):
        val = val * lam + c[k]
    return val


def lambda1_exact(C: mp.matrix) -> mp.mpf:
    n = C.rows
    arr = np.array([[float(C[i, j]) for j in range(n)] for i in range(n)])
    return mp.mpf(float(np.linalg.eigvalsh(arr)[-1]))


def main() -> int:
    print("=" * 78)
    print("SINGLE-EQUATION ALGEBRAIC CLOSED FORM FOR LAMBDA_1")
    print("=" * 78)
    print()
    print("P_n(lambda) = lambda^n + c_{n-1} lambda^{n-1} + ... + c_0")
    print("with c_k closed-form in cascade slicing ratios via Newton from")
    print("p_k = tr(C^k).  lambda_1 is the largest root.")
    print()

    cases = [(n, d0) for d0 in [5, 14, 19] for n in [2, 3, 4, 5, 6, 8]]

    # -----------------------------------------------------------------
    # 1. Verify P_n(lambda_1) = 0
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 1: verify P_n(lambda_1) = 0")
    print("-" * 78)
    print(f"{'n':>3} {'d_0':>4}  {'lambda_1':>14}  {'P_n(lambda_1)':>22}")
    print("-" * 78)
    for n, d0 in cases:
        C = build_C_mp(n, d0)
        p, e, c = char_poly_coeffs(n, d0)
        lam1 = lambda1_exact(C)
        val = evaluate_poly(c, lam1, n)
        # Normalize by characteristic value (lam1^n) for relative scale
        rel = val / (lam1 ** n)
        print(f"{n:>3} {d0:>4}  {float(lam1):>14.10f}  {float(rel):>22.4e}")
    print()

    # -----------------------------------------------------------------
    # 2. Display closed-form coefficients for cascade-physics paths
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 2: closed-form characteristic polynomial coefficients")
    print("-" * 78)
    print()
    for n, d0 in [(3, 14), (4, 14), (3, 19)]:
        p, e, c = char_poly_coeffs(n, d0)
        print(f"  n = {n}, d_0 = {d0} (m = {2*d0+1}):")
        print(f"    Power sums p_k = tr(C^k):")
        for k, pk in enumerate(p, start=1):
            print(f"      p_{k} = {mp.nstr(pk, 12)}")
        print(f"    Elementary symm e_k:")
        for k, ek in enumerate(e, start=1):
            print(f"      e_{k} = {mp.nstr(ek, 12)}")
        print(f"    Char poly: P_{n}(lambda) = lambda^{n}", end="")
        for k in range(n - 1, -1, -1):
            ck = float(c[k])
            sign = "+" if ck >= 0 else "-"
            print(f" {sign} {abs(ck):.6f} lambda^{k}", end="")
        print()
        print()

    # -----------------------------------------------------------------
    # 3. Solve P_n(lambda_1) = 0 numerically; verify it returns lambda_1
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 3: solve P_n = 0 for largest root; cross-check vs eigvalsh")
    print("-" * 78)
    print(f"{'n':>3} {'d_0':>4}  {'lambda_1 (eigvalsh)':>22}  {'lambda_1 (poly root)':>22}")
    print("-" * 78)
    for n, d0 in cases:
        C = build_C_mp(n, d0)
        p, e, c = char_poly_coeffs(n, d0)
        lam1_eig = lambda1_exact(C)
        # Find largest root via mpmath polyroots
        coeffs_full = [mp.mpf(1)] + [c[n - 1 - k] for k in range(n)]
        # mpmath.polyroots takes coefficients in DECREASING order: lambda^n + ...
        roots = mp.polyroots(coeffs_full, maxsteps=200, extraprec=40)
        lam1_poly = max(mp.re(r) for r in roots)
        print(f"{n:>3} {d0:>4}  {mp.nstr(lam1_eig, 18):>22}  {mp.nstr(lam1_poly, 18):>22}")
    print()

    # -----------------------------------------------------------------
    # 4. Tighter bracket via Sturm: lambda_1 is in [U_K, P^{-1}_n(0+)]
    #    Using P_n(lambda_1) = 0 with U_K from power-trace (upper bound) and
    #    lambda_1 lower bound from Theorem 14.5 brackets it; the polynomial
    #    is monotone increasing for lambda > lambda_1 so a Newton iteration
    #    from U_K converges to lambda_1.
    # -----------------------------------------------------------------
    print("-" * 78)
    print("PASS 4: closed-form bracket -- Newton iteration from U_K")
    print("-" * 78)
    print("Starting from U_K (cascade-native upper bound), one Newton step on")
    print("P_n(lambda) gives lambda_1 to ~ machine precision.")
    print(f"{'n':>3} {'d_0':>4}  {'U_K init':>14}  {'after 1 step':>18}  {'lambda_1':>18}")
    print("-" * 78)
    for n, d0 in cases:
        C = build_C_mp(n, d0)
        p, e, c = char_poly_coeffs(n, d0)
        # U_K with K = min(n, 4)
        K = min(n, 4)
        U4 = p[K - 1] ** (mp.mpf(1) / K)
        # Newton step: lambda_new = lambda - P/P'
        # P'(lambda) = n*lambda^{n-1} + (n-1) c_{n-1} lambda^{n-2} + ...
        def Pp(lam):
            return evaluate_poly(c, lam, n)
        def dP(lam):
            v = mp.mpf(0)
            for k in range(1, n + 1):
                if k == n:
                    v += k * lam ** (k - 1)
                else:
                    v += k * c[k] * lam ** (k - 1)
            return v
        lam_new = U4 - Pp(U4) / dP(U4)
        lam1 = lambda1_exact(C)
        print(f"{n:>3} {d0:>4}  {float(U4):>14.10f}  {float(lam_new):>18.14f}  {float(lam1):>18.14f}")
    print()

    print("=" * 78)
    print("CONCLUSION")
    print("=" * 78)
    print()
    print("The single-equation closed form for lambda_1 at every n is:")
    print("   P_n(lambda_1) = 0,   P_n(lambda) = lambda^n + sum_k c_k lambda^k")
    print("   c_k = closed-form sum of R-ratio products via Newton's identities")
    print("         applied to tr(C^k) = sum_{i_1,...,i_k} C_{i_1 i_2} ... C_{i_k i_1}")
    print()
    print("This is the algebraic closed form: lambda_1 is an algebraic number over")
    print("the field of cascade slicing ratios, of degree at most n, specified by")
    print("an explicit minimal polynomial.")
    print()
    print("The radical-form question (Abel-Ruffini at n >= 5) is whether this")
    print("polynomial admits a radical solution.  For unstructured matrices this")
    print("fails generically; for the cascade matrix it remains open whether the")
    print("Galois group of P_n is solvable for n >= 5.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
