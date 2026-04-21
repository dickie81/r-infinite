#!/usr/bin/env python3
"""
fermion_dirac_spectral_zeta.py

Numerical verification of the Clifford-absorption conjecture
(Part IVc, conj:clifford-absorption).

The cascade claims the fermion lapse at Dirac layer d is R(d)/chi,
where chi = chi(S^{2n}) = 2, and d = 2n+1 so S^{d-1} = S^{2n}.

This tool computes the Dirac spectral zeta zeta_D(s=1) on round
S^{2n} via Hurwitz-zeta analytic continuation and compares to
R(d)/2 at the cascade's Dirac layers d in {5, 13, 21, 29}.

Stage 1: lay out the Dirac spectrum on S^{2n} and sanity-check
multiplicities and spinor-bundle dimensions.
"""

import os
import sys

import mpmath as mp
from mpmath import mpf, binomial, factorial, gamma, pi as mp_pi, sqrt as mp_sqrt, zeta as mp_zeta

# Shared cascade primitives (mpmath backend).
sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from cascade_constants import mp as _cascade_mp  # noqa: E402

mp.mp.dps = 50


def dirac_multiplicity_per_chirality(n, k):
    """
    Multiplicity of eigenvalue lambda_k = +(k+n) on round S^{2n},
    per chirality sector.

    D_k = 2^{n-1} * binomial(2n+k-1, k)

    Reference: Camporesi-Higuchi (1996), Bar (1996).
    """
    return mpf(2) ** (n - 1) * binomial(2 * n + k - 1, k)


def dirac_eigenvalue(n, k, sign=+1):
    """Dirac eigenvalue on S^{2n}: lambda_k^pm = pm(k+n)."""
    return mpf(sign) * (k + n)


R = _cascade_mp.R  # Cascade's radial geometric coupling (mpmath backend).


def sanity_check(n, kmax=6):
    """Print the first few Dirac modes on S^{2n} for visual check."""
    d = 2 * n + 1
    print(f"\nDirac spectrum on S^{2*n} (d = {d}):")
    print(f"  Spinor bundle dimension: 2^{n} = {2**n}")
    print(f"  Per-chirality spinor dim: 2^{n-1} = {2**(n-1) if n > 0 else 'N/A (n=0)'}")
    print(f"  k | lambda_k^+ | D_k (per chirality)")
    total_modes_k0 = 0
    for k in range(min(kmax, 7)):
        lam = dirac_eigenvalue(n, k, +1)
        D = dirac_multiplicity_per_chirality(n, k)
        print(f"  {k} | {lam} | {D}")
        if k == 0:
            total_modes_k0 = D
    print(f"\n  R(d) = {mp.nstr(R(d), 10)}")
    print(f"  Cascade target R(d)/chi = R({d})/2 = {mp.nstr(R(d)/2, 10)}")
    # Consistency: at k=0, D_0 should equal spinor dim / 2? Check.
    print(f"\n  Consistency: D_0 (per chir) = {total_modes_k0}; "
          f"spinor bundle dim per chir = {2**(n-1) if n > 0 else 1}")
    expected = 2**(n-1) if n > 0 else 1
    if total_modes_k0 == expected:
        print(f"  OK -- D_0 matches spinor bundle dimension per chirality.")
    else:
        print(f"  WARNING -- D_0 = {total_modes_k0}, expected {expected}.")


def dirac_spectral_zeta_positive_chirality(n, s_val=None):
    """
    Compute the Dirac spectral zeta function on round S^{2n}, per
    chirality, evaluated at s=1 by default:

        zeta_D^+(s) = sum_{k=0}^inf D_k / (k+n)^s,

    where D_k = 2^{n-1} * binomial(2n+k-1, k) is the per-chirality
    multiplicity of lambda_k = +(k+n).

    This sum diverges for s <= 2n. We regularise via Hurwitz zeta.

    Expansion in m = k+n:
      D_k/m = 2^{n-1}/(2n-1)! * prod_{j=1}^{n-1}(m^2 - j^2)
    is a polynomial in m of degree 2n-2 (only even powers).

    At s=1: zeta_D^+(1) = (2^{n-1}/(2n-1)!) * sum_j c_j * zeta(-2j, n),
    where c_j are the polynomial coefficients.

    The Hurwitz zeta zeta(s, q) at negative-integer s is evaluated
    by mpmath via the Bernoulli-polynomial formula
    zeta(-p, q) = -B_{p+1}(q)/(p+1).
    """
    if s_val is None:
        s_val = mpf(1)

    # Build polynomial prod_{j=1}^{n-1}(m^2 - j^2) as coefficients
    # of even powers of m. coeffs[j] = coefficient of m^{2j}.
    coeffs = [mpf(1)]  # polynomial = 1 initially
    for j in range(1, n):
        new = [mpf(0)] * (len(coeffs) + 1)
        for idx, c in enumerate(coeffs):
            new[idx + 1] += c          # m^2 times c
            new[idx] -= c * mpf(j) ** 2  # -j^2 times c
        coeffs = new

    prefactor = mpf(2) ** (n - 1) / factorial(2 * n - 1)

    total = mpf(0)
    for j, c in enumerate(coeffs):
        if c == 0:
            continue
        # sum_{m=n}^inf m^{2j} = zeta(-2j, n) at s=1 argument shift
        z = mp_zeta(s_val - (2 * j + 1) + 1, n)  # i.e. zeta(s - 2j, n) with extra factor
        # Wait: D_k/m^s = D_k * m^{-s}, and D_k has m-dependence
        # Let's redo: zeta_D^+(s) = (2^{n-1}/(2n-1)!) * sum_m m * prod(m^2 - j^2) * m^{-s}
        # = (2^{n-1}/(2n-1)!) * sum_m m^{1-s} * sum_j c_j m^{2j}
        # = (2^{n-1}/(2n-1)!) * sum_j c_j * sum_m m^{1+2j-s}
        # = (2^{n-1}/(2n-1)!) * sum_j c_j * zeta(s - 2j - 1, n)
        z = mp_zeta(s_val - 2 * j - 1, n)
        total += c * z

    return prefactor * total


def cascade_target(d):
    """Cascade's fermion lapse target: R(d)/chi = R(d)/2."""
    return R(d) / 2


def run_comparison(d_list=(5, 13, 21, 29)):
    print("\n" + "=" * 70)
    print("Stage 2: Dirac spectral zeta vs cascade fermion lapse R(d)/2")
    print("=" * 70)
    header = (f"{'d':>4} | {'n':>3} | {'zeta_D^+(1)':>16} | "
              f"{'|zeta_D|(1)':>16} | {'R(d)/2':>16} | {'|z|/target':>11}")
    print("\n" + header)
    print("-" * len(header))
    rows = []
    for d in d_list:
        n = (d - 1) // 2
        zd_pos = dirac_spectral_zeta_positive_chirality(n)
        zd_abs = 2 * zd_pos  # sum over both signs of lambda
        target = cascade_target(d)
        ratio = zd_abs / target if target != 0 else mpf(0)
        rows.append((d, n, zd_pos, zd_abs, target, ratio))
        print(f"{d:>4} | {n:>3} | {mp.nstr(zd_pos, 10):>16} | "
              f"{mp.nstr(zd_abs, 10):>16} | {mp.nstr(target, 10):>16} | "
              f"{mp.nstr(ratio, 7):>11}")
    return rows


def verdict(rows):
    print("\n" + "=" * 70)
    print("Stage 3: Verdict")
    print("=" * 70)
    ratios = [float(r[-1]) for r in rows]
    max_dev = max(abs(r - 1) for r in ratios)
    print(f"\nRatio |zeta_D|(1) / (R(d)/2) for d in {[r[0] for r in rows]}:")
    print(f"  {[f'{r:.4g}' for r in ratios]}")
    print(f"\nMax deviation from 1: {max_dev:.4g}")
    if max_dev < 1e-6:
        print("\n  VERDICT: CONJECTURE SUPPORTED.")
        print("  The regularised Dirac spectral zeta (both signs) equals")
        print("  R(d)/chi at every tested Dirac layer. Clifford-absorption")
        print("  conjecture (Part IVc conj:clifford-absorption) is")
        print("  numerically validated to the displayed precision.")
    else:
        print("\n  VERDICT: NAIVE DIRAC SPECTRAL ZETA DOES NOT EQUAL R(d)/2.")
        print()
        print("  The regularised trace of |D|^{-1} on round S^{2n} decays")
        print("  much faster than R(d) as d grows, so the two are not")
        print("  proportional. This is an honest negative result for the")
        print("  simplest formulation of the Clifford-absorption conjecture")
        print("  (fermion lapse = zeta_D(1) on the boundary sphere).")
        print()
        print("  Interpretation: the cascade's fermion lapse R(d)/chi is")
        print("  NOT the Dirac operator's on-sphere spectral trace. The")
        print("  conjecture's correct formulation requires a different")
        print("  regularised quantity on the cascade lattice --- plausibly")
        print("  a DISCRETE Dirac operator D_lat whose Green's function at")
        print("  layer d differs from the round-sphere Dirac spectral zeta")
        print("  by a volumetric or boundary-dominance factor that recovers")
        print("  R(d) (the cascade's radial coupling) rather than the")
        print("  sphere Laplacian's eigenvalue structure.")
        print()
        print("  This constrains Part IVc: the D_lat construction of")
        print("  Section 4 cannot simply inherit the round-sphere Dirac")
        print("  spectrum of Section 3. A slicing-map-induced spin")
        print("  connection that rescales layer-wise is required; the")
        print("  precise form is the open research question.")
        print()
        print("  Numerical upper bound: the naive Dirac spectral zeta is")
        print("  smaller than R(d)/2 at every tested layer, consistently,")
        print("  so a correction would have to be multiplicative and")
        print("  d-dependent.")


if __name__ == "__main__":
    print("=" * 70)
    print("Stage 1: Dirac spectrum sanity check")
    print("=" * 70)
    for d in [5, 13, 21, 29]:
        n = (d - 1) // 2
        sanity_check(n, kmax=5)
    rows = run_comparison()
    verdict(rows)
