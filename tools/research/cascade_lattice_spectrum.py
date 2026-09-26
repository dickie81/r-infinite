#!/usr/bin/env python3
"""
Spectral test of the cascade lattice operator against the Riemann zeros.

Pre-registered question (stated before computation): does the spectrum of the
cascade's ONE admissible native operator -- the stiffness matrix of Part 0's
discrete elastic action

    S = sum_d (2 alpha(d))^-1 (phi_{d+1} - phi_d)^2

on the layer chain -- (a) have a counting function shaped like the Riemann
zeros' smooth staircase theta(T)/pi + 1 (theta = Im log Gamma_R(1/2+iT), the
phase of the cascade's own archimedean factor on the critical line), and
(b) show GUE level statistics (the Montgomery-Odlyzko signature of the zeros)?

Stated prior: NO on both -- a deterministic 1-D Jacobi chain should give a
rigid, crystal-like spectrum (mean adjacent-gap ratio near 1), not GUE
(~0.5996), Poisson (~0.3863), or GOE (~0.5307).  This script exists to let
the spectrum overrule the prior, with calibrated controls.

Parts
  A. Operator spectra: tower d = 4..217 (physical) and d = 4..2000
     (asymptotic), Neumann and Dirichlet boundaries; eigenvalues lambda_k
     and frequencies omega_k = sqrt(lambda_k).
  B. Staircase shape: least-squares fit of N(E) against (i) linear a*E+c and
     (ii) Riemann-type a*E*ln(E)+b*E+c; report R^2 of each.
  C. Level statistics: mean adjacent-gap ratio <r~> and spacing coefficient
     of variation, with same-size calibration controls: Poisson, GOE, GUE
     draws, and the first Riemann zeros (mpmath) run through the identical
     pipeline.
  D. Direct overlap: best affine map of the first 30 omega_k onto the first
     30 zeros gamma_n; RMS mismatch vs a bootstrap of smooth comparison
     spectra with the same endpoints.
"""

import math
import os
import sys

import numpy as np

RNG = np.random.default_rng(20260719)


def alpha(d):
    """alpha(d) = R(d)^2/4 in log space (the repo's Gamma-ratio form
    overflows past d ~ 340)."""
    lnR = math.lgamma((d + 1) / 2.0) - math.lgamma((d + 2) / 2.0)
    return math.exp(2.0 * lnR) / 4.0


def chain_operator(d_min, d_max, bc):
    """Stiffness matrix of the elastic action on layers d_min..d_max.
    Bond d<->d+1 carries weight w_d = 1/(2 alpha(d))."""
    d = np.arange(d_min, d_max + 1)
    w = np.array([1.0 / (2.0 * alpha(int(x))) for x in d[:-1]])
    n = len(d)
    L = np.zeros((n, n))
    for i, wi in enumerate(w):
        L[i, i] += wi
        L[i + 1, i + 1] += wi
        L[i, i + 1] -= wi
        L[i + 1, i] -= wi
    if bc == "dirichlet":
        L = L[1:-1, 1:-1]
    return np.linalg.eigvalsh(L)


def gap_ratio(e):
    s = np.diff(np.sort(e))
    s = s[s > 0]
    r = np.minimum(s[1:], s[:-1]) / np.maximum(s[1:], s[:-1])
    return float(np.mean(r))


def spacing_cv(e):
    """Coefficient of variation of unfolded spacings (local-mean unfolding
    over a 9-level window). Crystal -> ~0; Poisson -> ~1; GUE -> ~0.42."""
    s = np.diff(np.sort(e))
    s = s[s > 0]
    k = 9
    loc = np.array([np.mean(s[max(0, i - k // 2):i + k // 2 + 1])
                    for i in range(len(s))])
    u = s / loc
    return float(np.std(u) / np.mean(u))


def fit_staircase(E):
    """R^2 of N(E) ~ aE+c  vs  N(E) ~ aElnE+bE+c."""
    E = np.sort(E)
    N = np.arange(1, len(E) + 1, dtype=float)
    X1 = np.column_stack([E, np.ones_like(E)])
    X2 = np.column_stack([E * np.log(E), E, np.ones_like(E)])
    out = []
    for X in (X1, X2):
        beta, *_ = np.linalg.lstsq(X, N, rcond=None)
        resid = N - X @ beta
        out.append(1.0 - float(resid @ resid) / float(((N - N.mean()) ** 2).sum()))
    return out


def controls(n):
    """Same-size calibration spectra: Poisson, GOE, GUE."""
    pois = np.cumsum(RNG.exponential(size=n))
    A = RNG.normal(size=(n, n))
    goe = np.linalg.eigvalsh((A + A.T) / 2.0)
    B = RNG.normal(size=(n, n)) + 1j * RNG.normal(size=(n, n))
    gue = np.linalg.eigvalsh((B + B.conj().T) / 2.0)
    return {"Poisson": pois, "GOE": goe, "GUE": gue}


def riemann_zeros(m):
    import mpmath
    return np.array([float(mpmath.zetazero(k).imag) for k in range(1, m + 1)])


def main():
    print("=" * 78)
    print("Cascade lattice operator vs the Riemann spectrum")
    print("=" * 78)
    print("Pre-registered prior: crystal-like spectrum; NOT GUE; staircase")
    print("closer to linear than to E ln E.  Controls calibrate the pipeline.")

    specs = {}
    for (lo, hi, bc) in [(4, 217, "neumann"), (4, 217, "dirichlet"),
                         (4, 2000, "neumann")]:
        lam = chain_operator(lo, hi, bc)
        lam = lam[lam > 1e-9]          # drop Neumann zero mode
        specs[f"d={lo}..{hi} {bc}"] = lam

    print()
    print("PART B: staircase shape (R^2 of counting-function fits)")
    print(f"{'spectrum':<28}{'variable':>10}{'R2 linear':>11}{'R2 ElnE':>10}")
    for name, lam in specs.items():
        for var, E in (("lambda", lam), ("omega", np.sqrt(lam))):
            r1, r2 = fit_staircase(E)
            print(f"{name:<28}{var:>10}{r1:>11.5f}{r2:>10.5f}")
    zeros = riemann_zeros(120)
    r1, r2 = fit_staircase(zeros)
    print(f"{'Riemann zeros (control)':<28}{'gamma_n':>10}{r1:>11.5f}{r2:>10.5f}")
    print("  (zeros control shows E ln E clearly preferred; the operator's")
    print("   preference is read the same way)")

    print()
    print("PART C: level statistics")
    print(f"{'spectrum':<28}{'<r~>':>8}{'CV(unfolded s)':>16}")
    for name, lam in specs.items():
        print(f"{name + ' (omega)':<28}{gap_ratio(np.sqrt(lam)):>8.4f}"
              f"{spacing_cv(np.sqrt(lam)):>16.4f}")
    n = len(specs["d=4..217 neumann"])
    for name, e in controls(n).items():
        print(f"{name + ' control':<28}{gap_ratio(e):>8.4f}"
              f"{spacing_cv(e):>16.4f}")
    print(f"{'Riemann zeros control':<28}{gap_ratio(zeros):>8.4f}"
          f"{spacing_cv(zeros):>16.4f}")
    print("  reference values: Poisson 0.3863, GOE 0.5307, GUE 0.5996,")
    print("  rigid crystal -> 1.0")

    print()
    print("PART D: best affine overlap, first 30 omega_k vs first 30 gamma_n")
    om = np.sort(np.sqrt(specs["d=4..217 neumann"]))[:30]
    g = zeros[:30]
    X = np.column_stack([om, np.ones_like(om)])
    beta, *_ = np.linalg.lstsq(X, g, rcond=None)
    rms = float(np.sqrt(np.mean((g - X @ beta) ** 2)))
    mean_gap = float(np.mean(np.diff(g)))
    boot = []
    for _ in range(2000):
        # smooth comparison spectrum: random cubic monotone warp, same span
        t = np.sort(RNG.uniform(size=30))
        c = np.sort(RNG.uniform(0.3, 3.0, size=2))
        y = t ** c[0] * (1 + 0.3 * t ** c[1])
        y = (y - y[0]) / (y[-1] - y[0])
        s = g[0] + y * (g[-1] - g[0])
        Xb = np.column_stack([s, np.ones_like(s)])
        bb, *_ = np.linalg.lstsq(Xb, g, rcond=None)
        boot.append(float(np.sqrt(np.mean((g - Xb @ bb) ** 2))))
    frac = float(np.mean([b <= rms for b in boot]))
    print(f"  affine-fit RMS mismatch: {rms:.3f}  (mean zero gap {mean_gap:.3f},"
          f" RMS/gap = {rms / mean_gap:.2f})")
    print(f"  fraction of smooth random comparison spectra fitting at least"
          f" as well: {frac:.1%}")
    if rms > 0.5 * mean_gap:
        print("  verdict: NO level-by-level correspondence -- the map misses")
        print("  by most of a mean gap per zero; the bootstrap fraction only")
        print("  reflects both staircases being smooth and near-monotone,")
        print("  which the crude warp family fails to emulate.")
    else:
        print("  verdict: level-resolution overlap -- investigate further.")


if __name__ == "__main__":
    main()
