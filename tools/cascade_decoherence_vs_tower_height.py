#!/usr/bin/env python3
"""
Compute the eigenvalue deficit ε(N) of the Gram correlation matrix as a
function of tower truncation height N.

Used by Part VI §8.3 to give the time-dependent decoherence under the
tower-growth reading. At time t, the tower is [N_0, N(t)]; the Gram matrix
over the currently-existing layers has eigenvalue deficit ε(N(t)) that
monotonically grows from 0 (at N = N_0) to the saturated value
ε(217) = 6.11% identified in Paper II §8.6.

Outputs a table at checkpoints relevant to the pre-Big-Bang phase structure
(N = 5, 7, 19, 50, 100, 217) for both candidate initial truncation heights
N_0 = 4 and N_0 = 5.
"""

import numpy as np
from scipy.special import beta as B_func


def corr(d_i, d_j):
    """Normalised Gram entry: C_{ij} = G_{ij}/sqrt(G_{ii} G_{jj})
    with G_{ij} = B(1/2, (d_i + d_j)/2 + 1) (Paper 0 Supplement Thm 15.1)."""
    G_ii = B_func(0.5, d_i + 1.0)
    G_jj = B_func(0.5, d_j + 1.0)
    G_ij = B_func(0.5, (d_i + d_j) / 2.0 + 1.0)
    return G_ij / np.sqrt(G_ii * G_jj)


def epsilon_at(N_top, N_bot):
    """Eigenvalue deficit ε(N) = 1 - λ₁/n for the Gram matrix over
    layers [N_bot, N_top]."""
    dims = list(range(N_bot, N_top + 1))
    n = len(dims)
    if n < 2:
        return 0.0, n
    C = np.array([[corr(a, b) for b in dims] for a in dims])
    lam1 = np.linalg.eigvalsh(C).max()
    return 1.0 - lam1 / n, n


if __name__ == "__main__":
    print("=" * 72)
    print("ε(N): Gram eigenvalue deficit vs tower truncation height")
    print("=" * 72)

    checkpoints = [5, 6, 7, 10, 13, 19, 30, 50, 100, 150, 200, 217]

    for N_bot in [5, 4]:
        print(f"\nN_0 = {N_bot} (bottom of tower)")
        print("-" * 60)
        eps_full, _ = epsilon_at(217, N_bot=N_bot)
        print(f"{'N':>5}  {'n':>4}  {'ε(N)':>10}  {'ε (%)':>8}  {'fraction of saturated':>22}")
        print("-" * 60)
        for N in checkpoints:
            eps, n = epsilon_at(N, N_bot=N_bot)
            frac = (eps / eps_full * 100) if eps_full > 0 else 0
            print(f"{N:>5}  {n:>4}  {eps:>10.6f}  {eps*100:>8.4f}  {frac:>22.2f}%")

        print(f"\n  Saturated value (full path [N_0={N_bot}, 217]): "
              f"ε = {eps_full*100:.4f}%")

    # Summary at key cascade ticks for the Paper VI table
    print("\n\n" + "=" * 72)
    print("Paper VI §8.3 table (N_0 = 5, matches Paper II §8.6 saturation at 6.11%)")
    print("=" * 72)
    eps_217, _ = epsilon_at(217, N_bot=5)
    print(f"\n{'N':>5}  {'Layers':>8}  {'ε(N)':>10}  {'ε (%)':>8}  {'frac of ε(217)':>15}")
    print("-" * 60)
    for N in [7, 19, 50, 100, 217]:
        eps, n = epsilon_at(N, N_bot=5)
        frac = eps / eps_217 * 100
        print(f"{N:>5}  {n:>8}  {eps:>10.6f}  {eps*100:>8.4f}  {frac:>14.2f}%")
