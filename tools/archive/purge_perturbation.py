#!/usr/bin/env python3
"""
Purge Part 0.0 of perturbation theory and compute the exact values.

Part 0.0 uses:
  (1) First-order perturbation theory (Thm 14.4) to get
      eps = 1 - lambda_1/n = (2/n^2) sum_{i<j} (1 - C_ij)
  (2) An adjacent-only first-order correction (Thm 14.8)
      delta Q/Q = sum_{k=0}^{n-2} (1 - C_{d_k, d_{k+1}}^2)
  (3) A per-observable coefficient k_Q, fitted individually.
  (4) A finite path of n layers (8 for most observables).

This script computes the exact Gram eigenvalues directly (no perturbation),
studies their scaling with n, and asks whether any parameter-free formula
reproduces the observed corrections.
"""

import numpy as np
from scipy.special import beta as Beta

def G(i, j):
    """Exact Gram matrix entry: B(1/2, (i+j)/2 + 1)."""
    return Beta(0.5, (i + j) / 2.0 + 1.0)

def correlation_matrix(D, N):
    """Normalised Gram (correlation) matrix for N consecutive layers from D."""
    M = np.array([[G(D + i, D + j) for j in range(N)] for i in range(N)])
    d = np.sqrt(np.diag(M))
    return M / np.outer(d, d)

def exact_eigenvalues(D, N):
    """Full eigenvalue spectrum of C, descending."""
    C = correlation_matrix(D, N)
    return np.linalg.eigvalsh(C)[::-1]

def adjacent_sum(D, M):
    """sum_{k=0}^{M-1} (1 - C_{D+k, D+k+1}^2)."""
    s = 0.0
    for k in range(M):
        num = G(D + k, D + k + 1)
        den = np.sqrt(G(D + k, D + k) * G(D + k + 1, D + k + 1))
        C = num / den
        s += 1.0 - C ** 2
    return s

def main():
    print("=" * 78)
    print("PURGE PART 0.0 OF PERTURBATION THEORY")
    print("=" * 78)

    # === 1. Reproduce paper numbers exactly ===
    print("\n[1] Paper numbers (D=5, N=8) reproduced exactly:")
    lam = exact_eigenvalues(5, 8)
    e = 1.0 - lam[0] / 8
    print(f"  lambda_1 exact = {lam[0]:.10f}")
    print(f"  epsilon exact  = {e:.10f}   (paper: 0.008159)")
    print(f"  epsilon pert.  = 0.008173 (paper's first-order perturbation)")
    print(f"  Difference     = {abs(e - 0.008173) / e * 100:.2f}%")
    print(f"  sum adj (1-C^2) = {adjacent_sum(5, 7):.10f}   (paper: 0.01186)")

    # === 2. Scaling with N — is there an infinite limit? ===
    print("\n[2] Scaling with N (fixed D=5):")
    print(f"  {'N':>5s} {'lambda_1':>13s} {'lambda_1/N':>13s} {'epsilon':>12s}"
          f" {'S_adj=sum(1-C2)':>18s} {'kQ=S_adj/eps':>14s}")
    for N in [4, 8, 16, 32, 64, 128, 256, 512]:
        lam = exact_eigenvalues(5, N)
        e = 1.0 - lam[0] / N
        s = adjacent_sum(5, N - 1)
        kQ = s / e if e > 0 else float('inf')
        print(f"  {N:>5d} {lam[0]:>13.8f} {lam[0]/N:>13.10f}"
              f" {e:>12.6e} {s:>18.10f} {kQ:>14.4f}")

    print("""
  Observation: k_Q is NOT a universal constant. It is strongly N-dependent.
  N=4:  k_Q ~ 2.44
  N=8:  k_Q ~ 1.45   <-- paper's choice
  N=16: k_Q ~ 0.90
  N=256: k_Q ~ 0.34
  The 'k_Q ~ 2' universality is an artefact of choosing N=8.""")

    # === 3. Infinite-path adjacent sum from each starting D ===
    print("\n[3] Infinite-path adjacent sum S_inf(D) = sum_{d=D}^inf (1-C_{d,d+1}^2):")
    for D in [5, 6, 14]:
        S_inf = adjacent_sum(D, 100_000)
        print(f"  D = {D:2d}:  S_inf = {S_inf:.8f}")

    # === 4. Observed corrections vs. infinite-path predictions ===
    print("\n[4] Observed corrections vs. infinite-path predictions:")
    print(f"  {'observable':<12s} {'D':>3s} {'delta_obs':>12s}"
          f" {'S_inf(D)':>12s} {'ratio':>10s} {'partial N matching delta':>28s}")
    cases = [
        ("alpha_s",     5, 0.1159, 0.1179),
        ("m_tau/m_mu",  6, 16.53,  16.82),
        ("m_mu/m_e",   14, 206.50, 206.77),
    ]
    for name, D, Q0, Qo in cases:
        delta = Qo / Q0 - 1
        S_inf = adjacent_sum(D, 100_000)
        # Find N_match: the partial path length where S first exceeds delta_obs
        s, N_match = 0.0, None
        for k in range(100_000):
            num = G(D + k, D + k + 1)
            den = np.sqrt(G(D + k, D + k) * G(D + k + 1, D + k + 1))
            s += 1.0 - (num / den) ** 2
            if s >= delta and N_match is None:
                N_match = k + 1
                break
        print(f"  {name:<12s} {D:>3d} {delta:>12.6e}"
              f" {S_inf:>12.8f} {S_inf/delta:>10.4f} {str(N_match):>28s}")

    # === 5. Is C near-banded? No — non-adjacent correlations dominate. ===
    print("\n[5] Off-diagonal structure of C for D=5, N=16:")
    C = correlation_matrix(5, 16)
    print("  First row, showing (1 - C^2) per column offset:")
    for j in range(16):
        print(f"    offset {j:2d}:  C = {C[0,j]:.6f}   1-C^2 = {1-C[0,j]**2:.6f}")
    print("""
  The 'adjacent only' approximation throws away most of the correlation
  content. Long-range pairs carry far more 1-C^2 than adjacent ones.""")

if __name__ == "__main__":
    main()
