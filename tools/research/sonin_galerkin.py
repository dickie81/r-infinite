#!/usr/bin/env python3
"""1bd instrument, the Sonin-Galerkin route (per C-M Theorem 1.6:
W_sa commutes with P_lambda AND the Fourier projection, so the
negative spectrum lives in the Sonin space S_lambda = {f : f = 0 on
J and fhat = 0 on J}). C-M's Fourier convention is e^{-2 pi i x xi};
its eigenfunctions are e_n(x) = (2pi)^{1/4} h_n(sqrt(2pi) x) with
F2 e_n = (-i)^n e_n, so both constraints are LINEAR point conditions
in that basis. Work in y = sqrt(2pi) x: J = [-lam, lam] in x becomes
|y| <= sqrt(2pi) lam, and
  W = -d/dx (lam^2 - x^2) d/dx + (2 pi lam)^2 x^2
    = d_y y^2 d_y + 2 pi lam^2 (y^2 - d_y^2),
with y^2 - d_y^2 = diag(2n+1) exactly (harmonic oscillator).
Construction: even-sector Hermites h_0, h_2, ..., h_{2(M-1)};
constraint rows = values of h_n and (-1)^{n/2} h_n on a J-grid; SVD
null space at tol -> Sonin basis; compress W; eigensolve; negative
eigenvalues xi -> s = 2 sqrt(-xi). Banked targets: dims ~268 at
1e-15 (basis size unknown -- scan); count of s <= 240 = 103;
Delta = 0.510 spacings; cal rms 0.32; smooth increments (resid sd
~0.012)."""
import numpy as np, math, json, sys, os
CKDIR = "/home/user/r-infinite/tools/research/checkpoints"


def hermite_rows(nmax, x):
    """Normalized Hermite functions h_0..h_nmax at points x, by the
    stable three-term recurrence (values are O(1); raw hermval +
    exp-rescue overflows past n ~ 300 and NaN-poisoned the SVD)."""
    H = np.zeros((nmax + 1, len(x)))
    H[0] = math.pi**-0.25*np.exp(-x*x/2)
    if nmax >= 1:
        H[1] = math.sqrt(2.0)*x*H[0]
    for n in range(1, nmax):
        H[n + 1] = math.sqrt(2.0/(n + 1))*x*H[n] - math.sqrt(n/(n + 1.0))*H[n - 1]
    return H


def build(lam, M, NJ, tol):
    ns = np.arange(0, 2*M, 2)
    yj = np.linspace(0, math.sqrt(2*math.pi)*lam, NJ)  # even: [0, sqrt(2pi) lam]
    Hx = hermite_rows(2*M - 2, yj)[ns]   # M x NJ: values of h_n(y) on J
    ph = np.array([(-1.0)**(n//2) for n in ns])  # F2 e_n = (-i)^n e_n; even n: (-1)^{n/2}
    Hf = Hx*ph[:, None]                  # values of fhat-constraint rows
    C = np.concatenate([Hx, Hf], axis=1).T   # (2 NJ) x M constraint matrix
    U, sv, Vt = np.linalg.svd(C, full_matrices=True)
    rank = int(np.sum(sv >= tol*sv[0]))
    B = Vt[rank:, :]                     # (M - rank) x M: Sonin basis coeffs
    # W = d_y y^2 d_y + 2 pi lam^2 diag(2n+1) in the h_n(y) basis:
    # ladders on an ambient space wide enough that the shift-<=4
    # products are exact for every retained index (max n = 2M-2
    # couples to 2M+2).
    # y h_n = sqrt((n+1)/2) h_{n+1} + sqrt(n/2) h_{n-1}
    # h_n' = sqrt(n/2) h_{n-1} - sqrt((n+1)/2) h_{n+1}
    dim = 2*M + 6
    Xm = np.zeros((dim, dim)); Dm = np.zeros((dim, dim))
    for n in range(dim - 1):
        c = math.sqrt((n + 1)/2)
        Xm[n + 1, n] = c; Xm[n, n + 1] = c
        Dm[n + 1, n] = -c; Dm[n, n + 1] = c
    # (Dm is antisymmetric, so Dm X^2 Dm is symmetric as required)
    Wfull = Dm @ (Xm @ Xm) @ Dm \
        + (2*math.pi*lam*lam)*np.diag(2*np.arange(dim) + 1.0)
    idx = list(ns)
    Wee = Wfull[np.ix_(idx, idx)]
    Wc = B @ Wee @ B.T
    Wc = (Wc + Wc.T)/2
    ev = np.linalg.eigvalsh(Wc)
    neg = np.sort(ev[ev < 0])
    s = np.sort(2*np.sqrt(-neg))
    return len(B), s, rank


if __name__ == "__main__":
    lam = float(sys.argv[1]) if len(sys.argv) > 1 else 2.0
    M = int(sys.argv[2]) if len(sys.argv) > 2 else 400
    NJ = int(sys.argv[3]) if len(sys.argv) > 3 else 80
    tol = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-13
    dims, s, rank = build(lam, M, NJ, tol)
    out = {"lam": lam, "M": M, "NJ": NJ, "tol": tol, "sonin_dim": dims,
           "rank": rank, "s": list(map(float, s[:200]))}
    json.dump(out, open(os.path.join(
        CKDIR, f"galerkin_lam{lam:g}_M{M}.json"), "w"), indent=0)
    print(f"lam={lam} M={M} NJ={NJ} tol={tol:g}: rank {rank}, Sonin dim {dims}; "
          f"s count <= 240: {int((s <= 240).sum())}; "
          f"first five: {np.round(s[:5], 3)}", flush=True)
