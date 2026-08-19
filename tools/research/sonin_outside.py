#!/usr/bin/env python3
"""1bd instrument, outside-region Sonin compression (route 3).

The Sonin space S_lam = {f : f = 0 on J = [-lam, lam] and fhat = 0 on
J} (C-M Theorem 1.6; convention e^{-2 pi i x xi}). Support the basis
on the OUTSIDE region only -- normalized Legendre modes on [lam, X],
zero on J, even or odd reflection -- so f = 0 on J holds exactly, and
impose the single remaining constraint fhat = 0 on [0, lam] via an
SVD null space at tol:
  even: fhat(xi) = 2 int_lam^X f(x) cos(2 pi x xi) dx
  odd:  fhat(xi) = -2i int_lam^X f(x) sin(2 pi x xi) dx  (drop -2i)
Landau count: the constraint operator has effective rank ~ 2 lam
(X - lam), so K modes give a ~ (K - 2 lam (X-lam))-dim Sonin basis
(banked: 268 dims at 1e-15).

Compress the quadratic form of W = d/dx((x^2-lam^2) d/dx .) +
(2 pi lam)^2 x^2 (natural BCs; boundary terms dropped):
  <f, W g> = -int p f' g' + (2 pi lam)^2 int x^2 f g,  p = x^2-lam^2
onto the null basis; eigensolve; negative xi -> s = 2 sqrt(-xi).
Banked targets: merged (even+odd) count of s <= 240 = 103 (vs 102
zeros); Delta = 0.510 spacings; cal rms 0.32; increment resid ~0.012.
"""
import numpy as np, math, json, sys, os
CKDIR = "/home/user/r-infinite/tools/research/checkpoints"


def legendre_vals_ders(K, t):
    """P_0..P_{K-1} and dP/dt at points t, by recurrence."""
    P = np.zeros((K, len(t))); dP = np.zeros((K, len(t)))
    P[0] = 1.0
    if K > 1:
        P[1] = t
        dP[1] = 1.0
    for j in range(1, K - 1):
        P[j + 1] = ((2*j + 1)*t*P[j] - j*P[j - 1])/(j + 1)
        dP[j + 1] = dP[j - 1] + (2*j + 1)*P[j]
    return P, dP


def build(lam, K, X, NJ, tol, NQ, parity):
    tq, wq = np.polynomial.legendre.leggauss(NQ)
    half = (X - lam)/2
    xq = lam + half*(tq + 1)
    wx = wq*half
    P, dPdt = legendre_vals_ders(K, tq)
    nrm = np.sqrt((2*np.arange(K) + 1)/(2*half))   # L2([lam,X]) orthonormal
    Phi = P*nrm[:, None]                            # K x NQ values
    dPhi = dPdt*nrm[:, None]/half                   # d/dx
    xi = np.linspace(0, lam, NJ)
    osc = np.cos(2*math.pi*np.outer(xq, xi)) if parity == "even" \
        else np.sin(2*math.pi*np.outer(xq, xi))
    Fc = 2*(Phi*wx[None, :]) @ osc                  # K x NJ constraint matrix
    U, sv, Vt = np.linalg.svd(Fc.T, full_matrices=True)
    rank = int(np.sum(sv >= tol*sv[0]))
    B = Vt[rank:, :]                                # (K-rank) x K Sonin basis
    p = xq*xq - lam*lam
    q = (2*math.pi*lam)**2*xq*xq
    A = -(dPhi*(p*wx)[None, :]) @ dPhi.T + (Phi*(q*wx)[None, :]) @ Phi.T
    A = (A + A.T)/2
    Wc = B @ A @ B.T
    Wc = (Wc + Wc.T)/2
    ev = np.linalg.eigvalsh(Wc)
    neg = np.sort(ev[ev < 0])
    s = np.sort(2*np.sqrt(-neg))
    return len(B), rank, s


if __name__ == "__main__":
    lam = float(sys.argv[1]) if len(sys.argv) > 1 else math.sqrt(2)
    K = int(sys.argv[2]) if len(sys.argv) > 2 else 500
    X = float(sys.argv[3]) if len(sys.argv) > 3 else 40.0
    tol = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-15
    parity = sys.argv[5] if len(sys.argv) > 5 else "even"
    NJ = max(160, int(6*lam*X))   # xi-grid resolves the ~1/X kernel period
    NQ = max(1600, 4*K)
    dims, rank, s = build(lam, K, X, NJ, tol, NQ, parity)
    out = {"lam": lam, "K": K, "X": X, "NJ": NJ, "tol": tol, "NQ": NQ,
           "parity": parity, "sonin_dim": dims, "rank": rank,
           "s": list(map(float, s[:300]))}
    json.dump(out, open(os.path.join(
        CKDIR, f"outside_{parity}_lam{lam:.4f}_K{K}_X{X:g}.json"), "w"),
        indent=0)
    print(f"lam={lam:.4f} K={K} X={X:g} tol={tol:g} {parity}: rank {rank}, "
          f"Sonin dim {dims}; count s<=240: {int((s <= 240).sum())}; "
          f"first five: {np.round(s[:5], 3)}", flush=True)
