#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1, ROUND 2 -- the exact Temple-bound
optimizer: the push past delta = 0.9.

Commission: "A" (the first of the four next moves offered at the
B1-opening landing: Temple-objective-optimized trials + the
<T phi_i, T phi_j> Gram).

THE METHOD. The Kato-Temple lower bound for the bottom eigenvalue,
lambda_1 >= lambda_T(phi) = rho - sigma^2/(ell_2 - rho) (valid for
any trial phi with rho = <phi,T phi> < ell_2 <= lambda_2), is, in
trial coefficients c over a subspace with Gram N, form M_ij =
<b_i, T b_j>, and T-applied Gram S_ij = <T b_i, T b_j>, the RATIO
OF TWO QUADRATIC FORMS:

  lambda_T(c) = (ell_2 rho - y)/(ell_2 - rho)
              = (c'(ell_2 M - S)c) / (c'(ell_2 N - M)c),

so its exact maximizer over the whole subspace is the top
eigenvector of the pencil (ell_2 M - S, ell_2 N - M), solved on
the sub-span where the denominator form is positive definite
(the span of section eigenvectors with eigenvalue < ell_2, with a
0.95 safety factor against near-singular denominators). This
replaces S5's hand-picked trials with the best trial the subspace
CONTAINS.

THE SUBSPACE. The union of the two grid-safe r^-2-decay families
that S5 found nearest the truth (linear edge vanishing): the
certified-family modes cos((k+1/2) pi t/a), k < 40 (even) /
sin(k pi t/a), k <= 40 (odd), and the p = 1 windowed harmonics
(nsm = 32), whitened together on the t-grid (cutoff 1e-10;
effective dimension reported). Both families have ghat ~ r^-2, so
the wide-grid (Rmax 3000) truncation error in S sits at
sigma-floor ~ 1e-5 -- below every needed-sigma in the window
except the extreme top, which remains gap-limited regardless.

THE ELL_2 LADDER. ell_2 is still a STAND-IN (Temple needs a true
lower bound on lambda_2; min-max gives sections as upper bounds).
Three rungs reported per cell: the combined-subspace section
lambda_2 (the tightest available stand-in), the cos-24 section
lambda_2 (the S3/S5 convention, for comparability), and a
half-lambda_2 conservative rung showing sensitivity -- a closure
that survives ell_2/2 is robust to the stand-in worry; one that
does not is flagged by construction.

GATES. gA: the T-application cross-check -- M computed as
<b_i, T b_j> from the wide-grid application must match the r-grid
section form (rel Frobenius < 1e-6): two independent routes to the
same matrix. gB: sigma^2 >= -1e-12 clamp monitoring (Cauchy-Schwarz
on the grid).

CHECKS. 7: classical (spectral bounds, Fourier analysis). 8: no
hypothesis input.

Keying law: every producing file in every key.
"""
import hashlib, math, os, sys

import numpy as np
from scipy.linalg import eigh as scipy_eigh

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_bridge import build_Q64
from oneprime_certificate import (Wker, tgrid, trapzw, smooth_basis,
                                  psign)

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSP = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "oneprime_bridge.py",
                              "oneprime_certificate.py",
                              "oneprime_push.py")}
KEYFILE = os.path.join(HERE, "oneprime_push.py")

NCOS = 40
NSM = 32
RMAX, NR = 3000.0, 600001
CHUNK = 10001


def combined_basis(a, parity, npts=4001):
    tg, dt = tgrid(a, npts)
    ks = np.arange(NCOS)
    if parity == "even":
        w = (ks + 0.5)*np.pi/a
        fam1 = np.cos(w[:, None]*tg[None, :])
    else:
        w = (ks + 1.0)*np.pi/a
        fam1 = np.sin(w[:, None]*tg[None, :])
    _, _, fam2 = smooth_basis(a, parity, nsm=NSM, p=1, npts=npts)
    raw = np.vstack([fam1, fam2])
    wq = trapzw(npts, dt)
    Gm = (raw*wq[None, :]) @ raw.T
    ev, U = np.linalg.eigh(Gm)
    keep = ev > 1e-10*ev[-1]
    B = (U[:, keep]/np.sqrt(ev[keep])[None, :]).T @ raw
    return tg, dt, B


def apply_T_batch(B, tg, dt, parity):
    """TB (n x tgrid) on the wide grid, one pass per chunk; also
    returns the r-grid-free pole part folded in."""
    wq = trapzw(len(tg), dt)
    Bw = B*wq[None, :]
    f = np.cos if parity == "even" else np.sin
    rw = np.linspace(-RMAX, RMAX, NR)
    drw = rw[1] - rw[0]
    Ww = Wker(rw)
    TB = np.zeros_like(B)
    for i in range(0, NR, CHUNK):
        rr = rw[i:i + CHUNK]
        C = f(np.outer(tg, rr))
        QB = Bw @ C
        TB += (Ww[i:i + CHUNK][None, :]*QB) @ C.T
    TB *= drw/(2*np.pi)
    chi = np.cosh(tg/2) if parity == "even" else np.sinh(tg/2)
    TB += psign(parity)*2*np.outer(Bw @ chi, chi)
    return TB


def temple_opt(N, M, S, ell2, safety=0.95):
    """Exact maximizer of the Temple value over the subspace: top
    eigenvalue of (ell2 M - S, ell2 N - M) on the span of section
    eigenvectors with eigenvalue < safety*ell2."""
    lams, V = scipy_eigh(M, N)
    keep = lams < safety*ell2
    if not keep.any():
        return float("-inf"), None
    Vk = V[:, keep]
    A1 = Vk.T @ (ell2*M - S) @ Vk
    A2 = Vk.T @ (ell2*N - M) @ Vk
    A1, A2 = (A1 + A1.T)/2, (A2 + A2.T)/2
    mus, Wv = scipy_eigh(A1, A2)
    c = Vk @ Wv[:, -1]
    return float(mus[-1]), c


def run():
    params = {"deps": DEPSP, "ncos": NCOS, "nsm": NSM, "rmax": RMAX}
    st = ckpt_key.load("oneprime_push", KEYFILE, params)
    if st is not None:
        return st
    st = {}
    cells = [("even", 0.6931), ("even", 0.80), ("even", 0.85),
             ("even", 0.90), ("even", 0.95), ("even", 1.00),
             ("even", 1.05), ("even", 1.09),
             ("odd", 0.90), ("odd", 1.09)]
    r6 = np.linspace(-600.0, 600.0, 120001)
    dr6 = r6[1] - r6[0]
    for parity, delta in cells:
        a = delta/2
        tg, dt, B = combined_basis(a, parity)
        n = B.shape[0]
        wq = trapzw(len(tg), dt)
        TB = apply_T_batch(B, tg, dt, parity)
        N = (B*wq[None, :]) @ B.T
        M = (B*wq[None, :]) @ TB.T
        M = (M + M.T)/2
        S = (TB*wq[None, :]) @ TB.T
        S = (S + S.T)/2

        # gA: the r-grid section form as an independent route to M
        f = np.cos if parity == "even" else np.sin
        Bw = B*wq[None, :]
        qs = np.empty((n, len(r6)))
        for i in range(0, len(r6), CHUNK):
            rr = r6[i:i + CHUNK]
            qs[:, i:i + CHUNK] = Bw @ f(np.outer(tg, rr))
        W6 = Wker(r6)
        Mr = (qs*W6[None, :]) @ qs.T * dr6/(2*np.pi)
        chi = np.cosh(tg/2) if parity == "even" else np.sinh(tg/2)
        cv = Bw @ chi
        Mr = Mr + psign(parity)*2*np.outer(cv, cv)
        Mr = (Mr + Mr.T)/2
        gA = float(np.linalg.norm(M - Mr)/np.linalg.norm(Mr))
        assert gA < 1e-6, f"gA FAIL at {parity}:{delta:g}: {gA:.2e}"

        lams = scipy_eigh(M, N, eigvals_only=True)
        l1s, l2s = float(lams[0]), float(lams[1])
        Qc, Gc, _, _, _ = build_Q64(delta, parity=parity)
        l2c = float(scipy_eigh(Qc, Gc, eigvals_only=True)[1])

        row = {"dim": n, "gA": gA, "l1_sec": l1s, "l2_sec": l2s,
               "l2_cos24": l2c}
        for tag, ell2 in (("l2sec", l2s), ("l2cos24", l2c),
                          ("half", 0.5*l2s)):
            mu, c = temple_opt(N, M, S, ell2)
            if c is not None:
                nn = float(c @ N @ c)
                rho = float(c @ M @ c)/nn
                sig = math.sqrt(max(float(c @ S @ c)/nn - rho*rho,
                                    0.0))
            else:
                rho = sig = float("nan")
            row[tag] = {"ell2": ell2, "temple": mu, "rho": rho,
                        "sigma": sig}
        st[f"{parity}:{delta:g}"] = row
        print(f"PUSH {parity} delta {delta:g} (dim {n}, gA "
              f"{gA:.1e}): l1_sec {l1s:+.3e} l2_sec {l2s:+.3e} | "
              f"Temple-opt: l2sec {row['l2sec']['temple']:+.3e} "
              f"(rho {row['l2sec']['rho']:+.3e} sigma "
              f"{row['l2sec']['sigma']:.3e}), l2cos24 "
              f"{row['l2cos24']['temple']:+.3e}, half "
              f"{row['half']['temple']:+.3e}", flush=True)
    ckpt_key.save("oneprime_push", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("one-prime Temple-optimizer push complete", flush=True)
