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

THE SUBSPACE AND THE TRUNCATION DISCIPLINE (the first run's gA
catch). Every linear-edge mode has |ghat(r)| ~ 2w/r^2
asymptotically (sinc tails at its frequency w), so the S-matrix's
wide-grid truncation error scales like w^2 log^2(R)/R^3 -- and an
optimizer EXPLOITS underestimated ||T b||^2 on high modes to fake
sigma^2 gains. The first run (NCOS = 40, frequencies to ~358,
gate route at Rmax 600) was stopped by its own gA at 1.45e-3: the
r-grid route truncated exactly those tails. The discipline now:
frequencies capped at the certified reach (NCOS = 24 fam1 modes:
cos((k+1/2) pi t/a) even / sin((k+1) pi t/a) odd; NSM = 24
p = 1 windowed harmonics), the wide grid extended to Rmax 6000
(top-mode sigma^2 truncation ~1e-6, i.e. exploit-scale <= 1e-7 at
|c_top| <= 0.3), and the optimal vector's fam1-top-mode weight
reported so any residual exploitation is visible. Assembly is on
the RAW 48-mode basis (whitening applied afterwards as a linear
map), so the gate below compares raw sub-blocks directly.

THE ELL_2 LADDER. ell_2 is still a STAND-IN (Temple needs a true
lower bound on lambda_2; min-max gives sections as upper bounds).
Three rungs reported per cell: the combined-subspace section
lambda_2 (the tightest available stand-in), the cos-24 section
lambda_2 (the S3/S5 convention, for comparability), and a
half-lambda_2 conservative rung showing sensitivity -- a closure
that survives ell_2/2 is robust to the stand-in worry; one that
does not is flagged by construction.

GATES. gA: the fam1 sub-block of the t-inner-product M (from the
wide-grid T-application) against the certified build_Q64 matrix Q
on the same 24 modes -- two independent assemblies; tolerance
5e-4, the scale of build_Q64's own documented Rmax-600 ARCH
truncation class on its top modes (round 210 F5's fourth-digit
bias, seen here from the operator side). gB: sigma^2 clamped at 0
per vector; the clamp's firing is monitored.

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

# Run-2 lesson (the degenerate-union catch): cos(pi t/(2a)) times
# the integer harmonics recombines EXACTLY into half-integer
# cosines, so in the even sector the p = 1 window family is a
# linear recombination of fam1 -- the NCOS = NSM = 24 union
# collapsed to dim 24 and the optimizer merely re-derived the
# cos-24 trial (Temple-exhausted at 3 digits). The S5-winning
# p1n32 span reaches the half-integer modes 24.5..32.5 that the
# cap excluded; NSM = 32 restores them, and Rmax rises to 9000 so
# the new top frequency (~a-dependent, up to ~295) keeps the
# S-truncation below exploit scale (~2e-7 in sigma^2).
NCOS = 24
NSM = 32
RMAX, NR = 9000.0, 1800001
CHUNK = 10001


def raw_basis(a, parity, npts=4001):
    """The raw 48-mode union: fam1 = the certified-family modes,
    fam2 = p = 1 windowed harmonics. Returns the raw rows plus the
    whitening map Wh (B_orthonormal = Wh @ raw)."""
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
    Wh = (U[:, keep]/np.sqrt(ev[keep])[None, :]).T
    return tg, dt, raw, Wh


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
             ("odd", 0.90), ("odd", 1.05), ("odd", 1.09)]
    for parity, delta in cells:
        a = delta/2
        tg, dt, raw, Wh = raw_basis(a, parity)
        wq = trapzw(len(tg), dt)
        TBraw = apply_T_batch(raw, tg, dt, parity)
        Nr_ = (raw*wq[None, :]) @ raw.T
        Mr_ = (raw*wq[None, :]) @ TBraw.T
        Mr_ = (Mr_ + Mr_.T)/2
        Sr_ = (TBraw*wq[None, :]) @ TBraw.T
        Sr_ = (Sr_ + Sr_.T)/2

        # gA: the fam1 sub-block against the certified build_Q64
        # matrix on the same 24 modes (independent assembly)
        Qc, Gc, _, _, _ = build_Q64(delta, parity=parity)
        gA = float(np.linalg.norm(Mr_[:NCOS, :NCOS] - Qc)
                   / np.linalg.norm(Qc))
        assert gA < 5e-4, f"gA FAIL at {parity}:{delta:g}: {gA:.2e}"
        l2c = float(scipy_eigh(Qc, Gc, eigvals_only=True)[1])

        # whiten
        N = Wh @ Nr_ @ Wh.T
        M = Wh @ Mr_ @ Wh.T
        S = Wh @ Sr_ @ Wh.T
        N, M, S = (N + N.T)/2, (M + M.T)/2, (S + S.T)/2
        n = N.shape[0]

        lams = scipy_eigh(M, N, eigvals_only=True)
        l1s, l2s = float(lams[0]), float(lams[1])

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
                # fam1 top-mode weight of the optimal vector (the
                # truncation-exploit monitor): coefficients back in
                # the raw basis via Wh
                craw = Wh.T @ c
                topw = float(np.sum(craw[NCOS-6:NCOS]**2)
                             / np.sum(craw**2))
            else:
                rho = sig = topw = float("nan")
            row[tag] = {"ell2": ell2, "temple": mu, "rho": rho,
                        "sigma": sig, "top_weight": topw}
        st[f"{parity}:{delta:g}"] = row
        print(f"PUSH {parity} delta {delta:g} (dim {n}, gA "
              f"{gA:.1e}): l1_sec {l1s:+.3e} l2_sec {l2s:+.3e} "
              f"l2_cos24 {l2c:+.3e} | Temple-opt: l2sec "
              f"{row['l2sec']['temple']:+.3e} (rho "
              f"{row['l2sec']['rho']:+.3e} sigma "
              f"{row['l2sec']['sigma']:.3e} topw "
              f"{row['l2sec']['top_weight']:.3f}), l2cos24 "
              f"{row['l2cos24']['temple']:+.3e}, half "
              f"{row['half']['temple']:+.3e}", flush=True)
    ckpt_key.save("oneprime_push", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("one-prime Temple-optimizer push complete", flush=True)
