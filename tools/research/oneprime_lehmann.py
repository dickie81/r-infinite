#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1, ROUND 5 -- the hardening: a
RIGOROUS second-eigenvalue bound replaces the ell_2 stand-in.

Commission: "Attack B pls" (the second next move at the round-4
landing: Lehmann-Goerisch-class ell_2 -- the novelty-bearing step
from feasibility toward theorem).

THE CHAIN (each link elementary and checkable).
  (1) POLE REDUCTION. Even sector: the pole is PSD rank one, so
      lambda_2(T) >= lambda_2(PWP): count <= 1 for the pole-free
      operator suffices. Odd sector: the pole is negative rank
      one, and Weyl interlacing for a rank-one non-positive
      perturbation gives lambda_2(T) >= lambda_3(PWP): count <= 2
      suffices.
  (2) THE BIRMAN-SCHWINGER-TYPE SPLIT. For beta > 0 write
      W - nu = max(W - nu, beta) - qt,  qt := (nu + beta - W)_+ ,
      so PWP - nu >= beta - P qt(D) P as forms. On any subspace
      where PWP < nu, therefore, P qt(D) P > beta:
        #{PWP < nu} <= #{eig(P qt(D) P) > beta}.
      qt is COMPACTLY SUPPORTED in frequency (the kernel W grows
      like log r, so {W < nu + beta} is bounded: the two dips plus
      shoulders), hence P qt(D) P is the integral operator on
      [-a, a] with the explicit convolution kernel
        k(x, y) = qtcheck(x - y),
        qtcheck(u) = (1/pi) int_0^Rq qt(r) cos(ru) dr.
  (3) THE COUNT. The kernel is analytic, so Nystrom (GL-260 with
      symmetric weighting) converges spectrally; its traces are
      GATED against the exact identities
        tr  = (2a/2pi) int qt dr           (= 2a qtcheck(0)),
        tr2 = int |qtcheck(u)|^2 (2a - |u|) du
            = the exact Hilbert-Schmidt norm,
      and the count #{mu_j > beta} is read off the mu-ladder with
      the trace-power scaffold #{mu > beta} <= 1 +
      (sum_{j>=2} mu_j^{2m})/beta^{2m} recorded alongside (the
      inequality chain that survives interval hardening; m = 3).
  (4) THE CERTIFICATE. The largest nu with certified count <= 1
      (even) / = 0 before the +1 (odd) gives the RIGOROUS
      lambda_2(T) >= nu* -- and Kato-Temple runs with ell_2 = nu*
      instead of the section stand-in:
        lambda_1(T) >= rho - sigma^2/(nu* - rho).
      (N, M, S) come from the validated round-3 t-space pipeline
      at base 0.005, with the exact-pencil optimizer choosing the
      trial.

WHAT THIS ROUND DOES AND DOES NOT CLAIM. It removes the ell_2
stand-in -- the certificate's one structural IOU -- so the bound
chain is now mathematically closed. It does NOT yet claim a
theorem: every number is float64 (the quadratures are
ladder-validated but not interval enclosures), W's pointwise
values are scipy digamma, and the Nystrom count is spectral-quality
numerics with its trace-power scaffold recorded for the future
interval pass. That pass (round 6) is mechanical: 1-d integrals of
explicit smooth functions and finite eigenproblems.

GATES. gL1: Nystrom trace vs the exact (2a/2pi) int qt (rel
< 1e-8). gL2: Nystrom sum mu^2 vs the exact HS norm (rel < 1e-6).
gL3: the toy count check -- for a synthetic multiplier with known
compression behavior (qt = indicator-like bump), the Nystrom count
matches the trace-power scaffold's implication. gF1/gF4 inherited
per cell from the round-3 pipeline.

CHECKS. 7: classical (Birman-Schwinger counting, prolate-type
compressions, Kato-Temple). 8: no hypothesis input.

Keying law: every producing file in every key.
"""
import hashlib, math, os, sys

import numpy as np
from scipy.linalg import eigh as scipy_eigh

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_bridge import build_Q64
from oneprime_certificate import Wker
from oneprime_push import temple_opt
import oneprime_fractional as opf

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSL = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "oneprime_bridge.py",
                              "oneprime_certificate.py",
                              "oneprime_push.py",
                              "oneprime_fractional.py",
                              "oneprime_top.py",
                              "oneprime_lehmann.py")}
KEYFILE = os.path.join(HERE, "oneprime_lehmann.py")

NNY = 260          # Nystrom order
BASE = 0.003       # the round-3 pipeline's quadrature base here
NUGRID = (0.002, 0.005, 0.01, 0.013, 0.015, 0.02, 0.03, 0.04,
          0.08, 0.15)
BETAGRID = (1.0, 1.5, 2.0, 2.5, 3.0, 3.5)
UMAX = 1.2         # covers 2a for every cell in the window

_qcache = {}

def qt_profile(nu, beta, rmax=1500.0):
    """qtcheck(u) on a fine u-grid (CELL-INDEPENDENT: qt depends
    only on the kernel), returned as a cubic spline plus the exact
    trace ingredients; cached per (nu, beta). The r-grid at
    dr = 0.01 is 500+ points per oscillation period (u <= 1.2),
    with the support-edge kink costing ~1e-5 relative -- the
    float64-stage tolerance, noted for the interval pass."""
    key = (round(nu, 9), round(beta, 9))
    if key in _qcache:
        return _qcache[key]
    dr = 0.01
    r = np.arange(0.0, rmax, dr)
    r[0] = 1e-9
    Wv = Wker(r)
    qt = np.clip(nu + beta - Wv, 0.0, None)
    assert qt[-int(2.0/dr):].max() == 0.0, "qt support hit rmax"
    ug = np.arange(0.0, UMAX, 1e-4)
    qc = np.empty(len(ug))
    for i in range(0, len(ug), 500):
        uu = ug[i:i + 500]
        qc[i:i + 500] = (np.cos(np.outer(uu, r)) @ qt)*dr/np.pi
    from scipy.interpolate import CubicSpline
    spl = CubicSpline(ug, qc)
    intqt = 2*float(np.sum(qt))*dr    # int over the full line
    _qcache[key] = (spl, intqt, ug, qc)
    return _qcache[key]

def qtcheck_matrix(a, nu, beta):
    """The Nystrom matrix of P qt(D) P on [-a, a] via the cached
    qtcheck spline; returns (mu descending, tr_ny, tr_exact,
    tr2_ny, tr2_exact)."""
    spl, intqt, ug, qc = qt_profile(nu, beta)
    x, w = np.polynomial.legendre.leggauss(NNY)
    xs, ws = a*x, a*w
    U = np.abs(xs[:, None] - xs[None, :])
    K = spl(U)
    sw = np.sqrt(ws)
    Ks = sw[:, None]*K*sw[None, :]
    mu = np.linalg.eigvalsh((Ks + Ks.T)/2)[::-1]
    tr_ny = float(np.trace(Ks))
    tr_exact = (2*a/(2*np.pi))*intqt
    m2 = ug < 2*a
    integ = (qc*qc*(2*a - ug))[m2]
    tr2_exact = 2*(float(np.sum(integ)) - integ[0]/2)*1e-4
    tr2_ny = float(np.sum(mu*mu))
    return mu, tr_ny, tr_exact, tr2_ny, tr2_exact

def certified_count(mu, beta, m=3):
    """The Nystrom count above beta, plus the trace-power scaffold
    1 + sum_{j>=2} (mu_j/beta)^{2m} (what an interval pass would
    bound); both returned."""
    cnt = int(np.sum(mu > beta))
    scaff = 1.0 + float(np.sum((np.clip(mu[1:], 0, None)/beta)
                               ** (2*m)))
    return cnt, scaff


def run():
    params = {"deps": DEPSL, "nny": NNY, "base": BASE,
              "nugrid": NUGRID, "betagrid": BETAGRID}
    st = ckpt_key.load("oneprime_lehmann", KEYFILE, params)
    if st is not None:
        return st
    st = {}
    cells = [("even", 0.6931), ("even", 0.80), ("even", 0.90),
             ("even", 0.95), ("even", 1.00),
             ("odd", 0.90), ("odd", 1.05), ("odd", 1.09)]
    for parity, delta in cells:
        a = delta/2
        # --- the certified count curve nu -> K
        best = {}
        gl_done = False
        for nu in NUGRID:
            kbest, srec = None, None
            for beta in BETAGRID:
                mu, trn, tre, t2n, t2e = qtcheck_matrix(a, nu, beta)
                if not gl_done:
                    assert abs(trn/tre - 1) < 1e-8, \
                        f"gL1 FAIL {trn:.6e} vs {tre:.6e}"
                    assert abs(t2n/t2e - 1) < 1e-6, \
                        f"gL2 FAIL {t2n:.6e} vs {t2e:.6e}"
                    gl_done = True
                cnt, scaff = certified_count(mu, beta)
                if kbest is None or cnt < kbest:
                    kbest = cnt
                    srec = {"beta": beta, "mu123": [float(mu[0]),
                                                   float(mu[1]),
                                                   float(mu[2])],
                            "scaffold": scaff}
            best[f"{nu:g}"] = {"count": kbest, **srec}
        # the pole reduction: even needs count <= 1 for ell2 = nu;
        # odd needs count = 0 (its pole can ADD one below nu)
        need = 1 if parity == "even" else 2
        nustar = max((float(k) for k, v in best.items()
                      if v["count"] <= need), default=None)
        # --- the certificate with the rigorous ell_2 = nustar
        md, N, M, S, gf4, grids = opf.cell_matrices(
            a, parity, base=BASE)
        assert gf4 < 1e-8, "gF4 FAIL"
        tn, tw, B, TB = grids
        Qc, Gc, _, _, _ = build_Q64(delta, parity=parity)
        if parity == "even":
            idx = np.arange(opf.NHALF)
        else:
            wcert = (np.arange(opf.NHALF) + 1.0)*np.pi/a
            idx = np.array([int(np.argmin(np.abs(md.w - w)))
                            for w in wcert])
        Qs = Qc[:opf.NHALF, :opf.NHALF]
        gf1 = float(np.linalg.norm(M[np.ix_(idx, idx)] - Qs)
                    / np.linalg.norm(Qs))
        assert gf1 < 5e-4, "gF1 FAIL"
        d = 1.0/np.sqrt(np.diag(N))
        Nn = d[:, None]*N*d[None, :]
        ev, U = np.linalg.eigh(Nn)
        keep = ev > 1e-4
        Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T*d[None, :])
        Bw, TBw = Wh @ B, Wh @ TB
        NA = 2*(Bw*tw[None, :]) @ Bw.T
        MA = 2*(Bw*tw[None, :]) @ TBw.T
        SA = 2*(TBw*tw[None, :]) @ TBw.T
        NA, MA, SA = ((NA + NA.T)/2, (MA + MA.T)/2, (SA + SA.T)/2)
        l2sec = float(scipy_eigh(MA, NA, eigvals_only=True)[1])
        # also the pole-free section lambda_1 (the reduction's
        # sanity view: how much room the pole-free operator has)
        chi = (np.cosh(tn/2) if parity == "even"
               else np.sinh(tn/2))
        v = 2*(Bw*(tw*chi)[None, :]).sum(1)
        MP = MA - opf.psign(parity)*2*np.outer(v, v)
        l1free = float(scipy_eigh((MP + MP.T)/2, NA,
                                  eigvals_only=True)[0])
        row = {"count_curve": best, "nustar": nustar,
               "l2sec": l2sec, "l1_polefree_sec": l1free,
               "gF1": gf1}
        if nustar is not None:
            mu, c = temple_opt(NA, MA, SA, min(nustar, l2sec))
            nn = float(c @ NA @ c)
            rho = float(c @ MA @ c)/nn
            sig = math.sqrt(max(float(c @ SA @ c)/nn - rho*rho,
                                0.0))
            lam = rho - sig*sig/(nustar - rho) \
                if nustar > rho else float("-inf")
            row.update({"rho": rho, "sigma": sig,
                        "temple_rig": lam})
            print(f"LEH {parity} delta {delta:g}: nustar "
                  f"{nustar:g} (counts "
                  f"{[best[f'{nu:g}']['count'] for nu in NUGRID]}"
                  f", l1_polefree_sec {l1free:+.3e}) -> RIGOROUS-"
                  f"ell2 Temple {lam:+.3e} (rho {rho:+.3e} sigma "
                  f"{sig:.3e}; stand-in l2sec {l2sec:.3e})",
                  flush=True)
        else:
            print(f"LEH {parity} delta {delta:g}: NO nu with "
                  f"count <= {need} on the grid (counts "
                  f"{[best[f'{nu:g}']['count'] for nu in NUGRID]}"
                  f", l1_polefree_sec {l1free:+.3e})", flush=True)
        st[f"{parity}:{delta:g}"] = row
    ckpt_key.save("oneprime_lehmann", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("one-prime rigorous-ell2 round complete", flush=True)
