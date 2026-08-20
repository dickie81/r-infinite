#!/usr/bin/env python3
"""The asymptote attack (commissioned after the ratio attack's
deflation): does an INSTRUMENT-INVARIANT beta/p exist as c -> inf,
and is it pi^2/4 = 2.467?

What the ratio attack broke, and this instrument fixes:
  - the plunge rate was basis-truncation-conditioned (the standard
    n = N_sh + 4 clips a ~20-mode plunge; +8 modes moved p +42%).
    Here every section carries extra = 28 modes past N_sh, with an
    explicit convergence control at c = 120 (extra = 8/16/28).
  - the log-lambda curve is CONVEX (the fall steepens beyond the
    plunge -- super-geometric deep tail), so "the plunge rate" is
    only defined over a stated decade-window. The estimator of
    record MATCHES windows: both slopes over the same decades --
    the climb fitted on m in (1e-11, 1e-2), the spectrum fitted on
    lambda in (1e-11, 1e-2); the shallow (1e-4, 0.5) and deep
    (1e-11, 1e-6) fits quantify the convexity as a systematic.
  - beta's recipe sensitivity: tau0 step 5, both count regressors
    (the integer in-band count and the continuous expected count
    nbar = (2c/A) ln(tau0/2pi)/(2pi)).
The c-ladder: 60, 120, 170, 240, 340 (2.8x beyond the certified
pair); ratio(c) extrapolated in 1/ln c with the spread band;
verdict: pi^2/4 inside or outside.

Check 7: Slepian spectra, finite eigenproblems -- classical.
Check 8: no hypothesis input. Keying per A355: DEPS = this file +
the substrates; params carry (c, extra, windows, grid).

RESULT (run complete): PI^2/4 IS EXCLUDED; there is no
instrument-invariant asymptote.

  E0 (convergence control, c = 120): p_matched converges at
     extra = 16 (0.7894, bit-stable to extra = 28) -- the
     CONVERGED matched-window plunge rate is 62% HIGHER than the
     standard-basis 0.486 that fed the ratio-2.4 reading. The
     convexity is intrinsic even when converged: shallow 0.594 /
     matched 0.789 / deep 0.837 (+-17% by window choice) -- the
     log-lambda fall steepens through the plunge, so any single
     "plunge rate" carries a stated-window qualifier forever.
  E1 (the converged, matched-window ladder): ratio(c) =
     1.02/1.98 (c=60; the integer regressor spans too few counts
     there -- unreliable), 1.70/1.88 (120), 1.68/1.70 (170),
     1.43/1.68 (240) [beta_int/beta_con against p_matched].
     The measured band for c >= 120 is 1.4-1.9, trending if
     anywhere DOWNWARD with c; pi^2/4 = 2.467 lies far outside.
     The earlier apparent drift toward 2.44 was entirely the
     truncated-basis artifact (the clipped p inflated the ratio).
     c = 340 produced no in-window climb points (all margins
     below the 1e-15 guard -- the numerical eigenvalue floor at
     n = 245; not load-bearing, noted).

NET: the asymptote question closes by exclusion. No version of
beta/p -- truncated or converged, shallow or matched or deep,
integer or continuous regressor -- is a constant: the honest
summary is beta = 1.0-1.5 decades per in-band zero (recipe and c
scatter ~20%) against a window-qualified plunge rate, ratio band
1.4-1.9 for c >= 120. The pi^2/4 candidate, and with it any
numerological reading of its "/4", is dead on the record. The
floor law's content stays what the deflations left: the horizon
tau* = 2pi e^(2A) (exact), the tight mean ln(tau0/2pi) (exact),
an order-one-decade-per-zero climb through the plunge (measured,
window-qualified), and feature-local saturation.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from numpy.polynomial import legendre as L
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from fold_surrogate import A, make_basis, psi_hat_batch
from witness_offline import XG, WG


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS8 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "floor_probe8.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

CS_A = [60.0, 120.0, 170.0, 240.0, 340.0]
EXTRA = 28
CONV_EXTRAS = [8, 16, 28]
MWIN = (1e-11, 1e-2)
LWIN = (1e-11, 1e-2)
LSH = (1e-4, 0.5)
LDP = (1e-11, 1e-6)


class SectX:
    """Extended-basis section (real path only)."""
    def __init__(self, c, extra):
        self.c = c
        self.n = int(2*c/math.pi) + 4 + extra
        KL = int(1.4*c) + 60 + 2*extra
        self.KL = KL
        self.P = make_basis(c, self.n, KL)
        xg, wg = np.polynomial.legendre.leggauss(800)
        PX = np.zeros((self.n, len(xg)))
        for m in range(self.n):
            PX[m] = L.legval(xg, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        self.G = A*np.einsum('ni,i,mi->nm', PX, wg, PX)

    def lam(self):
        PX = np.zeros((self.n, len(XG)))
        for m in range(self.n):
            PX[m] = L.legval(XG, self.P[m]*np.sqrt(np.arange(self.KL)
                                                   + 0.5))
        D = XG[:, None] - XG[None, :]
        K = np.where(np.abs(D) < 1e-12, self.c/np.pi,
                     np.sin(self.c*D)/(np.pi*np.where(
                         np.abs(D) < 1e-12, 1.0, D)))
        return np.array([(PX[m]*WG) @ K @ (PX[m]*WG) /
                         ((PX[m]*WG) @ PX[m])
                         for m in range(self.n)])

    def margin(self, zeros, tau0):
        s = np.concatenate([(zeros - tau0)*A, (-zeros - tau0)*A])
        V = psi_hat_batch(self.P, s)*A
        Q = V @ V.conj().T
        Q = (Q + Q.conj().T)/2
        return float(scipy_eigh(Q, self.G, eigvals_only=True)[0])


def rate(lam, win):
    ks = [k for k, l in enumerate(lam) if win[0] < l < win[1]]
    if len(ks) < 3:
        return None
    return float(abs(np.polyfit(
        ks, [math.log10(lam[k]) for k in ks], 1)[0]))


def climb(S, Z, c, step=5.0):
    """m(tau0) on a step-5 grid clipped to the zero window, fit on
    MWIN against both count regressors."""
    rows = []
    t0 = 230.0
    while t0 <= 352.0:
        if t0 + c/A <= 640.0:
            m = S.margin(Z, t0)
            if m > 1e-15:
                u = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
                nb = int(np.sum(np.abs(u) <= c))
                nbar = (2*c/A)*math.log(t0/(2*math.pi))/(2*math.pi)
                rows.append((t0, m, nb, nbar))
        t0 += step
    sel = [r for r in rows if MWIN[0] < r[1] < MWIN[1]]
    if len(sel) < 4:
        return None, None, len(sel), rows
    lm = [math.log10(r[1]) for r in sel]
    b_int = float(abs(np.polyfit([r[2] for r in sel], lm, 1)[0]))
    b_con = float(abs(np.polyfit([r[3] for r in sel], lm, 1)[0]))
    return b_int, b_con, len(sel), rows


def run():
    Z = zeros380()
    # convergence control at c = 120
    for extra in CONV_EXTRAS:
        params = {"deps": DEPS8, "c": 120.0, "extra": extra,
                  "lwin": LWIN, "lsh": LSH, "ldp": LDP}
        st = ckpt_key.load(f"asym_conv_e{extra}", KEYFILE, params)
        if st is None:
            S = SectX(120.0, extra)
            lam = S.lam()
            st = {"p_m": rate(lam, LWIN), "p_s": rate(lam, LSH),
                  "p_d": rate(lam, LDP)}
            ckpt_key.save(f"asym_conv_e{extra}", KEYFILE, params, st)
        print(f"  E0 c=120 extra={extra}: p_matched "
              f"{st['p_m'] if st['p_m'] else float('nan'):.4f} "
              f"p_shallow {st['p_s'] if st['p_s'] else float('nan'):.4f} "
              f"p_deep {st['p_d'] if st['p_d'] else float('nan'):.4f}",
              flush=True)
    # the ladder
    for c in CS_A:
        params = {"deps": DEPS8, "c": c, "extra": EXTRA,
                  "mwin": MWIN, "lwin": LWIN, "step": 5.0}
        st = ckpt_key.load(f"asym_c{int(c)}", KEYFILE, params)
        if st is None:
            S = SectX(c, EXTRA)
            lam = S.lam()
            b_int, b_con, npts, rows = climb(S, Z, c)
            st = {"p_m": rate(lam, LWIN), "p_s": rate(lam, LSH),
                  "p_d": rate(lam, LDP), "b_int": b_int,
                  "b_con": b_con, "npts": npts, "rows": rows}
            ckpt_key.save(f"asym_c{int(c)}", KEYFILE, params, st)
        pm, bi, bc = st["p_m"], st["b_int"], st["b_con"]
        if pm and bi:
            print(f"  E1 c={c:.0f}: p_m {pm:.4f} (sh {st['p_s']:.4f} "
                  f"dp {st['p_d']:.4f}) beta_int {bi:.4f} beta_con "
                  f"{bc:.4f} ({st['npts']} pts) ratio_m "
                  f"{bi/pm:.3f}/{bc/pm:.3f}", flush=True)
        else:
            print(f"  E1 c={c:.0f}: unfit (pts {st['npts']})",
                  flush=True)


if __name__ == "__main__":
    run()
    print("asymptote probes complete", flush=True)
