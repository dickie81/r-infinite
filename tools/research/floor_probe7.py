#!/usr/bin/env python3
"""The ratio attack (commissioned after the saturation attack):
derive the floor law's last underived number -- beta/plunge ~ 2.4
(the climb rate in decades per in-band zero over the Slepian
plunge fall rate in decades per mode; measured 2.34 / 2.46 at
c = 60 / 120).

THE CANDIDATE (scaffold, tested here): beta/p = pi^2/4 = 2.467.
With the Landau-Widom plunge-rate form p = pi^2/(2 ln(alpha c)
ln 10), the measured p at both certified c give the SAME
alpha ~ 0.68, and the prediction beta = (pi^2/4) p hits the
measured c = 120 climb rate to 0.3% (1.198 vs 1.195).

Experiments:
  E1 the c-ladder: c in {45, 60, 90, 120, 170} -- per c the
     Slepian spectrum (plunge rate p, same fit recipe as the 1bg
     landing) and a dense zeta climb ladder (tau0 = 230..350 step
     10, m_Z by the certified real path), beta vs in-band count.
     Tests beta/p = pi^2/4 across a 3.8x range of c and pins
     alpha in the Landau-Widom form.
  E2 surrogate climbs at c = 60 and 120 on the same grid:
     the perfect lattice (density rho(tau0), deterministic
     aliasing climb) and CUE spacings (5 realizations/point,
     certified-comparator pattern) -- if the RATIO is shared and
     only intercepts move, the 2.4 is pure sampling/Slepian
     geometry and the arithmetic lives in the intercept (the
     certified 1bc stiffness excess); if the slope bends with the
     process, spacing statistics enter the exponent.
  E3 the mechanism: at the c = 120 climb points, the minimizer's
     prolate occupancy edge k* (90% mass) vs the in-band count
     (slope 1 = one mode per zero?), and log m vs log(1 - lambda)
     at the edge (the leakage-pricing exponent).
  E4 the fits: beta/p per c; alpha per c from p; the pi^2/4
     verdict.
  E5 basis-truncation control: c = 120 with n extended by 8
     (the standard basis carries only ~4 plunge modes) -- does
     beta move?

Check 7: Slepian asymptotics, sampling surrogates -- classical.
Check 8: no hypothesis input. Keying per A355: DEPS = this file +
floor_probe.py + the four substrates; params carry every stage
input; CUE seeds explicit.

RESULT (all probes complete): THE 2.4 DEFLATES -- it is not a
universal constant.

  E1 (one fixed recipe, dense uniform grid): the ratio is NOT
     c-independent: 1.374 / 1.916 / 1.982 / 2.346 / 2.443 at
     c = 45/60/90/120/170 -- and the drift is carried by the
     DENOMINATOR: beta is approximately c-flat (0.87-1.16, no
     monotone trend, median ~1.1 decades per in-band zero) while
     p falls as ~1/ln(alpha c) (alpha = 0.66-0.69 for c <= 120;
     the c = 170 value 0.53 is the truncation artifact below).
  E5 (the killer): extending the basis by 8 modes at c = 120
     moves p 0.486 -> 0.690 (+42%) and beta 1.140 -> 1.212 (+6%);
     the ratio moves 2.346 -> 1.757. The measured "plunge rate"
     is BASIS-TRUNCATION-CONDITIONED: the standard section
     (n = N_sh + 4) clips the plunge at the same relative depth
     at every c -- which is exactly why the landed ratio looked
     c-independent at c = 60/120. The pi^2/4 candidate is dead as
     a finite-c identity and not even well-posed as an asymptote
     under this sensitivity.
  E2 (process dependence): mild and non-uniform -- zeta
     1.109/1.140 vs lattice 0.882/1.219 vs CUE 0.709/0.956 at
     c = 60/120. CUE is consistently ~20% shallower; the lattice
     brackets zeta. At leading order the slope is
     sampling-geometric; the certified 1bc stiffness excess
     remains an intercept phenomenon.
  E3 (mechanism): the minimizer's 90%-occupancy edge advances
     ~2 modes per added zero (slopes 1.4-2.3, median ~2): the
     per-zero price is roughly two plunge-mode leakage quanta --
     measured, not derived.
  Recipe sensitivity disclosed: the 1bg landing recipe gave 2.34
     at c = 60; this recipe gives 1.92 (integer-chunky counts +
     window choice).

NET: the honest floor law simplifies -- m_Z ~ m_sat *
10^(-beta (N* - nb)) with beta ~ 1.1 +- 0.15 decades per in-band
zero, at most weakly c-dependent; the "beta/plunge ~ 2.4"
framing landed in Theorem 1bg is a (recipe, basis)-conditioned
slope ratio, not a structural constant, and the paper block is
corrected accordingly (the g3/g4 gates remain honest as measured
pins under the standard basis and recipe -- their stage
reproduces them -- but the c-independence INTERPRETATION is
struck). Open (small): why ~2 modes per zero; whether beta's
~1.1 has a closed form.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from numpy.polynomial import legendre as L
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from fold_surrogate import A, make_basis
from floor_probe6 import cue_points, local_density
from witness_offline import XG, WG
from witness_twosided import TwoSided


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS7 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe.py", "floor_probe6.py",
    "floor_probe7.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

CS = [45.0, 60.0, 90.0, 120.0, 170.0]

def _zsha(a):
    """Ordinate-content hash (round-235 held observation: the
    keying class's landing-scope fix extended to this instrument's
    own checkpoints -- stage inputs keyed by content, not intent).
    """
    import numpy as _np
    return hashlib.sha256(
        _np.ascontiguousarray(a).tobytes()).hexdigest()[:16]

T0S = [230.0 + 10.0*i for i in range(13)]      # 230..350
SUR_CS = [60.0, 120.0]
MWIN = (1e-13, 0.15)


class TwoSidedN(TwoSided):
    """TwoSided with the basis extended by `extra` modes (E5)."""
    def __init__(self, c, extra):
        self.c = c
        self.n = int(2*c/math.pi) + 4 + extra
        KL = int(1.4*c) + 60 + 2*extra
        self.P = make_basis(c, self.n, KL)
        xg, wg = np.polynomial.legendre.leggauss(800)
        PX = np.zeros((self.n, len(xg)))
        for m in range(self.n):
            PX[m] = L.legval(xg, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        self.G = A*np.einsum('ni,i,mi->nm', PX, wg, PX)
        PXc = np.zeros((self.n, len(XG)))
        for m in range(self.n):
            PXc[m] = L.legval(XG, self.P[m]*np.sqrt(np.arange(KL) + 0.5))
        self.PXw = PXc*WG[None, :]


def nband(Z, c, t0):
    u = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
    return int(np.sum(np.abs(u) <= c))


def climb_fit(rows):
    """(nb, m) rows -> slope in decades/zero over MWIN."""
    sel = [(nb, m) for nb, m in rows if MWIN[0] < m < MWIN[1]]
    if len(sel) < 3:
        return None, len(sel)
    nb = [r[0] for r in sel]
    lm = [math.log10(r[1]) for r in sel]
    return float(abs(np.polyfit(nb, lm, 1)[0])), len(sel)


def plunge_rate(S):
    lam = 1.0 - S.slepian_leakage()
    ks = [k for k, l in enumerate(lam) if 1e-10 < l < 0.5]
    if len(ks) < 2:
        return None, lam
    return float(abs(np.polyfit(
        ks, [math.log10(lam[k]) for k in ks], 1)[0])), lam


def run():
    Z = zeros380()
    for c in CS:
        params = {"deps": DEPS7, "c": c, "t0s": T0S,
                  "z_sha": _zsha(Z)}
        st = ckpt_key.load(f"ratio_c{int(c)}", KEYFILE, params)
        if st is None:
            S = TwoSided(c)
            p, lam = plunge_rate(S)
            rows = []
            occ = []
            for t0 in T0S:
                sgrid = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
                from fold_surrogate import psi_hat_batch
                V = psi_hat_batch(S.P, sgrid)*A
                Q = V @ V.conj().T
                Q = (Q + Q.conj().T)/2
                ev, VV = scipy_eigh(Q, S.G)
                m = float(ev[0])
                w2 = np.abs(VV[:, 0])**2
                cs_ = np.cumsum(w2)/np.sum(w2)
                kstar = int(np.searchsorted(cs_, 0.9))
                rows.append([nband(Z, c, t0), m])
                occ.append([t0, kstar,
                            float(lam[min(kstar, len(lam)-1)])])
            beta, npts = climb_fit(rows)
            st = {"p": p, "beta": beta, "npts": npts,
                  "rows": rows, "occ": occ,
                  "nsh": 2*c/math.pi}
            ckpt_key.save(f"ratio_c{int(c)}", KEYFILE, params, st)
        p, beta = st["p"], st["beta"]
        if beta:
            alpha = math.exp(math.pi**2/(2*p*math.log(10)))/c
            print(f"  E1 c={c:.0f}: p {p:.4f} beta {beta:.4f} "
                  f"({st['npts']} pts) ratio {beta/p:.3f} "
                  f"[pi^2/4 = {math.pi**2/4:.3f}] alpha {alpha:.3f}",
                  flush=True)
        else:
            print(f"  E1 c={c:.0f}: p {p:.4f} beta unfit "
                  f"({st['npts']} pts)", flush=True)

    for c in SUR_CS:
        params = {"deps": DEPS7, "c": c, "t0s": T0S, "nreal": 5,
                  "seed": 31, "half": 300.0, "z_sha": _zsha(Z)}
        st = ckpt_key.load(f"ratio_sur_c{int(c)}", KEYFILE, params)
        if st is None:
            S = TwoSided(c)
            rng = np.random.default_rng(31)
            lat_rows, cue_rows = [], []
            for t0 in T0S:
                dens = local_density(t0)
                lat = t0 + (np.arange(-int(300.0*dens),
                                      int(300.0*dens) + 1))/dens
                lat_rows.append([nband(lat, c, t0),
                                 float(S.margin(lat, t0))])
                ms = []
                for _ in range(5):
                    pts = cue_points(rng, t0, 300.0, dens, N=480)
                    ms.append(max(float(S.margin(pts, t0)), 1e-18))
                cue_rows.append([nband(np.asarray(pts), c, t0),
                                 float(np.exp(np.mean(np.log(ms))))])
            bl, nl = climb_fit(lat_rows)
            bc, nc = climb_fit(cue_rows)
            st = {"lat_rows": lat_rows, "cue_rows": cue_rows,
                  "beta_lat": bl, "n_lat": nl,
                  "beta_cue": bc, "n_cue": nc}
            ckpt_key.save(f"ratio_sur_c{int(c)}", KEYFILE, params, st)
        print(f"  E2 c={c:.0f}: beta_lat "
              f"{st['beta_lat'] if st['beta_lat'] else float('nan'):.4f} "
              f"({st['n_lat']} pts)  beta_cue "
              f"{st['beta_cue'] if st['beta_cue'] else float('nan'):.4f} "
              f"({st['n_cue']} pts)", flush=True)

    params = {"deps": DEPS7, "c": 120.0, "t0s": T0S, "extra": 8,
              "z_sha": _zsha(Z)}
    st = ckpt_key.load("ratio_ext120", KEYFILE, params)
    if st is None:
        S = TwoSidedN(120.0, 8)
        rows = []
        for t0 in T0S:
            rows.append([nband(Z, 120.0, t0),
                         float(S.margin(Z, t0))])
        beta, npts = climb_fit(rows)
        p, _ = plunge_rate(S)
        st = {"beta": beta, "npts": npts, "p": p, "rows": rows}
        ckpt_key.save("ratio_ext120", KEYFILE, params, st)
    print(f"  E5 c=120 n+8: beta {st['beta']:.4f} ({st['npts']} pts) "
          f"p {st['p']:.4f} ratio {st['beta']/st['p']:.3f}",
          flush=True)


if __name__ == "__main__":
    run()
    print("ratio probes complete", flush=True)
