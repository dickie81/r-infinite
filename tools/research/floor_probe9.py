#!/usr/bin/env python3
"""The flow attack (commissioned after the asymptote exclusion):
the floor law under the de Bruijn-Newman surrogate dynamics --
the finite-N zero flow dx_j/dt = sum_{k!=j} 2/(x_j - x_k)
(repulsion forward, the standard dBN/Rodgers-Tao surrogate;
mirror ordinates -x_k exert their force analytically, the +-pair
evolving symmetrically). Forward time anneals the spacing
fluctuations (t -> inf: equal spacing); backward time opens gaps
and drives the tightest pairs toward collision -- the local model
of which is exactly the certified 1bf collision topology.

PREDICTIONS ON THE RECORD (this run tests them):
  (P1) the saturated margin m_sat(t) at (120, 420) RISES toward
       the tight value ln(tau0/2pi) = 4.20 forward -- the
       fluctuation discount (measured 16x at t = 0) evaporates,
       not the horizon;
  (P2) the tight-mean control Q(top prolate) stays ~ L at every t
       (density is flow-invariant; tau* immovable);
  (P3) climb margins rise forward (intercept motion), collapse
       backward; min-gap(t) closes backward on the ~t = -0.03 to
       -0.06 scale (two-body estimate g^2/8 for the tightest
       t = 0 gaps);
  (P4) spacing std shrinks forward (the rigidity meter).

Truncation honesty: only the 380-ordinate list evolves; the
missing far tail exerts a smooth drift that shifts positions
without much local spacing effect; measurements sit in the
interior band. Time is in surrogate units of the ODE above (no
calibration to the true dBN normalization is claimed).

Check 7: an ODE plus the committed margin instruments --
classical. Check 8: no hypothesis input. Keying per A355: DEPS =
this file + substrates; params carry every t and the integrator
step; evolved configurations are checkpointed per t.

RESULT: appended after the run by the analysis pass.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from fold_surrogate import A, psi_hat_batch
from witness_twosided import TwoSided


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS9 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe9.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

T_FWD = [0.05, 0.15, 0.5, 1.5, 5.0]
T_BWD = [-0.01, -0.02, -0.03, -0.045]
PTS9 = [(120.0, 260.0), (120.0, 300.0), (120.0, 420.0)]
DT_F, DT_B = 1e-3, 2e-4
GAP_GUARD = 0.03


def force(x):
    d = x[:, None] - x[None, :]
    np.fill_diagonal(d, np.inf)
    f = np.sum(2.0/d, axis=1)
    f += np.sum(2.0/(x[:, None] + x[None, :]), axis=1)  # mirrors
    return f


def evolve(x0, t_target, dt):
    """Fixed-step RK4 to t_target (sign of dt = sign of target);
    stops early if min gap < GAP_GUARD; returns (x, t_reached)."""
    x = x0.copy()
    t = 0.0
    h = dt if t_target > 0 else -dt
    nstep = int(round(abs(t_target)/dt))
    for i in range(nstep):
        if np.diff(x).min() < GAP_GUARD:
            return x, t
        k1 = force(x)
        k2 = force(x + 0.5*h*k1)
        k3 = force(x + 0.5*h*k2)
        k4 = force(x + h*k3)
        x = x + (h/6.0)*(k1 + 2*k2 + 2*k3 + k4)
        t += h
    return x, t


def measures(S, Z, t0):
    s = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
    V = psi_hat_batch(S.P, s)*A
    Q = V @ V.conj().T
    Q = (Q + Q.conj().T)/2
    m = float(scipy_eigh(Q, S.G, eigvals_only=True)[0])
    w = np.eye(S.n)[:, 0]/math.sqrt(S.G[0, 0])
    qtop = float(np.real(np.conj(w) @ Q @ w))
    return m, qtop


def band_stats(Z, t0, c):
    zb = Z[(Z > t0 - c/A) & (Z < t0 + c/A)]
    g = np.diff(zb)
    return {"mean_gap": float(g.mean()), "std_gap": float(g.std()),
            "min_gap": float(g.min()), "max_gap": float(g.max()),
            "count": int(len(zb))}


def run():
    Z0 = zeros380()
    S = TwoSided(120.0)
    for t_tgt in [0.0] + T_FWD + T_BWD:
        dt = DT_F if t_tgt >= 0 else DT_B
        params = {"deps": DEPS9, "t": t_tgt, "dt": dt,
                  "guard": GAP_GUARD, "nz": 380}
        name = f"flow_t{t_tgt:+.3f}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            if t_tgt == 0.0:
                Z, t_r = Z0.copy(), 0.0
            else:
                Z, t_r = evolve(Z0, t_tgt, dt)
            row = {"t_target": t_tgt, "t_reached": t_r, "pts": {}}
            gmin_all = float(np.diff(Z).min())
            for c, t0 in PTS9:
                m, qtop = measures(S, Z, t0)
                row["pts"][f"{t0:.0f}"] = {
                    "m": m, "qtop": qtop,
                    **band_stats(Z, t0, c)}
            row["gmin_all"] = gmin_all
            st = row
            ckpt_key.save(name, KEYFILE, params, st)
        p260, p300, p420 = (st["pts"]["260"], st["pts"]["300"],
                            st["pts"]["420"])
        print(f"  t={st['t_target']:+.3f} (reached "
              f"{st['t_reached']:+.4f}, gmin {st['gmin_all']:.3f}): "
              f"m260 {p260['m']:.3e} m300 {p300['m']:.3e} "
              f"m420 {p420['m']:.3e} | Qtop420 {p420['qtop']:.3f} "
              f"stdgap420 {p420['std_gap']:.3f} "
              f"mingap420 {p420['min_gap']:.3f}", flush=True)


if __name__ == "__main__":
    run()
    print("flow probes complete", flush=True)
