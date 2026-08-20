#!/usr/bin/env python3
"""The floor attack, second instrument: (i) densify the climb
ladders (step 10 where floor_probe.py measured the slopes with
step 20), sharpening the decades-per-zero rates whose ratio to the
Slepian plunge rate measured 2.50/2.52 at c = 60/120; (ii) measure
the minimizer overlap |<w_Z, G w_W>| at regime-sample points -- the
mechanism probe for the antisymmetry invariant T(w_Z) = -T(w_W)
(median relative residual 3-5e-4 across all 37 first-run points):
if the two minimizers are near-parallel, the antisymmetry is a
perturbative identity (w_W = w_Z + delta with the excess symmetric
to O(delta^2)); if they are far apart, it is a genuine two-sided
symmetry of the pair (Q_Z, Q_W) and much stranger.

Keying per the A355 standing rule: DEPS carries the producing code
(this file AND floor_probe.py, whose floor_point it extends) plus
the four substrate modules; params carry (c, t0, nz, botk).
floor_probe.py's own checkpoints are untouched (separate names,
separate producing code -- this file does not edit that one).

RESULT (run complete at f403d73): the dense climb sharpened the
combined fits recorded in floor_probe.py's RESULT (N* = N_sh to
1-2%; beta/plunge = 2.34/2.46). The overlap probe DECIDED the
antisymmetry mechanism: |<w_Z, G w_W>| = 0.014-0.36 at the six
regime points (0.36 at the certified (60,200); 0.01-0.11 on the
climb and at saturation) -- the two minimizers are far from
parallel, in several cases nearly G-orthogonal, while
T(w_Z) = -T(w_W) holds to 5e-4 median. The perturbative reading
(w_W = w_Z + small) is REFUTED: the antisymmetry is a structural
symmetry of the PAIR (Q_Z, Q_W) -- each form's minimizer pays the
same excess in the other form -- and its mechanism is the arc's
open object, alongside the beta/plunge ~ 2.4 constant and the
c-independent saturation value 0.25.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from fold_D import zeros380
from floor_probe import floor_point
from witness_twosided import TwoSided


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS2 = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "witness_offline.py",
    "witness_twosided.py", "floor_probe.py", "floor_probe2.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

NZ = 380
BOTK = 5
# dense climb fills (halfway points of the first run's step-20 grid)
LADDERS2 = {
    60.0: [150.0, 170.0, 190.0, 210.0, 230.0, 250.0, 270.0, 290.0],
    120.0: [230.0, 250.0, 270.0, 290.0, 310.0, 330.0, 350.0],
}
# regime samples for the overlap probe (below horizon / deep climb /
# mid-climb / saturated)
OVPTS = [(60.0, 200.0), (120.0, 180.0), (120.0, 260.0),
         (120.0, 300.0), (120.0, 340.0), (120.0, 420.0)]


def point2(S, Z, c, t0):
    """floor_point plus the minimizer overlap |<w_Z, G w_W>| (both
    unit G-norm), recomputed here so both vectors are in scope."""
    st = floor_point(S, Z, c, t0)
    from floor_probe import zero_form
    from scipy.linalg import eigh as scipy_eigh
    QZ = zero_form(S, Z, t0)
    evz, VZ = scipy_eigh(QZ, S.G)
    wZ = VZ[:, 0]
    mW, wW = S.weil_margin(t0)
    ov = abs(complex(np.conj(wZ) @ S.G @ wW))
    st["ov"] = float(ov)
    return st


def run():
    Z = zeros380()
    sects = {}
    def sect(c):
        if c not in sects:
            sects[c] = TwoSided(c)
        return sects[c]
    for c, t0s in LADDERS2.items():
        for t0 in t0s:
            params = {"deps": DEPS2, "c": c, "t0": t0,
                      "nz": NZ, "botk": BOTK}
            name = f"floor2_{int(c)}_{int(t0)}"
            st = ckpt_key.load(name, KEYFILE, params)
            if st is None:
                st = point2(sect(c), Z, c, t0)
                ckpt_key.save(name, KEYFILE, params, st)
            print(f"  c={c:5.0f} t0={t0:5.0f}: mZ {st['mZ']:+.3e} "
                  f"mW {st['mW']:+.3e} ratio {st['ratio']:+.3f} "
                  f"ov {st['ov']:.4f} nb {st['nband_c']}", flush=True)
    for c, t0 in OVPTS:
        params = {"deps": DEPS2, "c": c, "t0": t0,
                  "nz": NZ, "botk": BOTK}
        name = f"floor2ov_{int(c)}_{int(t0)}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = point2(sect(c), Z, c, t0)
            ckpt_key.save(name, KEYFILE, params, st)
        print(f"  OV c={c:5.0f} t0={t0:5.0f}: mZ {st['mZ']:+.3e} "
              f"ov {st['ov']:.4f} TwZ {st['TwZ']:+.3e} "
              f"TwW {st['TwW']:+.3e}", flush=True)


if __name__ == "__main__":
    run()
    print("floor2 complete", flush=True)
