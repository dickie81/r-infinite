#!/usr/bin/env python3
"""The residue attack (commissioned after Phase 2): why do the
A = 3 saturated-regime points (tau0 = 2000, 2340) close at only
2-4e-2 while the deep point (1580) closes at 1.2e-5 under the
identical recipe?

Suspect ranking from the config pattern:
  R4 POLE QUADRATURE (the sharp one): the pole vectors oscillate
     at frequency A*tau0 ~ 6000-7000 rad over the section -- far
     beyond the 3000-node Gauss validity (~2400) -- so the
     computed pole term is quadrature NOISE (squared, rank-2),
     config-dependent; the TRUE pole contribution at these
     heights is |psi_hat| at frequency ~A*tau0: superexponentially
     negligible. Prediction: ablating the poles recovers the
     closure at 2000/2340 and leaves 1580 unchanged; the computed
     |u|, |v| magnitudes expose the noise scale directly.
  R1 WINDOWING EDGE (reserve): an SCUT sweep at tau0 = 2000
     (1400/1700/2300) -- runs only if R4 fails to close it.
  R3 coverage-clip asymmetry: already disfavored (2340 is clipped
     but 2000, the WORSE point, is interior).

Check 7/8: classical; no hypothesis input. Keying per the
standing law: content-keyed, full config in params.

RESULT (run complete): R4 CONFIRMED IN FULL; THE RESIDUE IS
CLOSED.

  The smoking gun -- the pole-vector magnitudes: |u| = |v| =
  0.039 at tau0 = 1580 (harmless noise) vs 1.93 at 2000 and 1.48
  at 2340 -- ORDER-ONE quadrature garbage at oscillation
  frequency A*tau0 ~ 6000-7000 rad (validity ~2400), where the
  true pole vectors are superexponentially negligible.

  The ablation (the analytically-justified omission):
    tau0 = 2000: closure 4.07e-2 -> 3.41e-5; dm/m +3.42 -> -0.0000
    tau0 = 2340: closure 1.84e-2 -> 2.36e-5; dm/m -0.028 -> +0.0000
    tau0 = 1580: 1.19e-5 -> 8.84e-6 (indifferent, as predicted)

  With the poles omitted, EVERY Phase-2 point is in the 1e-5
  closure class and dm/m <= 0.15%: the height arc's arithmetic
  side is uniformly green at A = 2.5 and 3.0, heights 630-2340.

STANDING RULE (the arc's instrument legacy, alongside 1bg's
horizon matching and the s-window matching): when A*tau0 exceeds
the quadrature validity, the pole term is analytically negligible
and must be OMITTED, never computed -- a computed negligible term
is not a small error, it is unbounded noise.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
from fold_D import zeros380
from height_uniformity import ext_zeros_to
from height_arith import (AWSect, arch_true_A, prime_mat_A,
                          pole_vecs_A, zform_A, C0, SCUT, S_STEP)


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPSR = {f: _sha(f) for f in (
    "fold_D.py", "fold_surrogate.py", "height_uniformity.py",
    "height_arith.py", "height_residue.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")


def _zsha(a):
    return hashlib.sha256(
        np.ascontiguousarray(a).tobytes()).hexdigest()[:16]


PTS_R = [(3.0, 1580.0), (3.0, 2000.0), (3.0, 2340.0)]


def run():
    Z380 = zeros380()
    ZE = ext_zeros_to(2270)
    Z = np.concatenate([Z380, ZE])
    Tz = float(Z.max()) + 0.5
    S = AWSect(C0)
    for Ap, t0 in PTS_R:
        params = {"deps": DEPSR, "A": Ap, "t0": t0, "c": C0,
                  "Tz": round(Tz, 2), "s_cut": SCUT,
                  "s_step": S_STEP, "z_sha": _zsha(Z)}
        name = f"resid_A{Ap:.1f}_t{int(t0)}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            G = Ap*S.gram
            AT, NR = arch_true_A(S, t0, Ap, Tz)
            PR = prime_mat_A(S, t0, Ap)
            u, v = pole_vecs_A(S, t0, Ap)
            Mp = np.outer(np.conj(v), u)
            QZ = zform_A(S, Z, t0, Ap)
            out = {"A": Ap, "t0": t0,
                   "norm_u": float(np.linalg.norm(u)),
                   "norm_v": float(np.linalg.norm(v))}
            for tag, POLE in (("with-pole", Mp + Mp.conj().T),
                              ("no-pole", 0.0)):
                QW = AT + POLE + PR
                QW = (QW + QW.conj().T)/2
                mW = float(scipy_eigh(QW, G, eigvals_only=True)[0])
                mZ = float(scipy_eigh(QZ, G, eigvals_only=True)[0])
                out[tag] = {
                    "mW": mW, "mZ": mZ,
                    "rel": float(np.linalg.norm(QW - QZ) /
                                 np.linalg.norm(QW))}
            ckpt_key.save(name, KEYFILE, params, out)
            st = out
        wp, np_ = st["with-pole"], st["no-pole"]
        print(f"  A={st['A']:.1f} t0={st['t0']:6.0f}: |u| "
              f"{st['norm_u']:.3e} |v| {st['norm_v']:.3e} | "
              f"with-pole rel {wp['rel']:.2e} dm/m "
              f"{(wp['mW']-wp['mZ'])/wp['mZ']:+.4f} | NO-pole rel "
              f"{np_['rel']:.2e} dm/m "
              f"{(np_['mW']-np_['mZ'])/np_['mZ']:+.4f}", flush=True)


if __name__ == "__main__":
    run()
    print("residue probes complete", flush=True)
