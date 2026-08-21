#!/usr/bin/env python3
"""The 1bh landing stage (the height-uniformity arc, consolidated):
produces every quantity the Theorem 1bh verifier
(cascade_height_uniformity.py) gates on, driving the arc's four
instruments --

  height_uniformity.py : the aperture-dial rung ladders (tau* =
      2pi e^(2A) out-of-sample; the tight-mean control; the
      deficit-parameterized climbs) and the beta fits under the
      DECLARED recipe (fit window m in (1e-12, 1e-2), regressor =
      the integer in-band count).
  height_anomaly.py : the mirror ablation and far-mirror control.
  (the gradient test, run inline at the anomaly attack, is
      COMMITTED here as _gradient -- the landing closes that
      code-provenance gap.)
  height_arith.py / height_residue.py : the Phase-2 arithmetic
      side under THE POLE RULE (include the pole pair iff
      A*tau0 <= 2200 -- within quadrature validity; omit
      otherwise, where it is analytically negligible and a
      computed value is unbounded noise), plus the with-pole
      diagnostics that demonstrate the rule at (3, 2000/2340).

The stage lives here per the round-229 F7 rule; every sub-stage
and the consolidated checkpoint are content-keyed per the standing
law (A361: module shas + full config + ordinate-array bytes).
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
import height_anomaly as HA
import height_arith as HR
import height_uniformity as HU
from fold_D import zeros380, inv_Nbar
from fold_surrogate import psi_hat_batch


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

MODULES = ("fold_D.py", "fold_surrogate.py", "height_uniformity.py",
           "height_anomaly.py", "height_arith.py",
           "height_residue.py", "height_landing.py")
DEPSL2 = {f: _sha(f) for f in MODULES}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")
_zsha = HU._zsha

POLE_VALID = 2200.0            # |A*tau0| quadrature validity bound
ARITH_PTS = [(2.5, 630.0, 810), (2.5, 880.0, 810),
             (3.0, 1580.0, 2270), (3.0, 2000.0, 2270),
             (3.0, 2340.0, 2270)]
POLE_DIAG = [(3.0, 2000.0, 2270), (3.0, 2340.0, 2270)]
GRAD_PTS = [(1.5, 116.5, 380), (1.5, 130.0, 380), (3.0, 2000.0, 2270)]
FITWIN = (1e-12, 1e-2)


def _zfor(Z380, kmax):
    ZE = HU.ext_zeros_to(kmax)
    return np.concatenate([Z380, ZE]) if len(ZE) else Z380


def _rungs(Z380):
    out = {}
    for Ap, t0s, kmax in HU.RUNGS:
        Z = _zfor(Z380, kmax)
        params = {"deps": HU.DEPSH, "A": Ap, "c": HU.C0, "t0s": t0s,
                  "kmax": kmax, "z_sha": _zsha(Z)}
        name = f"height_A{Ap:.1f}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            S = HU.ASect(HU.C0)
            rows = []
            for t0 in t0s:
                r = S.measures(Z, t0, Ap)
                r["t0"] = t0
                rows.append(r)
            st = {"A": Ap, "tstar": 2*math.pi*math.exp(2*Ap),
                  "rows": rows}
            ckpt_key.save(name, KEYFILE, params, st)
        rows = st["rows"]
        sel = [r for r in rows if FITWIN[0] < r["m"] < FITWIN[1]]
        beta = float(abs(np.polyfit(
            [r["nb"] for r in sel],
            [math.log10(r["m"]) for r in sel], 1)[0]))
        qrel = max(abs(r["qtop"]/math.log(r["t0"]/(2*math.pi)) - 1)
                   for r in rows)
        out[f"{Ap:.1f}"] = {"rows": {f"{r['t0']:.1f}": r["m"]
                                     for r in rows},
                            "beta": beta, "nsel": len(sel),
                            "qrel": float(qrel)}
    return out


def _anomaly(Z380):
    out = {}
    for Ap, t0s, kmax in HA.LADDERS_AB:
        Z = _zfor(Z380, kmax)
        params = {"deps": HA.DEPSA, "A": Ap, "c": HA.C0, "t0s": t0s,
                  "kmax": kmax, "z_sha": _zsha(Z)}
        name = f"anom_A{Ap:.1f}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            S = HU.ASect(HA.C0)
            rows = []
            for t0 in t0s:
                G, Qd, Qm = HA.forms(S, Z, t0, Ap)
                Q = Qd + Qm
                Q = (Q + Q.conj().T)/2
                m_full = float(scipy_eigh(Q, G, eigvals_only=True)[0])
                m_dir = float(scipy_eigh(Qd, G, eigvals_only=True)[0])
                rows.append({"t0": t0, "m_full": m_full,
                             "m_dir": m_dir})
            st = {"A": Ap, "rows": rows}
            ckpt_key.save(name, KEYFILE, params, st)
        out[f"{Ap:.1f}"] = st["rows"]
    return out


def _Nbar(t):
    return t/(2*math.pi)*math.log(t/(2*math.pi*math.e)) + 7.0/8.0


def _gradient(Z380):
    """The E3 gradient test, now committed: zeros vs the
    smooth-counting comb (density gradient, no fluctuations) vs the
    constant-density comb, at the anomaly points + the high
    control."""
    out = []
    S = HU.ASect(HU.C0)
    for Ap, t0, kmax in GRAD_PTS:
        Z = _zfor(Z380, kmax)
        params = {"deps": DEPSL2, "A": Ap, "t0": t0,
                  "kmax": kmax, "z_sha": _zsha(Z)}
        name = f"grad_A{Ap:.1f}_t{int(t0)}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            lo = max(15.0, t0 - 120.0/Ap - 60)
            hi = t0 + 120.0/Ap + 60
            js = np.arange(math.ceil(_Nbar(lo)), math.floor(_Nbar(hi)))
            grad = np.array([inv_Nbar(j + 0.5) for j in js])
            rho = math.log(t0/(2*math.pi))/(2*math.pi)
            cst = t0 + (np.arange(int((lo - t0)*rho),
                                  int((hi - t0)*rho) + 1))/rho
            def marg(g):
                return S.measures(np.asarray(g), t0, Ap)["m"]
            st = {"A": Ap, "t0": t0, "m_zeros": marg(Z),
                  "m_grad": marg(grad), "m_const": marg(cst)}
            ckpt_key.save(name, KEYFILE, params, st)
        out.append(st)
    return out


def _arith(Z380):
    out = []
    S = HR.AWSect(HU.C0)
    for Ap, t0, kmax in ARITH_PTS:
        Z = _zfor(Z380, kmax)
        Tz = float(Z.max()) + 0.5
        use_pole = Ap*t0 <= POLE_VALID
        params = {"deps": DEPSL2, "A": Ap, "t0": t0,
                  "Tz": round(Tz, 2), "s_cut": HR.SCUT,
                  "s_step": HR.S_STEP, "pole": use_pole,
                  "z_sha": _zsha(Z)}
        name = f"land_arith_A{Ap:.1f}_t{int(t0)}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            G = Ap*S.gram
            AT, NR = HR.arch_true_A(S, t0, Ap, Tz)
            PR = HR.prime_mat_A(S, t0, Ap)
            QW = AT + PR
            if use_pole:
                u, v = HR.pole_vecs_A(S, t0, Ap)
                Mp = np.outer(np.conj(v), u)
                QW = QW + Mp + Mp.conj().T
            QW = (QW + QW.conj().T)/2
            QZ = HR.zform_A(S, Z, t0, Ap)
            evW, VW = scipy_eigh(QW, G)
            mW, wW = float(evW[0]), VW[:, 0]
            st = {"A": Ap, "t0": t0, "pole": use_pole,
                  "mW": mW,
                  "mZ": float(scipy_eigh(QZ, G,
                                         eigvals_only=True)[0]),
                  "rel": float(np.linalg.norm(QW - QZ) /
                               np.linalg.norm(QW)),
                  "arch": float(np.real(np.conj(wW) @ AT @ wW)),
                  "prime": float(np.real(np.conj(wW) @ PR @ wW))}
            ckpt_key.save(name, KEYFILE, params, st)
        out.append(st)
    # the pole-rule demonstration (with-pole diagnostics)
    diag = []
    for Ap, t0, kmax in POLE_DIAG:
        Z = _zfor(Z380, kmax)
        Tz = float(Z.max()) + 0.5
        params = {"deps": DEPSL2, "A": Ap, "t0": t0,
                  "Tz": round(Tz, 2), "s_cut": HR.SCUT,
                  "s_step": HR.S_STEP, "z_sha": _zsha(Z)}
        name = f"land_pdiag_A{Ap:.1f}_t{int(t0)}".replace(".", "p")
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            G = Ap*S.gram
            AT, NR = HR.arch_true_A(S, t0, Ap, Tz)
            PR = HR.prime_mat_A(S, t0, Ap)
            u, v = HR.pole_vecs_A(S, t0, Ap)
            Mp = np.outer(np.conj(v), u)
            QWp = AT + PR + Mp + Mp.conj().T
            QWp = (QWp + QWp.conj().T)/2
            QZ = HR.zform_A(S, Z, t0, Ap)
            st = {"A": Ap, "t0": t0,
                  "norm_u": float(np.linalg.norm(u)),
                  "rel_withpole": float(np.linalg.norm(QWp - QZ) /
                                        np.linalg.norm(QWp))}
            ckpt_key.save(name, KEYFILE, params, st)
        diag.append(st)
    return out, diag


def load_or_run():
    Z380 = zeros380()
    assert len(Z380) == 380
    ZEmax = HU.ext_zeros_to(2270)
    params = {"deps": DEPSL2, "pole_valid": POLE_VALID,
              "fitwin": FITWIN, "z_sha": _zsha(Z380),
              "zext_sha": _zsha(ZEmax)}
    st = ckpt_key.load("height_arc_landing", KEYFILE, params)
    if st is None:
        arith, pdiag = _arith(Z380)
        st = {"rungs": _rungs(Z380), "anom": _anomaly(Z380),
              "grad": _gradient(Z380), "arith": arith,
              "pdiag": pdiag}
        ckpt_key.save("height_arc_landing", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    st = load_or_run()
    for a, r in st["rungs"].items():
        print(f"A={a}: beta {r['beta']:.4f} qrel {r['qrel']:.4f}")
    print("landing stage complete", flush=True)
