#!/usr/bin/env python3
"""The 1bg landing stage (the floor arc, consolidated): produces
every quantity the Theorem 1bg verifier (cascade_floor_closure.py)
gates on, by driving the four attack instruments --

  floor_probe.py / floor_probe2.py : the floor ladders and fits
      (the floor law: N* = N_sh, beta/plunge ~ 2.4, Landau-Widom
      1/ln c scaling, regime pins, minimizer migration)
  floor_probe3.py : the conjugacy (Q_W_code ~= conj Q_Z), the
      conjugate overlap, the first-order g4 accounting
  floor_probe4.py : the partition refutation (window locality,
      per-prime beta_n = -1, tail invisibility) + the extended
      ordinate list
  floor_probe5.py : the defect closure (horizon mismatch;
      matched-window collapse; NR invariance) + arch_true, which
      the gauge verdict also uses

The stage lives here (not in the verifier) per the round-229 F7
rule: the producing code is content-addressed. Sub-stages reuse
the attack runs' exact checkpoint keys (same names, same params,
same producing-module shas), so a clean landing run REUSES them;
CASCADE_COMPUTE=fresh recomputes everything (the landing battery
runs fresh once, per the instrument rules). The consolidated
checkpoint is keyed on all seven module shas plus the config.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from scipy.linalg import eigh as scipy_eigh

import ckpt_key
import floor_probe
import floor_probe2
import floor_probe3
import floor_probe4
import floor_probe5
from fold_D import zeros380
from fold_surrogate import A
from witness_twosided import TwoSided


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

MODULES = ("fold_D.py", "fold_surrogate.py", "witness_offline.py",
           "witness_twosided.py", "floor_probe.py", "floor_probe2.py",
           "floor_probe3.py", "floor_probe4.py", "floor_probe5.py",
           "floor_landing.py")
DEPSL = {f: _sha(f) for f in MODULES}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

CONJ_PTS = [(60.0, 200.0), (120.0, 260.0), (120.0, 300.0),
            (120.0, 420.0)]
DEF_PTS = [(60.0, 200.0), (120.0, 300.0), (120.0, 420.0)]
TLIST, TEXT = 653.7, 1013.1


def _ladder_points(Z, sects):
    """All floor/floor2 ladder points via the attack keys."""
    pts = []
    for c, t0s in floor_probe.LADDERS.items():
        S = sects(c)
        for t0 in t0s:
            params = {"deps": floor_probe.DEPS, "c": c, "t0": t0,
                      "nz": floor_probe.NZ, "botk": floor_probe.BOTK}
            name = f"floor_{int(c)}_{int(t0)}"
            st = ckpt_key.load(name, KEYFILE, params)
            if st is None:
                st = floor_probe.floor_point(S, Z, c, t0)
                ckpt_key.save(name, KEYFILE, params, st)
            pts.append(st)
    for c, t0s in floor_probe2.LADDERS2.items():
        S = sects(c)
        for t0 in t0s:
            params = {"deps": floor_probe2.DEPS2, "c": c, "t0": t0,
                      "nz": floor_probe2.NZ, "botk": floor_probe2.BOTK}
            name = f"floor2_{int(c)}_{int(t0)}"
            st = ckpt_key.load(name, KEYFILE, params)
            if st is None:
                st = floor_probe2.point2(S, Z, c, t0)
                ckpt_key.save(name, KEYFILE, params, st)
            pts.append(st)
    return pts


def _fits(pts, sects):
    out = {}
    for c in (60.0, 120.0):
        lam = 1.0 - sects(c).slepian_leakage()
        ks = [k for k, l in enumerate(lam) if 1e-10 < l < 0.5]
        plunge = float(np.polyfit(
            ks, [math.log10(lam[k]) for k in ks], 1)[0])
        rows = [p for p in pts if p["c"] == c]
        climb = [p for p in rows if 1e-13 < p["mZ"] < 0.15]
        nb = [p["nband_c"] for p in climb]
        lm = [math.log10(p["mZ"]) for p in climb]
        a, b0 = np.polyfit(nb, lm, 1)
        beta = float(abs(a))                      # decades per zero
        nstar = float((math.log10(0.25) - b0)/a)
        out[str(int(c))] = {"plunge": abs(plunge), "beta": beta,
                            "nstar": nstar, "nsh": 2*c/math.pi,
                            "ratio": beta/abs(plunge),
                            "nclimb": len(climb)}
    return out


def _regimes(pts, sects):
    lam120 = 1.0 - sects(120.0).slepian_leakage()
    def get(c, t0):
        for p in pts:
            if p["c"] == c and p["t0"] == t0:
                return p
        raise KeyError((c, t0))
    def plunge_mass(p):
        w2 = np.array(p["wZ2"])
        tot = float(w2.sum())
        return float(sum(w2[k] for k in range(len(w2))
                         if 1e-6 <= lam120[k] <= 0.99)/tot)
    sat = [get(120.0, t0)["mZ"] for t0 in (360.0, 380.0, 400.0,
                                           420.0, 440.0)]
    return {
        "below": get(120.0, 200.0)["mZ"],
        "climb1": get(120.0, 240.0)["mZ"],
        "climb2": get(120.0, 260.0)["mZ"],
        "climb3": get(120.0, 300.0)["mZ"],
        "sat_lo": min(sat), "sat_hi": max(sat),
        "pm_below": plunge_mass(get(120.0, 180.0)),
        "pm_mid": plunge_mass(get(120.0, 340.0)),
        "pm_sat": plunge_mass(get(120.0, 420.0)),
    }


def _conj(Z, sects):
    out = []
    for c, t0 in CONJ_PTS:
        params = {"deps": floor_probe3.DEPS3, "c": c, "t0": t0,
                  "nz": floor_probe3.NZ}
        name = f"conj_{int(c)}_{int(t0)}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = floor_probe3.conj_point(sects(c), Z, c, t0)
            ckpt_key.save(name, KEYFILE, params, st)
        out.append(st)
    return out


def _gauge_base(Z, sects):
    """Per DEF_PTS: one base-window ARCH_true build feeding both the
    gauge verdict and the base defect (landing-specific stage)."""
    out = []
    for c, t0 in DEF_PTS:
        params = {"deps": DEPSL, "c": c, "t0": t0,
                  "rlo": t0 - 800.0, "rhi": t0 + 800.0, "NR": 120001}
        name = f"gaugebase_{int(c)}_{int(t0)}"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            S = sects(c)
            S.weil_margin(t0)
            POLE = S.QW - S.ARCH - S.PRIME
            AT = floor_probe5.arch_true(S, t0 - 800.0, t0 + 800.0,
                                        120001, t0)
            QZ = floor_probe5.zform_list(S, Z, t0)
            nq = lambda M: float(np.linalg.norm(M))
            QWt = AT + POLE + np.conj(S.PRIME)
            QWt = (QWt + QWt.conj().T)/2
            QWc = AT + POLE + S.PRIME
            QWc = (QWc + QWc.conj().T)/2
            st = {
                "c": c, "t0": t0,
                "arch_gauge": nq(AT - np.conj(S.ARCH))/nq(AT),
                "true_vs_QZ": nq(QWt - QZ)/nq(QWt),
                "true_vs_cQZ": nq(QWt - np.conj(QZ))/nq(QWt),
                "code_vs_QZ": nq(QWc - QZ)/nq(QWc),
                "code_vs_cQZ": nq(QWc - np.conj(QZ))/nq(QWc),
            }
            ckpt_key.save(name, KEYFILE, params, st)
        out.append(st)
    return out


def _defects(Z, ZE, sects):
    out = {}
    cfgs = [("MATCHED", 380, -TLIST, TLIST, 120001),
            ("ext-MATCH", 660, -TEXT, TEXT, 180001)]
    for c, t0 in DEF_PTS:
        for lab, nlist, rlo, rhi, NR in cfgs:
            params = {"deps": floor_probe5.DEPS5, "c": c, "t0": t0,
                      "list": nlist, "rlo": rlo, "rhi": rhi, "NR": NR}
            name = f"defect_{lab}_{int(c)}_{int(t0)}"
            st = ckpt_key.load(name, KEYFILE, params)
            if st is None:
                st = floor_probe5.defect(
                    sects(c), Z if nlist == 380 else ZE, t0,
                    rlo, rhi, NR)
                ckpt_key.save(name, KEYFILE, params, st)
            out[(lab, c, t0)] = st
    # NR invariance pair at (60,200)
    for lab, NR in (("base", 120001), ("NR-2", 60001)):
        params = {"deps": floor_probe5.DEPS5, "c": 60.0, "t0": 200.0,
                  "list": 380, "rlo": -600.0, "rhi": 1000.0, "NR": NR}
        name = f"defect_{lab}_60_200"
        st = ckpt_key.load(name, KEYFILE, params)
        if st is None:
            st = floor_probe5.defect(sects(60.0), Z, 200.0,
                                     -600.0, 1000.0, NR)
            ckpt_key.save(name, KEYFILE, params, st)
        out[(lab, 60.0, 200.0)] = st
    return out


def _partition(Z, ZE, sects):
    params = {"deps": DEPSL, "pt": [120.0, 300.0],
              "sweepT": [400.0, 653.7], "text": TEXT}
    name = "part_landing"
    st = ckpt_key.load(name, KEYFILE, params)
    if st is None:
        c, t0 = 120.0, 300.0
        S = sects(c)
        n = S.n
        S.weil_margin(t0)
        oPR = floor_probe4.odd(S.PRIME, n)
        betas = {}
        for T in (400.0, 653.7):
            sub = Z[Z <= T]
            oQ = floor_probe4.odd(floor_probe4.zform(S, sub, t0), n)
            betas[str(T)] = floor_probe4.proj(oQ, oPR)
        base = floor_probe4.odd(floor_probe4.zform(S, Z, t0), n)
        tail = floor_probe4.odd(floor_probe4.zform(S, ZE, t0), n)
        btail = floor_probe4.proj(tail, oPR)
        mats = floor_probe4.prime_mats_per_n(S, t0)
        keys = sorted(mats)
        omats = [floor_probe4.odd(mats[k], n) for k in keys]
        Gm = np.array([[np.real(np.sum(np.conj(a)*b)) for b in omats]
                       for a in omats])
        rhs = np.array([np.real(np.sum(np.conj(a)*base))
                        for a in omats])
        bfit = np.linalg.lstsq(Gm, rhs, rcond=None)[0]
        big = [(k, float(b)) for k, b, m in
               zip(keys, bfit, omats) if float(np.linalg.norm(m)) > 1.5]
        st = {"betas": betas, "btail": btail, "per_n": big}
        ckpt_key.save(name, KEYFILE, params, st)
    return st


def landing_stage():
    Z = zeros380()
    ZE = floor_probe4.ext_zeros()
    sects_d = {}
    def sects(c):
        if c not in sects_d:
            sects_d[c] = TwoSided(c)
        return sects_d[c]
    pts = _ladder_points(Z, sects)
    st = {
        "fits": _fits(pts, sects),
        "regimes": _regimes(pts, sects),
        "conj": _conj(Z, sects),
        "gauge": _gauge_base(Z, sects),
        "defects": {f"{k[0]}|{k[1]:.0f}|{k[2]:.0f}": v
                    for k, v in _defects(Z, ZE, sects).items()},
        "partition": _partition(Z, ZE, sects),
    }
    return st


def load_or_run():
    params = {"deps": DEPSL, "conj_pts": CONJ_PTS,
              "def_pts": DEF_PTS, "tlist": TLIST, "text": TEXT}
    st = ckpt_key.load("floor_arc_landing", KEYFILE, params)
    if st is None:
        st = landing_stage()
        ckpt_key.save("floor_arc_landing", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    st = load_or_run()
    for c in ("60", "120"):
        f = st["fits"][c]
        print(f"c={c}: beta {f['beta']:.3f} nstar {f['nstar']:.1f} "
              f"nsh {f['nsh']:.1f} ratio {f['ratio']:.2f}")
    print("landing stage complete", flush=True)
