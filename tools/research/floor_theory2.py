#!/usr/bin/env python3
"""The floor-law derivation, phase 2: the jitter discount and the
height drift (continuing floor_theory.py's phase 1, whose results
stand: the leakage identity confirmed, the 2-modes-per-zero price
DERIVED as complex-vanishing = 2 real constraints -- edge advance
fit +2.00 -- and beta composed to 10% as 2 x the per-mode leakage
decade-rate, which follows the Landau-Widom form pi^2/ln(kappa c),
kappa ~ 3-4 drifting; the certified "approximately c-flat" and the
LW slow decline are indistinguishable at measured precision).

PART A -- THE DISCOUNT LAW. The twin's jitter lowers the margin
below the comb (the certified comb > zeta > CUE ordering; the min's
concavity). Measure E[log10 m] on white-noise displacement ladders
sigma = f x sigma_zeta at f in {0, 0.5, 0.75, 1, 1.5, 2}, at three
tau0 (climb / deep / near-saturation), and fit the discount's form
in sigma^2. Pre-registered expectation: the discount grows with the
in-band count and with sigma^2 (the 1bc fit R = -0.126 - 0.0056 Z);
the form (linear vs saturating in sigma^2) is the measurement.

PART B -- THE DRIFT PREDICTION. In the twin model the height enters
the matched-deficit margin ONLY through sigma^2(T) = Vsat(T) - 1/6,
Vsat = (ln ln(T/2pi) + Mertens + 1)/pi^2 -- the derived budget --
plus the (computable) comb geometry at the certified race points
(A, tau0) = (2, 260), (2.5, 630), (3, 1580), all d ~ 5.4, c = 120.
sigma^2 grows 0.094 -> 0.116 -> 0.134 across the triple (+42%).
The prediction: the twin's E[log10 m] ladder across the triple IS
the derived race curve; the certified single-realization values
(1.139e-7 / 1.102e-7 / 6.48e-8 -- flat within 2x) must sit at
consistent percentiles, and the predicted drift (comb drift + the
discount's growth with sigma^2) is the derived form of the
height-stationarity conjecture: FLAT MODULO THE BUDGET DRIFT.

Check 7: Slepian sections, Gaussian displacement fields, smooth
counting -- classical; no semiclassics; no cascade quantity. Check
8: no hypothesis input. Keying per the standing law: every
producing file in the key; full config in params; comb-only inputs
(no ordinate data anywhere in this instrument).
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from fold_D import inv_Nbar, TWO_PI
from fold_surrogate import Sect, A as A2, NZ
from height_uniformity import ASect


def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS2 = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "floor_theory.py", "floor_theory2.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

MERTENS = 0.2614972128476428
SIXTH = 1.0/6.0
NDRAW = 80
SEED = 31000


def vsat(T):
    return (math.log(math.log(T/TWO_PI)) + MERTENS + 1)/math.pi**2


def comb_band(t0, W, slack=40.0):
    lo, hi = t0 - W - slack, t0 + W + slack
    js, g = [], 20.0
    j = 1
    # find the index range by marching inv_Nbar
    while True:
        g = inv_Nbar(float(j), g0=g)
        if g > hi:
            break
        if g >= lo:
            js.append(j)
        j += 1
        if j > 10**6:
            raise RuntimeError("band walk failed")
    return np.array(js, dtype=float)


def jittered(js, sig, rng, g0s):
    d = rng.standard_normal(len(js))*sig
    out = np.empty(len(js))
    for i, (j, dd) in enumerate(zip(js, d)):
        out[i] = inv_Nbar(j - 0.5 + dd, g0=g0s[i])
    return out


def run():
    params = {"deps": DEPS2, "ndraw": NDRAW, "seed": SEED}
    st = ckpt_key.load("floor_theory_p2", KEYFILE, params)
    if st is not None:
        print("REUSED phase-2 state")
        return st
    st = {"discount": {}, "drift": {}}
    # ---------------- PART A: the discount ladder ----------------
    S = Sect(120.0)
    comb = np.array([inv_Nbar(float(k)) for k in range(1, NZ + 1)])
    sig_base = math.sqrt(vsat(320.0) - SIXTH)
    for t0 in (260.0, 300.0, 330.0):
        m_comb = float(S.margin(comb, t0))
        row = {"m_comb": m_comb, "cells": {}}
        for f in (0.5, 0.75, 1.0, 1.5, 2.0):
            rng = np.random.default_rng(SEED + int(t0) + int(100*f))
            sig = f*sig_base
            ls = []
            for _ in range(NDRAW):
                d = rng.standard_normal(NZ)*sig
                g = np.array([inv_Nbar(k - 0.5 + d[k-1],
                                       g0=comb[k-1])
                              for k in range(1, NZ + 1)])
                m = float(S.margin(g, t0))
                ls.append(math.log10(max(m, 1e-300)))
            ls = np.array(ls)
            row["cells"][f"{f:g}"] = {
                "mean": float(ls.mean()), "med": float(np.median(ls)),
                "sd": float(ls.std())}
            print(f"A t0={t0:4.0f} f={f:4.2f} (sig^2 "
                  f"{sig*sig:.4f}): E[log10 m] {ls.mean():+.3f} "
                  f"(comb {math.log10(m_comb):+.3f}, discount "
                  f"{ls.mean()-math.log10(m_comb):+.3f}, sd {ls.std():.3f})",
                  flush=True)
        st["discount"][f"{t0:g}"] = row
    # ---------------- PART B: the drift ladder --------------------
    SA = ASect(120.0)
    for Ap, t0 in ((2.0, 260.0), (2.5, 630.0), (3.0, 1580.0)):
        W = 120.0/Ap
        js = comb_band(t0, W)
        g0s = np.array([inv_Nbar(float(j)) for j in js])
        m_comb = SA.measures(g0s, t0, Ap)["m"]
        s2 = vsat(t0) - SIXTH
        sig = math.sqrt(s2)
        rng = np.random.default_rng(SEED + 7000 + int(t0))
        ls = []
        for _ in range(NDRAW):
            g = jittered(js, sig, rng, g0s)
            m = SA.measures(g, t0, Ap)["m"]
            ls.append(math.log10(max(m, 1e-300)))
        ls = np.array(ls)
        st["drift"][f"{Ap:g}:{t0:g}"] = {
            "m_comb": m_comb, "sig2": s2, "mean": float(ls.mean()),
            "med": float(np.median(ls)), "sd": float(ls.std()),
            "n_band": len(js)}
        print(f"B A={Ap:.1f} t0={t0:5.0f} (sig^2 {s2:.4f}, band "
              f"{len(js)}): comb {math.log10(max(m_comb,1e-300)):+.3f} | "
              f"twin E[log10 m] {ls.mean():+.3f} +- "
              f"{ls.std()/math.sqrt(NDRAW):.3f} (sd {ls.std():.3f})",
              flush=True)
    ckpt_key.save("floor_theory_p2", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("floor-theory phase 2 complete", flush=True)
