#!/usr/bin/env python3
"""The floor-law derivation, phase 3: the drift rerun with FULL-RANGE
combs. Phase 2's Part B used band combs (window + 40 slack) and the
phase-1 leakage identity itself explains why that pollutes the
comparison: the margin IS the distant-sample energy, so truncating
the comb's tail removes sampled energy and depresses the twin's
margins by ~0.4 decades (measured: band comb -6.976 vs full comb
-6.539 at (2, 260)) -- pushing the certified true-zero values to
artificially high percentiles. The certified 1bh race values were
computed against full ordinate lists (kmax = 380/810/2270); this
phase matches that coverage with full-range combs (indices
1..kmax) and per-height budget variance sigma^2(T) = Vsat(T) - 1/6.

Deliverable: the drift verdict -- the twin ladder across the
certified d ~ 5.4 race triple with correct coverage, the certified
values' z-scores in the twin distributions, and the predicted
height drift (comb drift + discount growth) against the measured
flat race curve.

Check 7/8 clean as phase 1/2. Keying: every producing file in the
key; comb-only inputs.
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from fold_D import inv_Nbar, TWO_PI
from height_uniformity import ASect

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS3 = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "floor_theory.py", "floor_theory2.py",
                              "floor_theory3.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

MERTENS = 0.2614972128476428
SIXTH = 1.0/6.0
NDRAW = 80
SEED = 32000
# the certified d ~ 5.4 race triple with its coverage kmax and the
# certified true-zero margins (1bh, gated g5)
PTS = [(2.0, 260.0, 380, 1.139e-7),
       (2.5, 630.0, 810, 1.102e-7),
       (3.0, 1580.0, 2270, 6.48e-8)]


def vsat(T):
    return (math.log(math.log(T/TWO_PI)) + MERTENS + 1)/math.pi**2


def run():
    params = {"deps": DEPS3, "ndraw": NDRAW, "seed": SEED}
    st = ckpt_key.load("floor_theory_p3", KEYFILE, params)
    if st is not None:
        print("REUSED phase-3 state")
        for k, r in st.items():
            print(f"{k}: comb {r['comb']:+.3f} twin {r['mean']:+.3f}"
                  f"+-{r['sd']:.3f} | certified {r['cert']:+.3f} "
                  f"(z {r['z']:+.2f})", flush=True)
        return st
    S = ASect(120.0)
    st = {}
    for Ap, t0, kmax, mcert in PTS:
        g0s = np.array([inv_Nbar(float(j)) for j in range(1, kmax+1)])
        m_comb = S.measures(g0s, t0, Ap)["m"]
        s2 = vsat(t0) - SIXTH
        sig = math.sqrt(s2)
        rng = np.random.default_rng(SEED + int(t0))
        ls = []
        for _ in range(NDRAW):
            d = rng.standard_normal(kmax)*sig
            g = np.array([inv_Nbar(j - 0.5 + d[j-1], g0=g0s[j-1])
                          for j in range(1, kmax+1)])
            m = S.measures(g, t0, Ap)["m"]
            ls.append(math.log10(max(m, 1e-300)))
        ls = np.array(ls)
        lcert = math.log10(mcert)
        z = (lcert - ls.mean())/ls.std()
        st[f"{Ap:g}:{t0:g}"] = {
            "comb": math.log10(max(m_comb, 1e-300)), "sig2": s2,
            "mean": float(ls.mean()), "med": float(np.median(ls)),
            "sd": float(ls.std()), "cert": lcert, "z": float(z),
            "kmax": kmax}
        print(f"A={Ap:.1f} t0={t0:5.0f} (kmax {kmax}, sig^2 {s2:.4f})"
              f": comb {math.log10(max(m_comb,1e-300)):+.3f} | twin "
              f"{ls.mean():+.3f}+-{ls.std():.3f} (sem "
              f"{ls.std()/math.sqrt(NDRAW):.3f}) | certified "
              f"{lcert:+.3f} (z {z:+.2f})", flush=True)
    ckpt_key.save("floor_theory_p3", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("floor-theory phase 3 complete", flush=True)
