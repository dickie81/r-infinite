#!/usr/bin/env python3
"""THE ONE-PRIME ARC, STAGE B1, ROUND 4 -- the even-top push:
[1.0, log 3), the last unclosed stretch of the window.

Commission: "Let's attack A first" (the first next move at the
round-3 landing: the even-top refinement push -- quadrature +
richer edge families on [1.0, log 3), where the ODD sector already
closes, so the even top is all that separates the arc from
full-window feasibility closure).

THE TWO LEVERS.
  (i)  QUADRATURE: round 3's even-top sigma plateaued at
       ~1.5-1.9e-4 and was still falling under refinement at
       delta = 1.0 (-9.4e-7 -> -2.7e-7 from base 0.012 -> 0.008):
       part of the plateau is floor, not physics. This round runs
       a base ladder {0.012, 0.008, 0.005} per cell so the
       saturation of both sigma and the Temple value is MEASURED,
       and only ladder-stable closures are claimed.
  (ii) EDGE RESOLUTION: the round-3 optimum put 57-73% of its
       weight in the edge families; near the window top the
       extremal's edge structure may need finer exponent
       resolution. The family grid grows to nu in
       {0.6, 0.75, 1.0, 1.25} (edge exponents s in
       {0.1, 0.25, 0.5, 0.75}) with nfr = 12 modes each, and the
       even rough family to 13 harmonics.

THE ADVERSE TRADEOFF, STATED. Enriching the span lowers its
section lambda_2 -- the tightest available (and safest) ell_2
stand-in -- which RAISES the needed sigma bar sqrt(rho(ell_2-rho))
even as it lowers sigma. The per-cell print shows both sides
(sigma vs needed), so the tradeoff's outcome is visible, not
assumed. Temple validity still rests on the stand-in ell_2 (the
standing caveat); the half rung is reported throughout.

MACHINERY: oneprime_fractional's t-space operator pipeline
(validated at five digits against the adjudicated sigma anchor),
parameterized here by (base, nus, nfr, nrough); its gF1/gF4 gates
run per cell.

CHECKS. 7: classical. 8: no hypothesis input.

Keying law: every producing file in every key.
"""
import hashlib, math, os, sys

import numpy as np
from scipy.linalg import eigh as scipy_eigh

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
from oneprime_bridge import build_Q64
from oneprime_push import temple_opt
import oneprime_fractional as opf

def _sha(name):
    return hashlib.sha256(
        open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPST = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "height_uniformity.py",
                              "oneprime_bridge.py",
                              "oneprime_certificate.py",
                              "oneprime_push.py",
                              "oneprime_fractional.py",
                              "oneprime_top.py")}
KEYFILE = os.path.join(HERE, "oneprime_top.py")

NUS_TOP = (0.6, 0.75, 1.0, 1.25)
NFR_TOP = 12
NROUGH_TOP = 13
BASES = (0.008, 0.005, 0.003)
XBASE = 0.002          # the extra rung for the two nearest cells
CELLS = (1.00, 1.02, 1.05, 1.07, 1.09)


def run():
    params = {"deps": DEPST, "nus": NUS_TOP, "nfr": NFR_TOP,
              "nrough": NROUGH_TOP, "bases": BASES,
              "cells": CELLS}
    st = ckpt_key.load("oneprime_top", KEYFILE, params)
    if st is not None:
        return st
    st = {}
    for delta in CELLS:
        a = delta/2
        Qc, Gc, _, _, _ = build_Q64(delta, parity="even")
        rows = {}
        bases = BASES + ((XBASE,) if delta <= 1.021 else ())
        for base in bases:
            md, N, M, S, gf4, grids = opf.cell_matrices(
                a, "even", base=base, nus=NUS_TOP, nfr=NFR_TOP,
                nrough=NROUGH_TOP)
            assert gf4 < 1e-8, f"gF4 FAIL {delta:g}: {gf4:.1e}"
            tn, tw, B, TB = grids
            idx = np.arange(opf.NHALF)
            gf1 = float(np.linalg.norm(
                M[np.ix_(idx, idx)] - Qc)/np.linalg.norm(Qc))
            assert gf1 < 5e-4, f"gF1 FAIL {delta:g}: {gf1:.1e}"
            d = 1.0/np.sqrt(np.diag(N))
            Nn = d[:, None]*N*d[None, :]
            ev, U = np.linalg.eigh(Nn)
            keep = ev > 1e-4
            Wh = ((U[:, keep]/np.sqrt(ev[keep])[None, :]).T
                  * d[None, :])
            Bw = Wh @ B
            TBw = Wh @ TB
            NA = 2*(Bw*tw[None, :]) @ Bw.T
            MA = 2*(Bw*tw[None, :]) @ TBw.T
            SA = 2*(TBw*tw[None, :]) @ TBw.T
            NA, MA, SA = ((NA + NA.T)/2, (MA + MA.T)/2,
                          (SA + SA.T)/2)
            l2A = float(scipy_eigh(MA, NA, eigvals_only=True)[1])
            mu, c = temple_opt(NA, MA, SA, l2A)
            nn = float(c @ NA @ c)
            rho = float(c @ MA @ c)/nn
            sig = math.sqrt(max(float(c @ SA @ c)/nn - rho*rho,
                                0.0))
            sneed = math.sqrt(max(rho*(l2A - rho), 0.0))
            muh, _ = temple_opt(NA, MA, SA, 0.5*l2A)
            # the deep-cutoff variant at the finest rungs: the
            # value-whitening's per-vector sigma^2 >= 0 exactness
            # makes 1e-5 admissible; ladder stability across bases
            # remains the guard against noise-direction artifacts
            keep5 = ev > 1e-5
            Wh5 = ((U[:, keep5]/np.sqrt(ev[keep5])[None, :]).T
                   * d[None, :])
            B5 = Wh5 @ B
            TB5 = Wh5 @ TB
            N5 = 2*(B5*tw[None, :]) @ B5.T
            M5 = 2*(B5*tw[None, :]) @ TB5.T
            S5 = 2*(TB5*tw[None, :]) @ TB5.T
            N5, M5, S5 = ((N5 + N5.T)/2, (M5 + M5.T)/2,
                          (S5 + S5.T)/2)
            l25 = float(scipy_eigh(M5, N5, eigvals_only=True)[1])
            mu5, c5 = temple_opt(N5, M5, S5, l25)
            nn5 = float(c5 @ N5 @ c5)
            rho5 = float(c5 @ M5 @ c5)/nn5
            sig5 = math.sqrt(max(float(c5 @ S5 @ c5)/nn5
                                 - rho5*rho5, 0.0))
            rows[f"{base:g}"] = {
                "dim": NA.shape[0], "gf1": gf1, "l2A": l2A,
                "temple": mu, "half": muh, "rho": rho,
                "sigma": sig, "sigma_needed": sneed,
                "dim5": N5.shape[0], "temple5": mu5, "rho5": rho5,
                "sigma5": sig5, "l25": l25}
            print(f"TOP delta {delta:g} base {base:g} (dim "
                  f"{NA.shape[0]} gF1 {gf1:.1e}): Temple "
                  f"{mu:+.3e} (half {muh:+.3e}) rho {rho:+.3e} "
                  f"sigma {sig:.3e} (needed {sneed:.3e}) l2A "
                  f"{l2A:.3e} | cut5 dim {N5.shape[0]} Temple "
                  f"{mu5:+.3e} sigma {sig5:.3e}", flush=True)
        st[f"{delta:g}"] = rows
    ckpt_key.save("oneprime_top", KEYFILE, params, st)
    return st


if __name__ == "__main__":
    run()
    print("one-prime even-top push complete", flush=True)
