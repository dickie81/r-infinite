#!/usr/bin/env python3
"""THE STRUCTURAL QUESTION (owner: "The structural question first
pls"): does the full Weil form's ground-state margin lambda_1(delta)
vanish at a prime-power threshold? The measured half: the margin
CURVE across three regimes on a fine delta-grid.

THE CURVE. lambda_1(delta) = the minimum L^2-Rayleigh quotient of
the full semi-local Weil form on test functions supported in
[-delta/2, delta/2], per parity, on the committed union span
(harmonics + rough + fractional Gegenbauer edges; a variational
UPPER bound on the true ground state at every point, tight to the
span). The full form per regime:
    delta <  log 2 : the archimedean form (no prime shift)
    [log 2, log 3) : + the prime-2 shift            (Theorem 1bj)
    [log 3, log 4) : + the prime-2 and prime-3 shifts (A417)
At each threshold the incoming prime's shift acts only on the
sliver |t| in [log p - a, a], whose width vanishes at the
threshold -- so the FULL form is continuous in delta across every
threshold; the WRONG form (the previous regime's) is what the
Connes-Consani remark and A417's diagnostic show turning negative.
Both are recorded: the full form on the grid, the wrong form at
the first grid points past each threshold.

GRID. delta from 0.50 to 1.38 in steps of 0.02, plus the
threshold-adjacent points 0.69/0.70 and 1.09/1.10 and the window
top 1.386 (log 4 - 0.0003); both parities; GL-panel base 0.008
(the Stage-0b adjudication's middle base: lambda_1 floor ~1e-9).

OUTPUT per cell: lambda_1, lambda_2 (the section's own), sigma at
the ground-state vector, the pipeline's block-CS residual; a
decay-law fit (log lambda_1 against delta, per regime and
parity) printed at the end -- a description of the curve, not a
theorem.

CHECKS. 7: classical. 8: no hypothesis input. Keying law: every
producing file in every key (executable content). A research
probe; float64; not a tower member.
"""
import math, os, sys, time

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

import ckpt_key
import twoprime_recon as TR
from twoprime_recon import cell, PRIMES_ONE, PRIMES_TWO


def _sha(name):
    return ckpt_key.code_sha(os.path.join(HERE, name))


DEPSM = {f: _sha(f) for f in ("twoprime_recon.py",
                              "oneprime_fractional.py",
                              "oneprime_push.py")}
KEYFILE = os.path.join(HERE, "twoprime_margin.py")

LOG2, LOG3, LOG4 = math.log(2), math.log(3), math.log(4)
BASE = 0.008
GRID = sorted(set([round(0.50 + 0.02*k, 2) for k in range(45)]
                  + [0.69, 0.70, 1.09, 1.10, 1.386]))
GRID = [d for d in GRID if d < LOG4]


def regime(delta):
    if delta < LOG2:
        return "arch", ()
    if delta < LOG3:
        return "one", PRIMES_ONE
    return "two", PRIMES_TWO


def wrong_form(delta):
    """The previous regime's primes, at the first points past a
    threshold (the diagnostic)."""
    if LOG2 <= delta < LOG2 + 0.05:
        return "arch-wrong", ()
    if LOG3 <= delta < LOG3 + 0.05:
        return "one-wrong", PRIMES_ONE
    return None


def run():
    params = {"deps": DEPSM, "grid": GRID, "base": BASE,
              "nus": TR.OF.NUS, "nfr": TR.OF.NFR, "nrough": TR.OF.NROUGH}
    st = ckpt_key.load("twoprime_margin", KEYFILE, params,
                       kfun=ckpt_key.code_key)
    if st is None:
        st = ckpt_key.load("twoprime_margin_partial", KEYFILE, params,
                           kfun=ckpt_key.code_key) or {}
    t0 = time.time()
    for delta in GRID:
        for parity in ("even", "odd"):
            jobs = [regime(delta)]
            w = wrong_form(delta)
            if w is not None:
                jobs.append(w)
            for tag, primes in jobs:
                key = f"{tag}:{parity}:{delta:g}"
                if key in st:
                    continue
                r = cell(delta/2, parity, primes, base=BASE)
                st[key] = {"lambda1": r["lambda1"], "lambda2": r["lambda2"],
                           "sigma": r["own"]["sigma"], "minres": r["minres"],
                           "dim": r["dim"]}
                print(f"MARGIN {tag:10s} {parity:4s} delta {delta:g}: lambda1 "
                      f"{r['lambda1']:+.3e} lambda2 {r['lambda2']:+.3e} sigma "
                      f"{r['own']['sigma']:.2e} [{time.time() - t0:.0f}s]",
                      flush=True)
                ckpt_key.save("twoprime_margin_partial", KEYFILE, params, st,
                              kfun=ckpt_key.code_key)
    ckpt_key.save("twoprime_margin", KEYFILE, params, st,
                  kfun=ckpt_key.code_key)
    # the decay-law description per regime and parity
    print("DECAY (least squares of log10 lambda_1 on delta, full form, "
          "lambda_1 > 5e-9 only):", flush=True)
    for parity in ("even", "odd"):
        for tag in ("arch", "one", "two"):
            pts = [(d, st[f"{tag}:{parity}:{d:g}"]["lambda1"]) for d in GRID
                   if f"{tag}:{parity}:{d:g}" in st]
            pts = [(d, l) for d, l in pts if l > 5e-9]
            if len(pts) >= 3:
                x = np.array([p[0] for p in pts]); y = np.log10([p[1] for p in pts])
                A = np.vstack([x, np.ones_like(x)]).T
                slope, icpt = np.linalg.lstsq(A, y, rcond=None)[0]
                resid = float(np.sqrt(np.mean((A @ [slope, icpt] - y)**2)))
                print(f"  {tag:4s} {parity:4s}: {len(pts)} points, "
                      f"{-slope:.2f} decades per unit delta (rms {resid:.2f} "
                      f"decades); lambda1 from {pts[0][1]:.2e} at {pts[0][0]:g} "
                      f"to {pts[-1][1]:.2e} at {pts[-1][0]:g}", flush=True)
    return st


if __name__ == "__main__":
    run()
    print("two-prime margin curve complete", flush=True)
