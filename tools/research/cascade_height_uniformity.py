#!/usr/bin/env python3
"""Theorem 1bh verifier: the height-uniformity arc -- the aperture
dial, the out-of-sample tau* law, the height-uniform floor law,
the resolved low-height case, and the arithmetic side verified at
the critical windows through height 2340 with moving prime sets.

The chain (the arc's commissions, each with its committed
instrument and RESULT):
(1) THE APERTURE DIAL (height_uniformity.py): at fixed aperture A
    the high heights are deeper into saturation, so the fragile
    hair-thin regime is ONE band per aperture, at tau*(A) =
    2pi e^(2A) -- derived at A = 2 by Poisson summation, and here
    verified OUT-OF-SAMPLE at A = 1.5/2.5/3.0 (critical windows at
    heights 127/933/2536; a factor ~20). The tight mean Q(top) =
    ln(tau0/2pi) is aperture-independent as the algebra demands.
(2) THE HEIGHT-UNIFORM FLOOR LAW: under the declared recipe the
    climb rate is beta = 1.09-1.37 decades per in-band zero at
    every aperture (spread 1.26x), and the deep margins at MATCHED
    count deficit are height-stable for A >= 2 (d ~ 5.4: 1.14e-7 /
    1.10e-7 / 6.5e-8 at heights 260/630/1580; d ~ 8.4: 8.1e-11 /
    9.7e-11 at 550/1350): THE RACE CURVE IS FLAT over the measured
    span. The A = 1.5 depression is RESOLVED as deterministic band
    geometry (height_anomaly.py + the committed gradient test:
    mirrors can only raise margins -- PSD; the smooth-counting
    comb with no fluctuations reproduces the depression while the
    constant-density comb sits 7-9 decades higher; the local
    Nyquist line falls inside the wide low-aperture band and the
    crossing smears) -- not a height effect, not arithmetic.
(3) THE ARITHMETIC SIDE AT THE CRITICAL WINDOWS (height_arith.py,
    height_residue.py): under matched s-windows and THE POLE RULE
    (the pole pair included iff A*tau0 <= 2200, within quadrature
    validity; omitted where analytically negligible -- a computed
    negligible term is unbounded noise, demonstrated: |u| = 1.9 at
    (3, 2000) where truth is superexponentially small, closure
    4e-2 -> 3.4e-5 on omission), the windowed explicit formula
    closes OPERATOR-WISE at every point (1e-5 class at A = 3;
    <= 2e-4 at A = 2.5) and m_W >= 0 arithmetic-only at all five
    critical-window points -- at height 1580 from 98 prime powers
    (primes to 403), hair-thin positive (6.3e-8) with dm/m = 0.01%
    and the null cancellation A/P = -1 to four digits.
Capability note (stated with its caveat): m_W at tau*(A) is an
arithmetic-only RH FALSIFIER at height 2pi e^(2A) -- primes to
tau*/2pi plus a fixed-cost integral, no zero computations; a
negative value anywhere disproves RH. Spot-checks at single
heights are cheap; SWEEPING a height range multiplies by the
core-local window count, and no complexity advantage over
classical verification at accessible heights is claimed.

Stage: height_landing.load_or_run() (the producing code in the
substrate per round-229 F7), content-keyed per the standing law
(A361/A363: module shas + full config + ordinate bytes, z_sha and
zext_sha both).

Gates:
  g0  pins set
  g1  the rung ladders pinned: three climb values per rung
      (rel 0.1), twelve pins spanning heights 116-2000
  g2  the tau* calendar: the deficit-anchored deep points at
      A = 2.5/3.0 in (1e-11, 1e-9); the A = 1.5 climb straddles
      tau* = 126.2 (m(112) < 1e-12, m(130) > 1e-8)
  g3  the tight mean: qrel_max per rung <= 0.002/0.01/0.03/0.05
      (the scatter grows as the band narrows -- feature-local)
  g4  beta height-uniform: each rung in (1.0, 1.5); max/min
      <= 1.35
  g5  matched-deficit stability: the d~5.4 triple within 2.5x;
      the d~8.4 pair within 2x
  g6  the anomaly resolution: m_dir <= m_full at every A = 1.5
      ablation point (the PSD direction); the far-mirror control
      within 5%; the gradient comb within 12x of the zeros at
      both anomaly points; the constant comb >= 1e4 x the zeros;
      the A = 3 control combs within 3x of the zeros
  g7  Phase-2 closures pinned {8.3e-5, 1.8e-4, 8.8e-6, 3.4e-5,
      2.4e-5} (rel 0.5) and every closure <= 3e-4
  g8  arithmetic positivity: m_W > 0 at all five points, pinned;
      |dm/m| <= 0.003 at every point
  g9  the null cancellation: |PRIME/ARCH + 1| <= 1e-3 at the deep
      points (630, 1580)
  g10 the pole rule demonstrated: |u| pinned {1.93, 1.48}
      (rel 0.3) at (3, 2000/2340) and the with-pole closure
      >= 100x the pole-omitted closure at both
  g11 the chain obligation to cascade_floor_closure.py
      (Theorem 1bg) met
  g12 the 1bh paper needles and the footer census (backticked
      >= 2; the anchored count and range needles)

Sabotage suite (live at the landing battery; edit-run-observe-
restore):
  (a) substrate mangle -- height_arith.py's prime phase
      orientation (the true-gauge e^(-i tau0 u) -> e^(+i tau0 u))
      -> the arith families and the consolidated stage
      self-invalidate and recompute; the closure collapses (the
      conjugate-gauge lesson of 1bg), g7-g9 fail
  (b) pin mangle -- a g1 ladder pin -> REUSED, one gate, exit 1
  (c) census revert -- footer 84 -> 83 -> g11 (chain census) +
      g12, two-gate detection
"""
import math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from height_landing import load_or_run

PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

st = load_or_run()
RU, AN, GR = st["rungs"], st["anom"], st["grad"]
AR, PD = st["arith"], st["pdiag"]

PIN_LAD = {("1.5", "116.5"): 4.712e-11, ("1.5", "120.0"): 3.789e-10,
           ("1.5", "130.0"): 1.483e-7, ("2.0", "260.0"): 1.139e-7,
           ("2.0", "280.0"): 6.646e-6, ("2.0", "300.0"): 3.760e-4,
           ("2.5", "550.0"): 8.069e-11, ("2.5", "630.0"): 1.102e-7,
           ("2.5", "770.0"): 6.787e-4, ("3.0", "1350.0"): 9.655e-11,
           ("3.0", "1580.0"): 6.480e-8, ("3.0", "2000.0"): 9.474e-4}
PIN_REL = {(2.5, 630.0): 8.27e-5, (2.5, 880.0): 1.81e-4,
           (3.0, 1580.0): 8.84e-6, (3.0, 2000.0): 3.41e-5,
           (3.0, 2340.0): 2.36e-5}
PIN_U = {2000.0: 1.932, 2340.0: 1.477}

for a, r in RU.items():
    print(f"  rung A={a}: beta {r['beta']:.4f} ({r['nsel']} pts) "
          f"qrel {r['qrel']:.4f}", flush=True)
for g in GR:
    print(f"  grad ({g['A']:.1f},{g['t0']:.0f}): zeros {g['m_zeros']:.3e} "
          f"grad {g['m_grad']:.3e} const {g['m_const']:.3e}", flush=True)
for a in AR:
    print(f"  arith ({a['A']:.1f},{a['t0']:.0f}) pole={a['pole']}: mW "
          f"{a['mW']:+.4e} mZ {a['mZ']:+.4e} rel {a['rel']:.2e} "
          f"A/P {a['arch']:+.3f}/{a['prime']:+.3f}", flush=True)
for p in PD:
    print(f"  pdiag ({p['A']:.1f},{p['t0']:.0f}): |u| {p['norm_u']:.3f} "
          f"with-pole rel {p['rel_withpole']:.2e}", flush=True)

# ---------------------------------------------------------------- g0
gate("g0 pins set", all(v for v in PIN_LAD.values())
     and all(v for v in PIN_REL.values()))

# ---------------------------------------------------------------- g1
ok = all(abs(RU[a]["rows"][t]/pin - 1) < 0.1
         for (a, t), pin in PIN_LAD.items())
gate("g1 the rung ladders pinned: twelve climb values across "
     "heights 116-2000 (rel 0.1)", ok)

# ---------------------------------------------------------------- g2
ok = 1e-11 < RU["2.5"]["rows"]["550.0"] < 1e-9
ok &= 1e-11 < RU["3.0"]["rows"]["1350.0"] < 1e-9
ok &= RU["1.5"]["rows"]["112.0"] < 1e-12
ok &= RU["1.5"]["rows"]["130.0"] > 1e-8
gate("g2 the tau* calendar out-of-sample: the deficit-anchored "
     "deep points at A = 2.5/3.0; the A = 1.5 climb straddles "
     "126.2", ok)

# ---------------------------------------------------------------- g3
QMAX = {"1.5": 0.002, "2.0": 0.01, "2.5": 0.03, "3.0": 0.05}
ok = all(RU[a]["qrel"] <= QMAX[a] for a in QMAX)
gate("g3 the tight mean Q(top) = ln(tau0/2pi), aperture-"
     "independent (band-scatter bounds per rung)", ok)

# ---------------------------------------------------------------- g4
bs = [RU[a]["beta"] for a in RU]
ok = all(1.0 < b < 1.5 for b in bs) and max(bs)/min(bs) <= 1.35
gate("g4 beta height-uniform: every rung in (1.0, 1.5), spread "
     "<= 1.35x", ok)

# ---------------------------------------------------------------- g5
d54 = [RU["2.0"]["rows"]["260.0"], RU["2.5"]["rows"]["630.0"],
       RU["3.0"]["rows"]["1580.0"]]
d84 = [RU["2.5"]["rows"]["550.0"], RU["3.0"]["rows"]["1350.0"]]
ok = max(d54)/min(d54) <= 2.5 and max(d84)/min(d84) <= 2.0
gate("g5 matched-deficit stability: the d~5.4 triple within 2.5x "
     "(heights 260-1580), the d~8.4 pair within 2x -- the race "
     "curve flat", ok)

# ---------------------------------------------------------------- g6
ok = all(r["m_dir"] <= r["m_full"] + 1e-15 for r in AN["1.5"])
ok &= all(abs(r["m_dir"]/r["m_full"] - 1) <= 0.05
          for r in AN["2.5"])
g15 = {f"{g['t0']:.0f}": g for g in GR if g["A"] == 1.5}
ok &= all(1/12 <= g["m_grad"]/g["m_zeros"] <= 12
          for g in g15.values())
ok &= all(g["m_const"]/g["m_zeros"] >= 1e4 for g in g15.values())
g3c = next(g for g in GR if g["A"] == 3.0)
ok &= 1/3 <= g3c["m_grad"]/g3c["m_zeros"] <= 3
ok &= 1/3 <= g3c["m_const"]/g3c["m_zeros"] <= 3
gate("g6 the anomaly resolution: ablation in the PSD direction; "
     "the far control within 5%; the gradient comb reproduces the "
     "depression (const comb >= 1e4x); the A = 3 control tight", ok)

# ---------------------------------------------------------------- g7
ok = all(abs(a["rel"]/PIN_REL[(a["A"], a["t0"])] - 1) < 0.5
         for a in AR)
ok &= all(a["rel"] <= 3e-4 for a in AR)
gate("g7 the Phase-2 operator closures pinned and <= 3e-4 at "
     "every critical-window point (1e-5 class at A = 3)", ok)

# ---------------------------------------------------------------- g8
ok = all(a["mW"] > 0 for a in AR)
ok &= all(abs(a["mW"] - a["mZ"]) <= 0.003*abs(a["mZ"]) for a in AR)
gate("g8 arithmetic-only Weil positivity at all five points; "
     "|dm/m| <= 0.003 (the derived-g4 class, out-of-sample in "
     "aperture)", ok)

# ---------------------------------------------------------------- g9
deep = [a for a in AR if a["t0"] in (630.0, 1580.0)]
ok = all(abs(a["prime"]/a["arch"] + 1) <= 1e-3 for a in deep)
gate("g9 the null cancellation PRIME/ARCH = -1 within 1e-3 at the "
     "deep points (primes to 148/403)", ok)

# --------------------------------------------------------------- g10
ok = all(abs(p["norm_u"]/PIN_U[p["t0"]] - 1) < 0.3 for p in PD)
rel_np = {a["t0"]: a["rel"] for a in AR if a["A"] == 3.0}
ok &= all(p["rel_withpole"] >= 100*rel_np[p["t0"]] for p in PD)
gate("g10 the pole rule demonstrated: the noise magnitudes pinned "
     "and the with-pole closure >= 100x the omitted one", ok)

# --------------------------------------------------------------- g11
from cascade_tower import chain_ok
gate("g11 the chain obligation to cascade_floor_closure.py "
     "(Theorem 1bg) met", chain_ok("cascade_floor_closure.py"))

# --------------------------------------------------------------- g12
import re
normp = re.sub(r"\s+", " ", paper)
plain = normp.replace("**", "")
needles = [
    "Theorem 1bh (the height-uniformity arc",
    "the aperture dial",
    "out-of-sample at every other aperture",
    "the race curve is flat",
    "the pole rule",
    "an arithmetic-only falsifier",
    "no RH leverage claimed",
]
ok = all(nd in plain for nd in needles)
for nd in needles:
    if nd not in plain:
        print(f"  g12 MISSING: {nd!r}", flush=True)
ok &= paper.count("`cascade_height_uniformity.py`") >= 2
ok &= "the **84 scripts cited in place** above" in normp
ok &= "extended by Theorems 1i–1bh:" in normp
gate("g12 the 1bh paper needles and the footer census (backticked "
     ">= 2; the anchored count and range needles)", ok)

print(("\nALL GATES PASS (13/13)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
