#!/usr/bin/env python3
"""Theorem 1bi verifier: the floor law derived -- the leakage
identity, the constraint price, the rate composition, the discount
law, and the budget-drift race curve.

The chain (the arc's commissions, each with its committed record):
"Point the certified surrogate at the Shannon crossing" (the
crossing-sign null, crossing_probe.py) -> "pursue the derivation"
(floor_theory.py phases 1-3). This verifier consumes the three
phase states (content-keyed per the post-eighth-catch law: every
producing file in every key) plus the crossing-null state, and
gates the derivation's claims.

Gates (thirteen, g0-g12; round-240 F5, applied at the round-241
sweep -- the first application was lost to a script abort):
  g0  pins set
  g1  the leakage identity: the in-band residual <= 3e-3 of the
      margin at every deep climb point (t0 <= 290), and the
      density x leakage approximation within a factor [0.03, 0.8]
      at every ladder point
  g2  the constraint price DERIVED: the occupancy-edge advance fit
      in (1.90, 2.10) modes per zero
  g3  the rate composition: beta_comb in (1.15, 1.45) and the
      composed/measured ratio within 15%
  g4  the Landau-Widom form: the per-mode decade rate strictly
      decreasing in c over the four-point scan, and
      pi^2/logit-slope - ln c in (0.9, 1.6) at every c
  g5  the discount law: the f = 1 discounts pinned (rel 0.15) at
      the three regimes; the discount strictly deepening in f at
      every regime; the log-log sigma-exponents in their regime
      windows (deep (1.1, 1.5); crossing (1.9, 2.5);
      near-saturation (1.6, 2.2))
  g6  the 1bc cross-check: the twin discount at (120, 260)
      brackets the certified true-zero R(260) = -0.40 within one
      twin sd
  g7  the drift triple typical: the certified race values at
      |z| <= 2 in the full-coverage twin ladders, each z pinned
      (window 0.5)
  g8  the budget-drift match: predicted decline (comb delta +
      discount delta) and certified decline (-0.245) both
      negative, within 0.15 decades of each other
  g9  the supersession demonstrated: the band-comb margin at
      (2, 260) sits >= 0.3 decades below the full-comb margin
      (the phase-2 Part B pollution mechanism, gated as a
      demonstration)
  g10 the crossing-null record: the count channel closed (uncond
      count sd <= 0.8 at every point; floor fraction 0 at every
      point) and the zeros' twin percentiles in (0.05, 0.95) at
      every window (the typicality verdict)
  g11 the chain obligation to cascade_height_uniformity.py
      (Theorem 1bh) met
  g12 the 1bi paper needles and the footer census (backticked
      >= 2; the anchored count and range needles)

Suite (per the standing protocol):
  (a) mechanism mangle -- e.g. perturb floor_theory.py's spectrum
      quadrature or edge-advance fit window: the content keys
      self-invalidate, the phase recomputes, g2/g3 fail
  (b) pin mangle -> REUSED one-gate failure
  (c) census revert -- footer 85 -> 84 -> g11 (chain census) +
      g12 (needles)
"""
import math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from floor_theory import run as run_p1
from floor_theory2 import run as run_p2
from floor_theory3 import run as run_p3
from crossing_probe import run as run_cx


# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g12', 's': 'Theorem 1bi (the floor law derived', 'form': 'plain'},
    {'g': 'g12', 's': 'the leakage identity', 'form': 'plain'},
    {'g': 'g12', 's': 'one complex vanishing condition is two real constraints', 'form': 'plain'},
    {'g': 'g12', 's': 'the LW slow decline are indistinguishable at measured precision', 'form': 'plain'},
    {'g': 'g12', 's': 'flat modulo the budget drift', 'form': 'plain'},
    {'g': 'g12', 's': 'conspiracy detectors', 'form': 'plain'},
    {'g': 'g12', 's': 'no RH leverage claimed', 'form': 'plain'},
    {'s': '`cascade_floor_theory.py`', 'min': 2, 'g': 'g12'},
    {'s': 'the **87 scripts cited in place** above', 'form': 'ws', 'g': 'g12'},
    {'s': 'extended by Theorems 1i–1bk:', 'form': 'ws', 'g': 'g12'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

P1 = run_p1()
P2 = run_p2()
P3 = run_p3()
CX = run_cx()

PIN_DISC = {"260": -0.498, "300": -0.596, "330": -1.166}
PIN_Z = {"2:260": 0.38, "2.5:630": 1.55, "3:1580": 0.41}
CERT_DECLINE = math.log10(6.48e-8) - math.log10(1.139e-7)  # -0.245

gate("g0 pins set", len(PIN_DISC) == 3 and len(PIN_Z) == 3)

# ---------------------------------------------------------------- g1
rows = P1["ladder"]["120"]
deep = [r for r in rows if r["t0"] <= 290]
ok = all(r["in"]/max(r["m"], 1e-300) <= 3e-3 for r in deep)
ok &= all(0.03 <= r["out"]/max(r["pred_out"], 1e-300) <= 0.8
          for r in rows)
gate("g1 the leakage identity: in-band residual <= 3e-3 at the deep "
     "climb; density x leakage within [0.03, 0.8] everywhere", ok)

# ---------------------------------------------------------------- g2
adv = P1["identity"]["edge_advance"]
gate("g2 the constraint price derived: edge advance in (1.90, 2.10) "
     f"modes/zero (measured {adv:+.2f})", 1.90 <= abs(adv) <= 2.10)

# ---------------------------------------------------------------- g3
beta = abs(P1["identity"]["beta"])  # the stage stores the fit
# slope's sign convention (printed "-1.280"); the law's beta is
# its magnitude -- the first fresh battery caught the raw read
# failing g3 (12/13) and this is the fix, on the record
comp = abs(P1["identity"]["composition"])
ok = 1.15 <= beta <= 1.45 and abs(comp/beta - 1) <= 0.15
gate("g3 the rate composition: beta_comb in (1.15, 1.45), "
     "composed/measured within 15%", ok)

# ---------------------------------------------------------------- g4
cs = ["60", "90", "120", "170"]
rates = [abs(P1["spectrum"][c]["dec_per_mode"]) for c in cs]
ok = all(rates[i] > rates[i+1] for i in range(3))
for c in cs:
    sp = P1["spectrum"][c]
    gap = math.pi**2/abs(sp["logit_slope"]) - sp["ln_c"]
    ok &= 0.9 <= gap <= 1.6
gate("g4 the Landau-Widom form: per-mode rate strictly decreasing "
     "in c; pi^2/slope - ln c in (0.9, 1.6) at every c", ok)

# ---------------------------------------------------------------- g5
ok = True
EXP_WIN = {"260": (1.1, 1.5), "300": (1.9, 2.5), "330": (1.6, 2.2)}
for t0, row in P2["discount"].items():
    cells = row["cells"]
    d1 = cells["1"]["mean"] - math.log10(row["m_comb"])
    ok &= abs(d1/PIN_DISC[t0] - 1) <= 0.15
    fs = ["0.5", "0.75", "1", "1.5", "2"]
    ds = [cells[f]["mean"] - math.log10(row["m_comb"]) for f in fs]
    ok &= all(ds[i] > ds[i+1] for i in range(4))
    slope = float(np.polyfit(np.log([float(f) for f in fs]),
                             np.log([-d for d in ds]), 1)[0])
    ok &= EXP_WIN[t0][0] <= slope <= EXP_WIN[t0][1]
gate("g5 the discount law: f = 1 discounts pinned (rel 0.15), "
     "strictly deepening in f, sigma-exponents in regime windows", ok)

# ---------------------------------------------------------------- g6
row = P2["discount"]["260"]
d1 = row["cells"]["1"]["mean"] - math.log10(row["m_comb"])
sd = row["cells"]["1"]["sd"]
gate("g6 the 1bc cross-check: the twin discount at (120, 260) "
     "brackets the certified R(260) = -0.40 within one sd",
     abs(d1 - (-0.40)) <= sd)

# ---------------------------------------------------------------- g7
ok = True
for k, zpin in PIN_Z.items():
    z = P3[k]["z"]
    ok &= abs(z) <= 2.0 and abs(z - zpin) <= 0.5
gate("g7 the drift triple typical: certified race values |z| <= 2 "
     "in the twin ladders, each z pinned (window 0.5)", ok)

# ---------------------------------------------------------------- g8
pred = ((P3["3:1580"]["comb"] - P3["2:260"]["comb"])
        + ((P3["3:1580"]["mean"] - P3["3:1580"]["comb"])
           - (P3["2:260"]["mean"] - P3["2:260"]["comb"])))
gate("g8 the budget-drift match: predicted and certified declines "
     f"both negative, within 0.15 decades (pred {pred:+.3f}, cert "
     f"{CERT_DECLINE:+.3f})",
     pred < 0 and CERT_DECLINE < 0 and abs(pred - CERT_DECLINE) <= 0.15)

# ---------------------------------------------------------------- g9
band = P2["drift"]["2:260"]["m_comb"]
full = P3["2:260"]["comb"]
gate("g9 the supersession demonstrated: the band comb sits >= 0.3 "
     "decades below the full comb at (2, 260)",
     math.log10(max(band, 1e-300)) <= full - 0.3)

# --------------------------------------------------------------- g10
ok = True
for t0k, ens in CX["points"].items():
    c = ens["zeta_uncond"]["counts"]
    ok &= c["sd"] <= 0.8
    ok &= ens["zeta_uncond"]["frac_floor"] == 0.0
    ok &= 0.05 <= ens["true"]["pct_vs_zeta_cond"] <= 0.95
gate("g10 the crossing-null record: count channel closed (sd <= "
     "0.8, floor fraction 0) and the zeros' twin percentiles in "
     "(0.05, 0.95) at every window", ok)

# --------------------------------------------------------------- g11
from cascade_tower import chain_ok
gate("g11 the chain obligation to cascade_height_uniformity.py "
     "(Theorem 1bh) met", chain_ok("cascade_height_uniformity.py"))

# --------------------------------------------------------------- g12
import re
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d, _n in _miss:
    print(f"  g12 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g12 the 1bi paper needles and the footer census "
     "(backticked >= 2; the anchored count and range needles) "
     "(declared surface)", ok)

print(("\nALL GATES PASS (13/13)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
