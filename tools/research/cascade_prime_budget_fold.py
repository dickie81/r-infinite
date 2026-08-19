#!/usr/bin/env python3
"""Theorem 1be verifier: the fold -- the 1bc stiffness excess derived
from the prime budget, parameter-free, with the non-Gaussian
remainder measured.

The chain: (1) the zeros' displacement structure function D(l)
saturates because the primes' budget is finite -- the explicit
formula's diagonal gives a fixed-shift saturation bracket of
ln ln(T/2pi) + Mertens + 1 (Mertens' theorem for the resolved
primes + the GUE short-time resummation tail; measured 2.630/pi^2
vs 2.615/pi^2 at the window center T0 = 320) -- while count-matched
CUE's D(l) keeps climbing as the RMT log law Sigma^2(l) =
(1/pi^2)(ln 2 pi l + gamma + 1) (measured = the form to < 0.01).
(2) The index/fixed statistic conversion is the exact sawtooth
constant 1/6 (S falls linearly by one between zeros: two endpoints
x uniform variance 1/12; CUE check 0.667 - 1/6 = 0.500 vs measured
0.499). (3) Gaussian surrogate ensembles carrying ONLY these two
parameter-free profiles, count-conditioned per the certified 1bc
protocol and pushed through the same prolate sections at the same
ten points, reproduce the certified stiffness excess:
seed ladders +0.841 +- 0.094 and +0.922 +- 0.097 vs the certified
+0.710 +- 0.086 -- every point positive -- with the surrogate
overshoot (+0.13/+0.21) measuring the NON-GAUSSIAN REMAINDER: real
zeta pays a small premium over its Gaussian twin (~20% of the
excess), the open higher-order piece.

Substrates (committed research instruments, audited not counted):
fold_D.py (profiles + empirics), fold_harden.py (the decomposition),
fold_surrogate.py (the transfer). Compute is content-addressed via
ckpt_key KEYED ON THIS VERIFIER's dependency set: every stage's
params carry the sha256 of each substrate, so any substrate edit
self-invalidates the checkpoints while gate-pin edits here do not.
CASCADE_COMPUTE=fresh forces recomputation (~15-20 min); cached
runs take seconds.

Gates:
  g0  all pins set
  g1  the zeros: 380 at dps 13; gamma_1 = 14.1347 +- 1e-3;
      gamma_380 pinned; 102 below 240 (the 1bc/1bd census)
  g2  the sawtooth: CUE (fixed - index) over lags {8,16,24,32}
      within 1/6 +- 0.025
  g3  CUE fixed-shift D = Sigma^2: |diff| < 0.035 at lags {8,16,24}
  g4  the prime budget: zeta fixed plateau (16..48) x pi^2 in
      (2.45, 2.80) and within 0.20 of ln ln X0 + Mertens + 1
  g5  the saturation dichotomy: zeta index D(48) - D(16) inside
      (-0.08, 0.08) (saturated) while CUE climbs by > 0.05;
      zeta index plateau in (0.09, 0.15)
  g6  the analytic ratio at lags 16..32, index statistics (both
      sides post-1/6, the fold's actual inputs): profile 0.200 in
      (0.15, 0.25); empirical 0.231 in (0.17, 0.30)
  g7  THE FOLD, ladder 9000: mean = pinned +0.922 +- 0.02, all ten
      points positive (> +0.25)
  g8  THE FOLD, ladder 7000: mean = pinned +0.841 +- 0.02, all ten
      points positive (> +0.25)
  g9  the remainder: both ladder means minus the certified 0.710
      in (0.02, 0.35) -- the non-Gaussian premium positive and
      bounded; both means in (0.70, 1.05)
  g10 the 1bc consistency: the certified headline needle
      "+0.710 ± 0.086" present in the paper
  g11 the chain obligation to cascade_sonin_dirac.py (Theorem 1bd)
  g12 the footer census (this script backticked >= 2; the anchored
      count and range needles) and the 1be paper needles

Sabotage suite (run live at the landing battery; edit-run-observe-
restore):
  (a) substrate mangle -- fold_surrogate.py's zeta profile min ->
      max (kills the saturation) -> dependency-sha keys change,
      RECOMPUTING printed, g7/g8 FAIL (the excess collapses), exit 1
  (b) pin mangle -- g7 mean pin 0.922 -> 0.822 -> REUSED, g7 FAIL
      alone, exit 1
  (c) census revert -- footer 81 -> 80 -> g11 FAIL (manifest census)
      AND g12 FAIL, exit 1 (two-gate detection)
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from fold_D import zeros380, D_cue_analytic
from fold_harden import decomposition
from fold_surrogate import run_fold

PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

MERTENS = 0.2614972128476428
SIXTH = 1.0/6.0
X0 = 320.0/(2*math.pi)
CERT_1BC = 0.710

def _sha(name):
    return hashlib.sha256(open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS = {f: _sha(f) for f in ("fold_D.py", "fold_harden.py", "fold_surrogate.py")}

# ---- pins (from the research record, session runs at 4b13418) -------
PIN_MEAN = {9000: 0.922, 7000: 0.841}
PIN_G380 = 653.650

# ---- staged compute (content-addressed on the substrate shas) -------
st = ckpt_key.load("fold_decomp", __file__, {"deps": DEPS})
if st is None:
    st = decomposition(verbose=False)
    ckpt_key.save("fold_decomp", __file__, {"deps": DEPS}, st)
D = st

folds = {}
for base in (9000, 7000):
    key = {"deps": DEPS, "seed_base": base, "nacc": 16}
    r = ckpt_key.load(f"fold_ladder_{base}", __file__, key)
    if r is None:
        pts, mean, sem, scale, prof = run_fold(seed_base=base, verbose=False)
        r = {"points": pts, "mean": mean, "sem": sem, "scale": scale,
             "prof": prof}
        ckpt_key.save(f"fold_ladder_{base}", __file__, key, r)
    folds[base] = r
    print(f"  [ladder {base}] mean {r['mean']:+.3f} +- {r['sem']:.3f}; "
          f"min point {min(r['points'].values()):+.3f}", flush=True)

# ---------------------------------------------------------------- g0
gate("g0 all pins set", all(v is not None for v in
     list(PIN_MEAN.values()) + [PIN_G380]))

# ---------------------------------------------------------------- g1
Z = zeros380()
ok = len(Z) == 380 and abs(Z[0] - 14.134725) < 1e-3
ok &= abs(Z[-1] - PIN_G380) < 0.1
ok &= int(np.sum(Z <= 240)) == 102
gate("g1 the zeros: 380 at dps 13, gamma_1 and gamma_380 pinned, "
     "102 below 240", ok)

# ---------------------------------------------------------------- g2
lags = D["lags"]
idx = [lags.index(a) for a in (8, 16, 24, 32)]
saw = np.mean([D["cue_fixed"][i] - D["cue_index_at_lags"][i] for i in idx])
print(f"  g2 sawtooth measured {saw:.4f} vs 1/6 = {SIXTH:.4f}", flush=True)
gate("g2 the sawtooth: CUE fixed - index = 1/6 +- 0.025", abs(saw - SIXTH) < 0.025)

# ---------------------------------------------------------------- g3
ok = all(abs(D["cue_fixed"][lags.index(a)] - D["sigma2"][lags.index(a)]) < 0.035
         for a in (8, 16, 24))
gate("g3 CUE fixed-shift D = Sigma^2 form (< 0.035 at lags 8/16/24)", ok)

# ---------------------------------------------------------------- g4
plateau = np.mean([D["zeta_fixed"][lags.index(a)] for a in (16, 24, 32, 48)])
bracket = plateau*math.pi**2
target = math.log(math.log(X0)) + MERTENS + 1
print(f"  g4 zeta fixed plateau bracket {bracket:.3f} vs "
      f"lnlnX0+M+1 = {target:.3f}", flush=True)
gate("g4 the prime budget: the fixed plateau bracket in (2.45, 2.80) "
     "and within 0.20 of ln ln X0 + Mertens + 1",
     2.45 < bracket < 2.80 and abs(bracket - target) < 0.20)

# ---------------------------------------------------------------- g5
zi = {a: D["zeta_index_at_lags"][lags.index(a)] for a in (16, 48)}
ci = {a: D["cue_index_at_lags"][lags.index(a)] for a in (16, 48)}
zpl = np.mean([D["zeta_index_at_lags"][lags.index(a)] for a in (16, 24, 32)])
ok = abs(zi[48] - zi[16]) < 0.08 and (ci[48] - ci[16]) > 0.05
ok &= 0.09 < zpl < 0.15
gate("g5 the saturation dichotomy: zeta index D flat 16->48 while CUE "
     "climbs; zeta plateau in (0.09, 0.15)", ok)

# ---------------------------------------------------------------- g6
l32 = np.arange(16, 33).astype(float)
Vsat = (math.log(math.log(X0)) + MERTENS + 1)/math.pi**2
prof_ratio = float(np.mean(np.minimum(D_cue_analytic(l32), Vsat) - SIXTH)
                   / np.mean(D_cue_analytic(l32) - SIXTH))
emp_ratio = zpl/np.mean([D["cue_index_at_lags"][lags.index(a)]
                         for a in (16, 24, 32)])
print(f"  g6 ratio zeta/CUE 16..32: profile {prof_ratio:.3f}; "
      f"empirical {emp_ratio:.3f}", flush=True)
gate("g6 the analytic ratio (index statistics, post-1/6): profile in "
     "(0.15, 0.25), empirical in (0.17, 0.30)",
     0.15 < prof_ratio < 0.25 and 0.17 < emp_ratio < 0.30)

# ------------------------------------------------------------- g7/g8
for gname, base in (("g7", 9000), ("g8", 7000)):
    r = folds[base]
    ok = abs(r["mean"] - PIN_MEAN[base]) < 0.02
    ok &= all(v > 0.25 for v in r["points"].values())
    gate(f"{gname} THE FOLD, ladder {base}: mean pinned "
         f"{PIN_MEAN[base]:+.3f} +- 0.02, all ten points > +0.25", ok)

# ---------------------------------------------------------------- g9
ok = all(0.02 < folds[b]["mean"] - CERT_1BC < 0.35 and
         0.70 < folds[b]["mean"] < 1.05 for b in (9000, 7000))
gate("g9 the remainder: both ladders' overshoot of the certified "
     "+0.710 in (0.02, 0.35) -- the non-Gaussian premium positive "
     "and bounded", ok)

# ---------------------------------------------------------------- g10
gate("g10 the 1bc consistency: the certified headline needle in the "
     "paper", "+0.710 ± 0.086" in paper)

# ---------------------------------------------------------------- g11
from cascade_tower import chain_ok
gate("g11 the chain obligation to cascade_sonin_dirac.py (Theorem 1bd) "
     "met", chain_ok("cascade_sonin_dirac.py"))

# ---------------------------------------------------------------- g12
import re
normp = re.sub(r"\s+", " ", paper)
plain = normp.replace("**", "")
needles = [
    "Theorem 1be (the fold",
    "the primes' budget",
    "the sawtooth constant 1/6",
    "ln ln(T/2π) + Mertens + 1",
    "the non-Gaussian remainder",
    "every point positive",
    "count-conditioned per the certified 1bc protocol",
]
ok = all(nd in plain for nd in needles)
for nd in needles:
    if nd not in plain:
        print(f"  g12 MISSING: {nd!r}", flush=True)
ok &= paper.count("`cascade_prime_budget_fold.py`") >= 2
ok &= "the **81 scripts cited in place** above" in normp
ok &= "extended by Theorems 1i–1be:" in normp
gate("g12 the 1be paper needles and the footer census (backticked >= 2; "
     "the anchored count and range needles)", ok)

print(("\nALL GATES PASS (13/13)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
