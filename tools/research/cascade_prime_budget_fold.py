#!/usr/bin/env python3
"""Theorem 1be verifier: the fold -- the 1bc stiffness excess derived
from the prime budget, parameter-free, with the non-Gaussian
remainder measured.

The chain: (1) the zeros' displacement structure function D(l)
saturates because the primes' budget is finite -- the explicit
formula's diagonal gives a fixed-shift saturation bracket of
ln ln(T/2pi) + Mertens + 1 (Mertens' theorem for the resolved
primes + the GUE short-time resummation tail; measured 2.630/pi^2
vs the formula 2.6302/pi^2 at the window center T0 = 320, agreement 0.0006 -- round-224 F4 corrected the stale 2.615) -- while count-matched
CUE's D(l) keeps climbing as the RMT log law Sigma^2(l) =
(1/pi^2)(ln 2 pi l + gamma + 1) (mean signed difference 0.004; per-lag within 0.023 -- round-224 F3 corrected the landing's "< 0.01 per lag").
(2) The index/fixed statistic conversion is the exact sawtooth
constant 1/6 (S falls linearly by one between zeros: two endpoints
x uniform variance 1/12; CUE check 0.667 - 1/6 = 0.500 vs measured
0.499). (3) Gaussian surrogate ensembles carrying ONLY these two
parameter-free profiles (round-224 F1: the landing carried
empirical floors 0.12/0.18 that silently overrode the derived
bracket -- min(Sigma^2, Vsat) - 1/6 = 0.0998 < 0.12 at every lag,
so the landing's transfer ran on the floor; floors removed, and the
zeta profile is now exactly the derived constant 0.0998), count-
conditioned per the certified 1bc protocol and pushed through the
same prolate sections at certified 1bc's own ten points (round-224
F2: the landing's grid differed at four of ten), reproduce the
certified stiffness excess: seed ladders +0.952 +- 0.127 and
+0.919 +- 0.111 vs the certified +0.710 +- 0.086 -- every point
positive, mins +0.354/+0.369 -- with the surrogate overshoot
(+0.24/+0.21). Round 227 INVERTED the overshoot's attribution: the
shared-field twin test (g13) puts the real zeros' correlated
ten-point excess INSIDE the Gaussian-twin distribution (real +0.908
vs draws +0.976 +- 0.087, z = -0.79, percentile 15.6) -- zeta is
CONSISTENT with its second-order Gaussian twin at this sample --
while the CUE twin test (g14) locates the overshoot's carrier on
the comparator side: real determinantal CUE dodges +0.272 +- 0.073
worse than ITS Gaussian D-matched twin (10/10 points positive;
the calibration-aligned value -- the landing's +0.243/9-of-10 ran
the F3-miscalibrated twin). The confound account (round-227 F2,
corrected): the twins' band-lag D mismatch is SYSTEMATIC (-0.05 to
-0.07 one-signed at lags 24-120) and the anchoring/registration
conventions each shift ~0.11 decades, cancelling; the committed
fully-matched control (g15) removes all of it and the premium
survives at +0.227 +- 0.085 (8/10). The decomposition arithmetic:
zeta-twin gap (-0.068) minus CUE-twin gap (+0.272) = -0.34 vs the
observed -0.24, within ~1.3 sem. The round-224 reviewer's independent
no-floor 1bc-grid run gave +0.952 +- 0.127 (seed 9000), matched
exactly by the re-pin.

Substrates (committed research instruments, audited not counted):
fold_D.py (profiles + empirics), fold_harden.py (the decomposition),
fold_surrogate.py (the transfer). Compute is content-addressed via
ckpt_key keyed on fold_surrogate.py's bytes PLUS every substrate's
sha256 in the params, so any substrate edit self-invalidates the
checkpoints while gate-pin edits to THIS file do not (the landing's
first keying used this verifier's own bytes, which discarded compute
on every pin edit -- caught by the suite's probe (b) and fixed
before the record).
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
  g7  THE FOLD, ladder 9000: mean = pinned +0.952 +- 0.02, all ten
      points positive (> +0.25)
  g8  THE FOLD, ladder 7000: mean = pinned +0.919 +- 0.02, all ten
      points positive (> +0.25)
  g9  the remainder: both ladder means minus the certified 0.710
      in (0.05, 0.40); both means in (0.75, 1.10) -- the overshoot
      positive and bounded, its carrier adjudicated at g13-g15
      (round 227: the comparator's determinantal premium, not zeta)
  g10 the 1bc consistency: the certified headline needle
      "+0.710 ± 0.086" present in the paper
  g11 the chain obligation to cascade_sonin_dirac.py (Theorem 1bd)
  g12 the footer census (this script backticked >= 2; the anchored
      count and range needles) and the 1be paper needles
  g13 the zeta twin test (round 227): the real zeros' correlated
      ten-point excess inside the shared-field Gaussian-twin
      distribution (pin +0.908 +- 0.02; z in (-1.4, -0.2);
      percentile 5-40%)
  g14 the CUE twin gap (round 227): real determinantal CUE vs its
      Gaussian twin, mean pinned +- 0.03, >= 8/10 positive
      (substrates fold_remainder.py / fold_remainder2.py, keyed
      via DEPS2; the round-227 sweep aligned the twin's calibration
      stream with 1be's -- F3 -- so the pin was re-collected)
  g15 the fully-matched control (round-227 F2, the reviewer's B''
      ported to the committed substrate): the premium survives full
      convention- and measured-D matching, pin +- 0.03, >= 7/10
      positive

Sabotage suite (run live at the landing battery; edit-run-observe-
restore):
  (a) substrate mangle -- fold_surrogate.py's zeta profile min ->
      max (kills the saturation) -> OBSERVED: keys changed,
      RECOMPUTING x3 (decomp + both ladders), the excess COLLAPSES
      to +0.019/+0.061 (without the saturation the two profiles
      coincide -- the probe doubles as the physics control), g7+g8+g9
      FAIL, exit 1
  (b) pin mangle -- g7 mean pin 0.922 -> 0.822 -> first run OBSERVED
      RECOMPUTING x3 where the docstring promised REUSED: the
      landing's keying used this verifier's own bytes, a real
      contract defect caught by this probe and fixed (re-keyed to
      substrate bytes; the gate detection held throughout: g7 FAIL
      alone, exit 1). Redo under the fixed keying OBSERVED: REUSED
      x4, seconds, g7 FAIL alone, exit 1
  (c) census revert -- footer 81 -> 80 -> OBSERVED: g11 FAIL (the
      chain gate prints the missing census string) AND g12 FAIL,
      exit 1 (two-gate detection)
  (d) round-227 reviewer's live probes on the twin gates: g13 pin
      0.908 -> 0.808 -> OBSERVED REUSED x6, g13 FAIL alone, exit 1;
      g14 pin -> mangled -> OBSERVED REUSED x6, g14 FAIL alone,
      exit 1 (the fixed keying contract held: pin edits reuse)
  (e) g15 pin mangle 0.227 -> 0.127 (the round-227 sweep battery)
      -- OBSERVED: REUSED x7 (all stages cached, seconds), g15 FAIL
      alone, exit 1; restored, 16/16
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from fold_D import zeros380, D_cue_analytic
from fold_harden import decomposition
from fold_surrogate import run_fold


# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
import paper_needles
PAPER_NEEDLES = [
    {'g': 'g12', 's': 'Theorem 1be (the fold', 'form': 'plain'},
    {'g': 'g12', 's': "the primes' budget", 'form': 'plain'},
    {'g': 'g12', 's': 'the sawtooth constant 1/6', 'form': 'plain'},
    {'g': 'g12', 's': 'ln ln(T/2π) + Mertens + 1', 'form': 'plain'},
    {'g': 'g12', 's': 'the non-Gaussian remainder', 'form': 'plain'},
    {'g': 'g12', 's': 'every point positive', 'form': 'plain'},
    {'g': 'g12', 's': 'count-conditioned per the certified 1bc protocol', 'form': 'plain'},
    {'s': '`cascade_prime_budget_fold.py`', 'min': 2, 'g': 'g12'},
    {'s': 'the **88 scripts cited in place** above', 'form': 'ws', 'g': 'g12'},
    {'s': 'extended by Theorems 1i–1bl:', 'form': 'ws', 'g': 'g12'},
    {'g': 'g10', 's': '+0.710 ± 0.086'},
]

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
DEPS2 = {f: _sha(f) for f in ("fold_D.py", "fold_harden.py",
                              "fold_surrogate.py", "fold_remainder.py",
                              "fold_remainder2.py")}

# ---- pins (from the research record, session runs at 4b13418) -------
PIN_MEAN = {9000: 0.952, 7000: 0.919}
PIN_G15 = 0.227   # the fully-matched premium (sweep battery fresh run)
PIN_G380 = 653.650

# ---- staged compute (content-addressed on the substrate shas) -------
KEYFILE = os.path.join(HERE, "fold_surrogate.py")
st = ckpt_key.load("fold_decomp", KEYFILE, {"deps": DEPS})
if st is None:
    st = decomposition(verbose=False)
    ckpt_key.save("fold_decomp", KEYFILE, {"deps": DEPS}, st)
D = st

folds = {}
for base in (9000, 7000):
    key = {"deps": DEPS, "seed_base": base, "nacc": 16}
    r = ckpt_key.load(f"fold_ladder_{base}", KEYFILE, key)
    if r is None:
        pts, mean, sem, scale, prof = run_fold(seed_base=base, verbose=False)
        r = {"points": pts, "mean": mean, "sem": sem, "scale": scale,
             "prof": prof}
        ckpt_key.save(f"fold_ladder_{base}", KEYFILE, key, r)
    folds[base] = r
    print(f"  [ladder {base}] mean {r['mean']:+.3f} +- {r['sem']:.3f}; "
          f"min point {min(r['points'].values()):+.3f}", flush=True)

# ---------------------------------------------------------------- g0
gate("g0 all pins set", all(v is not None for v in
     list(PIN_MEAN.values()) + [PIN_G380, PIN_G15]))

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
ok = all(0.05 < folds[b]["mean"] - CERT_1BC < 0.40 and
         0.75 < folds[b]["mean"] < 1.10 for b in (9000, 7000))
gate("g9 the remainder: both ladders' overshoot of the certified "
     "+0.710 in (0.05, 0.40), means in (0.75, 1.10) -- the overshoot "
     "positive and bounded (its carrier adjudicated at g13-g15: the "
     "comparator's determinantal premium, round 227)", ok)

# ------------------------------------------------------------ g13/g14
# (round-227 correction stages: the remainder attribution inverts)
from fold_remainder import significance
from fold_remainder2 import cue_twin_gap
sig = ckpt_key.load("fold_twin_sig", KEYFILE, {"deps": DEPS2, "ndraw": 32})
if sig is None:
    sig = significance(ndraw=32, verbose=False)
    ckpt_key.save("fold_twin_sig", KEYFILE, {"deps": DEPS2, "ndraw": 32}, sig)
gapr = ckpt_key.load("fold_twin_gap", KEYFILE, {"deps": DEPS2})
if gapr is None:
    gapr = cue_twin_gap(verbose=False)
    ckpt_key.save("fold_twin_gap", KEYFILE, {"deps": DEPS2}, gapr)
print(f"  g13 zeta twin: real {sig['real_mean']:+.3f}, z {sig['z']:+.2f}, "
      f"pct {100*sig['percentile']:.1f}", flush=True)
ok = abs(sig["real_mean"] - 0.908) < 0.02
ok &= -1.4 < sig["z"] < -0.2 and 0.05 < sig["percentile"] < 0.40
gate("g13 the zeta twin test: reproducibility pins (real +0.908 "
     "+- 0.02; z in (-1.4, -0.2); percentile 5-40% -- windows around "
     "the observed draw, so a z nearer 0 would STRENGTHEN the "
     "consistency claim while failing the pin); the claim itself is "
     "the interior position: zeta consistent with its second-order "
     "Gaussian twin", ok)
print(f"  g14 CUE twin gap: mean {gapr['mean']:+.3f} +- {gapr['sem']:.3f}, "
      f"{gapr['npos']}/10 positive", flush=True)
ok = abs(gapr["mean"] - 0.272) < 0.03 and gapr["npos"] >= 8
gate("g14 the CUE twin gap: real determinantal CUE dodges worse than "
     "its Gaussian D-matched twin (pin +0.272 +- 0.03, the "
     "calibration-aligned value -- the round-227 landing's +0.243 ran "
     "the F3-miscalibrated twin; >= 8/10 points positive) -- the "
     "certified overshoot's carrier is the comparator side", ok)

from fold_remainder2 import matched_twin_gap
mt = ckpt_key.load("fold_twin_matched", KEYFILE, {"deps": DEPS2})
if mt is None:
    mt = matched_twin_gap(verbose=False)
    ckpt_key.save("fold_twin_matched", KEYFILE, {"deps": DEPS2}, mt)
print(f"  g15 fully-matched premium: {mt['mean']:+.3f} +- {mt['sem']:.3f}, "
      f"{mt['npos']}/10 positive", flush=True)
ok = PIN_G15 is not None and abs(mt["mean"] - PIN_G15) < 0.03 and mt["npos"] >= 7
gate("g15 the fully-matched control (round-227 F2): the determinantal "
     "premium survives anchoring + registration + measured-D + "
     "calibration matching (pin from the committed run +- 0.03; "
     ">= 7/10 points positive) -- not a convention artifact", ok)

# ---------------------------------------------------------------- g10
_ok10, _m10 = paper_needles.verify(PAPER_NEEDLES, g='g10')
gate("g10 the 1bc consistency: the certified headline needle in the "
     "paper (declared surface)", _ok10)

# ---------------------------------------------------------------- g11
from cascade_tower import chain_ok
gate("g11 the chain obligation to cascade_sonin_dirac.py (Theorem 1bd) "
     "met", chain_ok("cascade_sonin_dirac.py"))

# ---------------------------------------------------------------- g12
# round-264 F264-5: g12 evaluates ONLY its own entries -- the g10
# headline needle is g10's gate, not a silent second conjunct here
import re
ok, _miss = paper_needles.verify(PAPER_NEEDLES, g='g12')
for _d, _n in _miss:
    print(f"  g12 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g12 the 1be paper needles and the footer census "
     "(backticked >= 2; the anchored count and range needles) "
     "(declared surface)", ok)

print(("\nALL GATES PASS (16/16)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
