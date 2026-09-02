#!/usr/bin/env python3
"""Theorem 1bf verifier: the two-sided witness -- section-level Weil
positivity measured from arithmetic alone, the truncation-tail
structure of the dodging margin, and the concentrated-vector
identity that confines the core-local in-band zeros to within
millionths of the critical line (round-229 F1: the confinement is
core-local, not band-wide -- see g9).

The chain: (1) the WEIL-SIDE form (digamma ARCH + pole pair + von
Mangoldt primes -- certified 1bb machinery on the certified 1bc
sections; NO zero-location input) has minimum eigenvalue m_W >= 0
at every measured point, hair-thin above zero at depth (+4.50e-7 /
+1.20e-7), with the PRIME term cancelling ARCH on the null
direction to seven decades: section-level Weil positivity with
unconditional inputs, the arithmetic doing the cancellation.
(2) The truncation-tail discovery: the certified zero-side dodging
margin is NOT the Weil margin at depth -- the dodging minimizer
exports O(1) Parseval mass beyond the measured zero window
(<w_Z, Q_W w_Z> = 3.12 at (60,200), gated), so the deep minima's
2-5% agreement is a section-floor effect; witness_offline's
sqrt-amplifier law (d* ~ sqrt(margin), slope ~0.5) is an
INSTRUMENT-sensitivity law for the dodging form (scope corrected
mid-arc from the landing draft's Weil-violation framing).
(3) The two-sided witness proper, on concentrated vectors (top
prolates, Slepian leakage ~1e-13, grid-limited): T = <w, Q_W w> -
z_380(w) measures arithmetic-vs-ordinates agreement at |T| <=
3.5e-12 measured (gated < 1e-11), against a jitter-CALIBRATED
ordinate-error budget (the zero side's response to Gaussian
ordinate jitter is linear -- the 1e-9/2e-11 rms ratio is 50.0x,
gated; dps-13 worst case 5.75-8.98e-12); the off-line COLLISION
injection (two adjacent donors collide to the off-line pair at
their mean -- the correct off-line topology; the response is even
in d by construction and O(d^2), measured coefficients resp2 ~
0.02-0.09 per (dA)^2) then confines a CORE-LOCAL collision pair
(round-229 F1, radius per round-230 F4: the response coefficient
collapses off-center -- at (120,300), max resp2 over the top-8
prolates in u = A(gamma - tau0): 2.5e-2 at u +1.5 (round-231 F1:
the 4.5e-2 previously printed here belongs to the next pair, at
u +4.3 -- a target-rounding misattribution), 6.6e-3 at
u +40, 0 at u +83 where the bound is vacuous; the ppm radius is
|gamma - tau0| <~ 20, the support edge ~41.5)
to d <= sqrt((|T| + budget)/resp2)/A = 5.5e-6 .. 9.2e-6 at the
four gated points, with the injected alarm at d = 2e-3 ringing
5+ orders above the floor.

Honest scope is carried by the paper block: window-bounded (heights
<= 653, four section points), ordinate-input caveats, no RH
leverage claimed.

Substrates (committed, audited not counted): witness_offline.py
(complex-ordinate evaluation, the sqrt-law), witness_twosided.py
(the Weil side, the concentrated witness, the collision probe, and
landing_stage -- the staged compute itself, relocated from this
verifier at round-229 F7 so the producing code is keyed), plus the
fold substrates they import. The stage is content-addressed via
ckpt_key keyed on fold_surrogate.py bytes with the 1bf substrate
sha set in params (DEPS_1BF: fold_D.py, fold_surrogate.py,
witness_offline.py, witness_twosided.py -- round-229 c2 renames
the set for what it is): substrate edits self-invalidate, verifier
pin edits reuse.

Gates:
  g0  pins set
  g1  consistency: the complex-ordinate path reproduces the
      certified real-path margins (rel < 1e-6 at (60,200))
  g2  WEIL POSITIVITY: m_W >= 0 at all four points, pinned
      (+4.501e-7, +1.196e-7, +9.496e-3, +3.921e-4, rel 3e-2)
  g3  the null-direction cancellation: PRIME/ARCH = -1 within 3e-7
      at the two deep points (the arithmetic eats the archimedean)
  g4  the section-floor proximity: 0 < (m_W - m_Z)/m_Z < 0.10 at
      all four points (observation, not the identity)
  g5  the truncation tail: <w_Z, Q_W w_Z> in (2.5, 4.0) at
      (60,200) -- the dodging minimizer's exported mass, O(1)
  g6  the concentrated identity: max |T| < 1e-11 over the top-8
      prolates at every point; Slepian leakage < 1e-12
  g7  the jitter calibration: the best-bound prolate's budget per
      point in (1e-12, 5e-11) (round-230 F5: the stage computes
      all 32 budgets but stores and gates the four best -- "every
      budget" was documented-not-gated) and the response linear --
      the 1e-9/2e-11 rms ratio gated in (49, 51), measured 50.0x
      (round-229 F4: previously documented-not-coded with a stale
      "30-300x" digit)
  g8  the collision probe: resp2 pinned per point (rel 0.3);
      evenness printed, not gated -- T(+d) = T(-d) is bit-exact by
      construction for real test vectors, so an evenness conjunct
      cannot fail (round-229 F3)
  g9  the d_bounds: pinned (5.51e-6, 8.15e-6, 7.32e-6, 9.24e-6,
      rel 0.25) -- a core-local collision pair within ~1e-5 of
      the critical line (round-229 F1: not band-wide)
  g10 the injected alarm: |collision T-shift| at d = 2e-3 exceeds
      1e-7 at every point (5+ orders above the identity floor)
  g11 the sqrt-law: d* recomputed at the four points, log-log
      slope vs the base dodging margin in (0.30, 0.60)
  g12 the chain obligation to cascade_prime_budget_fold.py
      (Theorem 1be) met
  g13 the footer census (this script backticked >= 2; the anchored
      count and range needles) and the 1bf paper needles

Sabotage suite (live at the landing battery; edit-run-observe-
restore):
  (a) substrate mangle -- witness_twosided.py's prime_mat sign
      flip -> OBSERVED: key changed, RECOMPUTING, m_W COLLAPSES to
      -0.542 at (60,200) (the flipped prime cannot cancel ARCH; the
      identity floor explodes to Tmax = 1.16), g2+g3+g4+g6+g8+g9
      FAIL, exit 1 -- richer detection than designed
  (b) pin mangle -- g2 m_W pin 4.501e-7 -> 5.501e-7 -> OBSERVED:
      REUSED (cached, seconds), g2 FAIL alone, exit 1
  (c) census revert -- footer 82 -> 81 -> OBSERVED: g12 FAIL (the
      chain gate prints the missing census string) AND g13 FAIL,
      exit 1 (two-gate detection)
"""
import hashlib, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from witness_twosided import landing_stage


# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g13', 's': 'Theorem 1bf (the two-sided witness', 'form': 'plain'},
    {'g': 'g13', 's': 'section-level Weil positivity', 'form': 'plain'},
    {'g': 'g13', 's': 'the prime term cancels the archimedean', 'form': 'plain'},
    {'g': 'g13', 's': 'the truncation-tail discovery', 'form': 'plain'},
    {'g': 'g13', 's': 'The collision injection', 'form': 'plain'},
    {'g': 'g13', 's': 'millionths of the critical line', 'form': 'plain'},
    {'g': 'g13', 's': 'no RH leverage claimed', 'form': 'plain'},
    {'g': 'g13', 's': 'core-local and collapses off-center', 'form': 'plain'},
    {'g': 'g13', 's': 'outside the probed collision topology', 'form': 'plain'},
    {'s': '`cascade_twosided_witness.py`', 'min': 2, 'g': 'g13'},
    {'s': 'the **88 scripts cited in place** above', 'form': 'ws', 'g': 'g13'},
    {'s': 'extended by Theorems 1i–1bl:', 'form': 'ws', 'g': 'g13'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

def _sha(name):
    return hashlib.sha256(open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS_1BF = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                                 "witness_offline.py",
                                 "witness_twosided.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

PTS = [(60.0, 200.0), (120.0, 260.0), (60.0, 280.0), (120.0, 300.0)]
PIN_MW = [4.501e-7, 1.196e-7, 9.496e-3, 3.921e-4]
PIN_DB = [5.51e-6, 8.15e-6, 7.32e-6, 9.24e-6]
PIN_DSTAR = [6.151e-4, 1.312e-3, 1.017e-1, 3.747e-2]   # dstar_tol 1e-6; the landing draft's 1e-3 was effectively absolute at the deep points; cross-validates witness_offline's committed table to 0.15%

# ---- staged compute (the stage body lives in witness_twosided.py's
# landing_stage so the producing code is keyed, round-229 F7; the
# point list keyed too, round-230 F3 -- a PTS edit must invalidate,
# not silently reuse) ------------------------------------------------
STAGE_PARAMS = {"deps": DEPS_1BF, "dstar_tol": 1e-6, "pts": PTS}
st = ckpt_key.load("witness_main", KEYFILE, STAGE_PARAMS)
if st is None:
    st = landing_stage(dstar_tol=STAGE_PARAMS["dstar_tol"],
                       pts=tuple(tuple(p) for p in PTS))
    ckpt_key.save("witness_main", KEYFILE, STAGE_PARAMS, st)

P = st["pts"]
for p in P:
    print(f"  ({p['c']:.0f},{p['t0']:.0f}): mW {p['mW']:+.3e} "
          f"(A {p['arch']:+.3f}/P {p['prime']:+.3f}) mZ {p['mZ']:.3e} "
          f"tail {p['tail']:.3f} Tmax {p['Tmax']:.2e} "
          f"db {p['best']['db']:.3e} lin {p['best']['lin_ratio']:.2f}x "
          f"d* {p['dstar']:.3e}", flush=True)

# ---------------------------------------------------------------- g0
gate("g0 pins set", PIN_DSTAR is not None and all(
     v is not None for v in PIN_MW + PIN_DB + PIN_DSTAR))

# ---------------------------------------------------------------- g1
gate("g1 consistency: complex path = certified real path (rel < 1e-6)",
     st["consist_rel"] < 1e-6)

# ---------------------------------------------------------------- g2
ok = all(p["mW"] >= 0 for p in P)
ok &= all(abs(p["mW"]/pin - 1) < 3e-2 for p, pin in zip(P, PIN_MW))
gate("g2 WEIL POSITIVITY: m_W >= 0 at all four points, pinned "
     "(arithmetic inputs only)", ok)

# ---------------------------------------------------------------- g3
ok = all(abs(p["prime"]/p["arch"] + 1) < 3e-7 for p in P[:2])
gate("g3 the null-direction cancellation: PRIME/ARCH = -1 within 3e-7 "
     "at the deep points", ok)

# ---------------------------------------------------------------- g4
ok = all(0 < (p["mW"] - p["mZ"])/p["mZ"] < 0.10 for p in P)
gate("g4 the section-floor proximity: 0 < (m_W - m_Z)/m_Z < 0.10", ok)

# ---------------------------------------------------------------- g5
gate("g5 the truncation tail: the dodging minimizer's exported mass "
     "in (2.5, 4.0) at (60,200)", 2.5 < P[0]["tail"] < 4.0)

# ---------------------------------------------------------------- g6
ok = all(p["Tmax"] < 1e-11 and p["leak_max"] < 1e-12 for p in P)
gate("g6 the concentrated identity: max|T| < 1e-11, leakage < 1e-12 "
     "at every point", ok)

# ---------------------------------------------------------------- g7
ok = all(1e-12 < p["best"]["bud"] < 5e-11 for p in P)
ok &= all(49.0 < p["best"]["lin_ratio"] < 51.0 for p in P)
gate("g7 the best-bound jitter budgets (one per point) in "
     "(1e-12, 5e-11); linear response (the 1e-9/2e-11 rms ratio "
     "in (49, 51) -- round-229 F4; round-230 F5)", ok)

# ---------------------------------------------------------------- g8
for p in P:
    print(f"  g8 even_rel ({p['c']:.0f},{p['t0']:.0f}): "
          f"{p['best']['even_rel']:.1e} (by construction; printed, "
          "not gated -- round-229 F3)", flush=True)
RESP_PIN = [9.428e-2, 3.819e-2, 4.413e-2, 2.398e-2]
ok = all(abs(p["best"]["resp2"]/r - 1) < 0.3
         for p, r in zip(P, RESP_PIN))
gate("g8 the collision probe: resp2 pinned per point (evenness "
     "printed, not gated -- bit-exact by construction)", ok)

# ---------------------------------------------------------------- g9
ok = all(abs(p["best"]["db"]/pin - 1) < 0.25 for p, pin in zip(P, PIN_DB))
gate("g9 the d_bounds pinned: a core-local collision pair within "
     "~1e-5 of the critical line (round-229 F1: core-local, "
     "not band-wide)", ok)

# --------------------------------------------------------------- g10
ok = all(p["best"]["alarm"] > 1e-7 for p in P)
gate("g10 the injected alarm at d = 2e-3 exceeds 1e-7 at every point "
     "(5+ orders above the identity floor; the response is "
     "resp2 (dA)^2 ~ 1e-6 -- the landing draft's 1e-4 threshold was "
     "calibrated to the superseded single-donor probe's doubling "
     "artifact)", ok)

# --------------------------------------------------------------- g11
lm = np.log([p["mZ"] for p in P])
ld = np.log([p["dstar"] for p in P])
b = float(np.polyfit(lm, ld, 1)[0])
ok = 0.30 < b < 0.60
ok &= PIN_DSTAR is not None and all(
    abs(p["dstar"]/pin - 1) < 0.10 for p, pin in zip(P, PIN_DSTAR))
print(f"  g11 sqrt-law slope {b:.3f}", flush=True)
gate("g11 the sqrt-law: d* pins and log-log slope in (0.30, 0.60) "
     "(the dodging-instrument sensitivity law)", ok)

# --------------------------------------------------------------- g12
from cascade_tower import chain_ok
gate("g12 the chain obligation to cascade_prime_budget_fold.py "
     "(Theorem 1be) met", chain_ok("cascade_prime_budget_fold.py"))

# --------------------------------------------------------------- g13
import re
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d, _n in _miss:
    print(f"  g13 MISSING (count {_n}): {_d['s']!r}", flush=True)
gate("g13 the 1bf paper needles and the footer census "
     "(backticked >= 2; the anchored count and range needles) "
     "(declared surface)", ok)

print(("\nALL GATES PASS (14/14)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
