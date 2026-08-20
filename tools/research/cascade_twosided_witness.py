#!/usr/bin/env python3
"""Theorem 1bf verifier: the two-sided witness -- section-level Weil
positivity measured from arithmetic alone, the truncation-tail
structure of the dodging margin, and the concentrated-vector
identity that confines every in-band zero to within millionths of
the critical line.

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
prolates, Slepian leakage ~1e-13): T = <w, Q_W w> - z_380(w)
measures arithmetic-vs-ordinates agreement at |T| <= 3.5e-12,
against a jitter-CALIBRATED ordinate-error budget (the zero side's
response to Gaussian ordinate jitter is linear; dps-13 worst case
~6-9e-12); the off-line COLLISION injection (two adjacent donors
collide to the off-line pair at their mean -- the correct
off-line topology; the response is even in d and O(d^2), measured
coefficients resp2 ~ 0.02-0.09 per (dA)^2) then confines every
in-band collision pair to d <= sqrt((|T| + budget)/resp2)/A =
5.5e-6 .. 9.2e-6 across the four gated points, with the injected
alarm at d = 2e-3 ringing 5+ orders above the floor.

Honest scope is carried by the paper block: window-bounded (heights
<= 653, four section points), ordinate-input caveats, no RH
leverage claimed.

Substrates (committed, audited not counted): witness_offline.py
(complex-ordinate evaluation, the sqrt-law), witness_twosided.py
(the Weil side, the concentrated witness, the collision probe),
plus the fold substrates they import. Stages are content-addressed
via ckpt_key keyed on fold_surrogate.py bytes with the full
substrate sha set in params (DEPS3): substrate edits
self-invalidate, verifier pin edits reuse.

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
  g7  the jitter calibration: every budget in (1e-12, 5e-11) and
      the response linear (scale 1e-9 gives 30-300x the 2e-11 rms)
  g8  the collision probe: T(+d) = T(-d) to rel 1e-6 (evenness) and
      resp2 pinned per point (rel 0.3)
  g9  the d_bounds: pinned (5.51e-6, 8.15e-6, 7.32e-6, 9.24e-6,
      rel 0.25) -- every in-band collision pair within ~1e-5 of
      the critical line
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
      flip -> keys change, RECOMPUTING, g2/g3 FAIL (m_W jumps to
      O(1): no cancellation), exit 1
  (b) pin mangle -- g2 m_W pin at (60,200) -> g2 FAIL alone on
      cached compute, exit 1
  (c) census revert -- footer 82 -> 81 -> g12 FAIL AND g13 FAIL,
      exit 1 (two-gate detection)
"""
import hashlib, math, os, sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import ckpt_key
from fold_D import zeros380
from fold_surrogate import A
from witness_offline import dstar
from witness_twosided import (TwoSided, concentrated_witness,
                              collision_probe, jitter_budget)

PAPER = os.path.join(HERE, "..", "..", "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

def _sha(name):
    return hashlib.sha256(open(os.path.join(HERE, name), "rb").read()).hexdigest()

DEPS3 = {f: _sha(f) for f in ("fold_D.py", "fold_surrogate.py",
                              "witness_offline.py", "witness_twosided.py")}
KEYFILE = os.path.join(HERE, "fold_surrogate.py")

PTS = [(60.0, 200.0), (120.0, 260.0), (60.0, 280.0), (120.0, 300.0)]
PIN_MW = [4.501e-7, 1.196e-7, 9.496e-3, 3.921e-4]
PIN_DB = [5.51e-6, 8.15e-6, 7.32e-6, 9.24e-6]
PIN_DSTAR = [6.151e-4, 1.312e-3, 1.017e-1, 3.747e-2]   # dstar_tol 1e-6; the landing draft's 1e-3 was effectively absolute at the deep points; cross-validates witness_offline's committed table to 0.15%

# ---- staged compute -------------------------------------------------
STAGE_PARAMS = {"deps": DEPS3, "dstar_tol": 1e-6}
st = ckpt_key.load("witness_main", KEYFILE, STAGE_PARAMS)
if st is None:
    Z = zeros380()
    out = {"pts": []}
    sects = {}
    for c, t0 in PTS:
        if c not in sects:
            sects[c] = TwoSided(c)
        S = sects[c]
        mW, wW = S.weil_margin(t0)
        arch = float(np.real(np.conj(wW) @ S.ARCH @ wW))
        prime = float(np.real(np.conj(wW) @ S.PRIME @ wW))
        mZ = S.base_margin(Z, t0)
        # dodging minimizer for the tail measurement
        s = np.concatenate([(Z - t0)*A, (-Z - t0)*A])
        Vb = np.asarray(S.vhat(s.astype(complex)))
        if Vb.shape[0] != len(s):
            Vb = Vb.T
        QZ = Vb.conj().T @ Vb
        QZ = (QZ + QZ.conj().T)/2
        from scipy.linalg import eigh as scipy_eigh
        evz, VZ = scipy_eigh(QZ, S.G)
        wZ = VZ[:, 0]
        tail = float(np.real(np.conj(wZ) @ S.QW @ wZ))
        rows = concentrated_witness(S, Z, t0, ktop=8)
        leak = S.slepian_leakage()
        Tmax = max(abs(r[3]) for r in rows)
        per_k = []
        for k, qw, z, T in rows:
            w = np.eye(S.n)[:, k]/math.sqrt(S.G[k, k])
            bud = jitter_budget(S, Z, t0, w)
            rP = collision_probe(S, Z, t0, w, 1e-3)
            rM = collision_probe(S, Z, t0, w, -1e-3)
            r0 = collision_probe(S, Z, t0, w, 1e-6)
            resp2 = abs(rP - r0)/((1e-3*A)**2)
            alarm = abs(collision_probe(S, Z, t0, w, 2e-3) - r0)
            even_rel = abs(rP - rM)/max(abs(rP), 1e-30)
            db = math.sqrt((abs(T) + bud)/resp2)/A if resp2 > 0 else None
            per_k.append({"k": k, "T": T, "bud": bud, "resp2": resp2,
                          "db": db, "even_rel": even_rel, "alarm": alarm})
        best = min((p for p in per_k if p["db"]), key=lambda p: p["db"])
        # sqrt-law point on the dodging instrument
        ds = dstar(S, Z, t0, t0, tol=1e-6)
        out["pts"].append({
            "c": c, "t0": t0, "mW": mW, "arch": arch, "prime": prime,
            "mZ": mZ, "tail": tail, "Tmax": Tmax,
            "leak_max": float(leak[:8].max()), "best": best,
            "dstar": ds, "consist_rel": None})
    # consistency at (60,200)
    S = sects[60.0]
    m_ref = S.margin(Z, 200.0)
    m_cpx = S.base_margin(Z, 200.0)
    out["consist_rel"] = abs(m_ref - m_cpx)/m_ref
    ckpt_key.save("witness_main", KEYFILE, STAGE_PARAMS, out)
    st = out

P = st["pts"]
for p in P:
    print(f"  ({p['c']:.0f},{p['t0']:.0f}): mW {p['mW']:+.3e} "
          f"(A {p['arch']:+.3f}/P {p['prime']:+.3f}) mZ {p['mZ']:.3e} "
          f"tail {p['tail']:.3f} Tmax {p['Tmax']:.2e} "
          f"db {p['best']['db']:.3e} d* {p['dstar']:.3e}", flush=True)

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
gate("g7 the jitter budgets in (1e-12, 5e-11)", ok)

# ---------------------------------------------------------------- g8
ok = all(p["best"]["even_rel"] < 1e-6 for p in P)
RESP_PIN = [9.428e-2, 3.819e-2, 4.413e-2, 2.398e-2]
ok &= all(abs(p["best"]["resp2"]/r - 1) < 0.3
          for p, r in zip(P, RESP_PIN))
gate("g8 the collision probe: even in d (rel 1e-6); resp2 pinned", ok)

# ---------------------------------------------------------------- g9
ok = all(abs(p["best"]["db"]/pin - 1) < 0.25 for p, pin in zip(P, PIN_DB))
gate("g9 the d_bounds pinned: every in-band collision pair within "
     "~1e-5 of the critical line", ok)

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
normp = re.sub(r"\s+", " ", paper)
plain = normp.replace("**", "")
needles = [
    "Theorem 1bf (the two-sided witness",
    "section-level Weil positivity",
    "the prime term cancels the archimedean",
    "the truncation-tail discovery",
    "The collision injection",
    "millionths of the critical line",
    "no RH leverage claimed",
]
ok = all(nd in plain for nd in needles)
for nd in needles:
    if nd not in plain:
        print(f"  g13 MISSING: {nd!r}", flush=True)
ok &= paper.count("`cascade_twosided_witness.py`") >= 2
ok &= "the **82 scripts cited in place** above" in normp
ok &= "extended by Theorems 1i–1bf:" in normp
gate("g13 the 1bf paper needles and the footer census (backticked >= 2; "
     "the anchored count and range needles)", ok)

print(("\nALL GATES PASS (14/14)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
