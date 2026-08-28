#!/usr/bin/env python3
"""Theorem 1bj -- the one-prime window certified: interval-rigorous
Weil positivity beyond log 2. Tower member 19 (top).

THE CLAIM GATED. For test support length delta < log 3 the
semi-local one-prime Weil form IS Weil's full quadratic
functional (the only prime power in the autocorrelation window
is log 2). The four interval instruments certify positivity --
the full form on [log 2, 1.0], the odd sector through 1.09 --
with every ingredient an interval enclosure: Stage I encloses
the kernel W (Binet + in-house transcendentals, no libm trust);
Stage II certifies the eight Birman-Schwinger count rows (the
pole-free ell2 <= lambda_2 premises); Stage II-b (round 7, the
deflation arc) certifies the POLE-INCLUSIVE count at the
even-1.0 frontier -- the pole kept inside the counting
operator, the Woodbury secular certificate g(beta') < 0 under a
two-sided count-regime gate -- giving lambda_2(T_even) >= 0.015
with no interlacing loss; Stage III certifies the eight
Kato-Temple ratio-form cells (even ell2 = nu* through 0.95; the
even-1.0 cell on the Stage II-b premise with a degree-10
Gegenbauer polynomial trial part; odd two-stage, pole-free nu1
then negative-rank-one interlacing). This
verifier loads the four committed checkpoints AT THEIR CURRENT
EXECUTABLE-CONTENT KEYS (a stale or mangled instrument cannot
match), pins every certified margin, re-checks the premise
wiring and the window arithmetic, demonstrates the certificate
predicate can fail (mangle probes), and carries the chain and
census obligations of the tower.

Gates (thirteen, g0-g12):
  g0  the four checkpoints load at the current keys with
      complete states (8 count rows + __gII4__; 8 temple cells
      + the theorem flag; 2 pole-inclusive rows + __gP4__ +
      __nustar__)
  g1  the Stage I record: gI2 pass; W-width max <= the cap
      (7.49e-7 <= 1.2e-6); the derivative majorants pinned
  g2  all eight count rows certified with margins pinned to
      4 significant figures (2.436e-1 ... 2.058e-4 ...
      2.753e-2)
  g3  all eight temple cells certified, premise_ok, theorem
      flag True, temple_lo pinned to 4 significant figures
  g4  the premise wiring: even ell2 = [nu*, nu*] with the
      matching count row certified at that nu THROUGH 0.95;
      the even-1.0 ell2 = [0.015, 0.015] backed by the
      CERTIFIED Stage II-b pole row at that nu (its pole-free
      count row sits at nu = 0.01 and does NOT back it); odd
      ell2 = [nu1, nu1] from a positive, premise_ok stage-1
      record whose OWN ell2 equals the certified odd count
      row's nu (the stage-1 link re-checkable since round 252)
  g5  the window arithmetic, LIVE from the checkpoint key
      strings (round-252): the key set matches the pins;
      every certified delta < log 3 (the one-prime =
      full-form identity domain); the even maximum 1.0 >=
      log 2; the odd maximum 1.09 < log 3
  g6  the deflation closure wired end to end: "even:1" carries
      BOTH the certified pole-free count row (margin pinned
      2.058e-4 at nu = 0.01 -- the recorded interlacing
      ceiling) AND a certified temple cell whose ell2 = 0.015
      equals the certified pole row's nu; the pole rows' nu
      ladder is consistent (0.014 < 0.015 = __nustar__)
  g7  internal consistency: per cell temple_lo <= rho.lo
      (Temple sits below the Rayleigh quotient) and
      rho.hi < ell2.lo (the ratio-form premise)
  g8  stored-enclosure sanity: S.lo >= 0, n in [0.5, 2],
      and sigma2_hi < ell2.lo (ell2.lo - rho.hi) -- the
      Temple gap condition, ASSERTED from the stored
      enclosures (round-252, reviewer-3 F1: the docstring
      had described this conjunct while the code carried a
      duplicate of g7)
  g9  mangle probes: the certificate predicate FAILS on a
      sign-flipped temple_lo and on a premise-violating
      (rho.hi >= ell2.lo) mangled copy -- the gate can fail
  g10 the chain obligation to cascade_floor_theory.py
      (Theorem 1bi) met
  g11 the 1bj paper needles and the footer census (backticked
      >= 2; the anchored count and range needles)
  g12 the Stage II-b rows: both certified with g(beta') < 0
      strictly (interval hi), margins pinned (2.486e-3,
      3.016e-3), the count-regime gaps positive, and the
      mangle probe fails (a g interval crossing 0)

Checks 7/8 clean: Kato-Temple, Birman-Schwinger, interlacing,
Binet, Hurwitz zeta, IEEE-754 intervals -- classical; no
semiclassics; no hypothesis input (Riemann-side).
"""
import math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from oneprime_interval_core import run as run_I
from oneprime_interval_count import run as run_II
from oneprime_interval_pole import run as run_IIb
from oneprime_interval_temple import run as run_III

PAPER = os.path.join(HERE, "..", "..",
                     "riemann-indistinguishability.md")
paper = open(PAPER, encoding="utf-8").read()

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

P1 = run_I()
P2 = run_II()
P4 = run_IIb()
P3 = run_III()

COUNT_PINS = {
    "even:0.6931": 2.436e-1, "even:0.8": 4.199e-3,
    "even:0.9": 1.457e-2, "even:0.95": 3.641e-3,
    "even:1": 2.058e-4, "odd:0.9": 4.114e-1,
    "odd:1.05": 8.644e-3, "odd:1.09": 2.753e-2,
}
TEMPLE_PINS = {
    "even:0.6931": 1.295e-3, "even:0.8": 1.689e-4,
    "even:0.9": 1.009e-5, "even:0.95": 7.357e-7,
    "even:1": 2.683e-7,
    "odd:0.9": 1.373e-3, "odd:1.05": 2.258e-5,
    "odd:1.09": 4.852e-6,
}
POLE_PINS = {"even:0.014:2": 2.486e-3,
             "even:0.015:2.5": 3.016e-3}
NUSTAR_POLE = 0.015
# deltas are DERIVED from the checkpoint key strings at gate
# time (round-252 sweep, reviewer-3 F2: the hand-listed dict
# was constant arithmetic -- a gate that could not fail against
# external state)

def pin4(x, pin):
    return abs(x - pin) <= 5e-4*abs(pin)

# ---------------------------------------------------------------- g0
ok = set(P2) == set(COUNT_PINS) | {"__gII4__"}
ok &= set(P3) == set(TEMPLE_PINS) | {"theorem"}
ok &= set(P4) == set(POLE_PINS) | {"__gP4__", "__nustar__"}
ok &= all(k in P1 for k in ("gI2", "wmax", "wcap", "m1", "m2"))
gate("g0 the four checkpoints load at the current keys with "
     "complete states (8 count rows; 8 temple cells + theorem; "
     "2 pole rows)", ok)

# ---------------------------------------------------------------- g1
ok = P1["gI2"] == "pass" and P1["wmax"] <= P1["wcap"]
ok &= pin4(P1["wmax"], 7.492e-7) and P1["wcap"] == 1.2e-6
ok &= pin4(P1["m1"], 9.502) and pin4(P1["m2"], 33.07)
gate("g1 the Stage I record: gI2 pass; W-width 7.49e-7 <= "
     "1.2e-6; majorants pinned", ok)

# ---------------------------------------------------------------- g2
ok = all(P2[k]["certified"] and pin4(P2[k]["margin"], v)
         for k, v in COUNT_PINS.items())
gate("g2 all eight count rows certified with margins pinned "
     "(2.436e-1 ... 2.058e-4 ... 2.753e-2)", ok)

# ---------------------------------------------------------------- g3
ok = bool(P3["theorem"])
ok &= all(P3[k]["certified"] and P3[k]["premise_ok"]
          and pin4(P3[k]["temple_lo"], v)
          for k, v in TEMPLE_PINS.items())
gate("g3 all eight temple cells certified, premise_ok, theorem "
     "True, temple_lo pinned", ok)

# ---------------------------------------------------------------- g4
ok = True
for k in TEMPLE_PINS:
    cell = P3[k]
    row = P2[k]
    lo, hi = cell["ell2"]
    if k == "even:1":
        # the deflation premise: ell2 from the CERTIFIED Stage
        # II-b pole row, NOT the (nu = 0.01) pole-free count row
        prow = P4[f"even:{NUSTAR_POLE:g}:2.5"]
        ok &= lo == hi == NUSTAR_POLE == prow["nu"]
        ok &= prow["certified"] and row["certified"]
        ok &= row["nu"] == 0.01
    elif k.startswith("even"):
        ok &= lo == hi == row["nu"] and row["certified"]
    else:
        s1 = cell["stage1"]
        ok &= s1["premise_ok"] and s1["temple_lo"] > 0
        ok &= s1["ell2"][0] == s1["ell2"][1] == row["nu"]
        ok &= lo == hi == s1["temple_lo"] and row["certified"]
gate("g4 the premise wiring: even ell2 = nu* at a certified "
     "count row; odd ell2 = stage-1 nu1 > 0 with premise_ok "
     "and a certified odd count row", ok)

# ---------------------------------------------------------------- g5
L3 = math.log(3.0)
cells_live = (set(P2) - {"__gII4__"}) | (set(P3) - {"theorem"})
dl = {k: float(k.split(":")[1]) for k in cells_live}
ok = set(dl) == set(COUNT_PINS) | set(TEMPLE_PINS)
ok &= all(d < L3 for d in dl.values())
ev = sorted(d for k, d in dl.items()
            if k.startswith("even") and k in P3)
od = sorted(d for k, d in dl.items() if k.startswith("odd"))
ok &= ev[-1] == 1.0 and 1.0 >= math.log(2.0)
ok &= od[-1] == 1.09 and 1.09 < L3
ok &= ev == sorted(set(ev)) and od == sorted(set(od))
gate("g5 the window arithmetic: every delta < log 3 (the "
     "one-prime = full-form domain); even max 1.0 >= log 2; "
     "odd max 1.09; nesting order", ok)

# ---------------------------------------------------------------- g6
ok = "even:1" in P2 and P2["even:1"]["certified"] \
    and pin4(P2["even:1"]["margin"], 2.058e-4) \
    and P2["even:1"]["nu"] == 0.01
ok &= "even:1" in P3 and P3["even:1"]["certified"]
nus_p = sorted(P4[k]["nu"] for k in POLE_PINS)
ok &= nus_p == [0.014, 0.015] and P4["__nustar__"] == 0.015
ok &= P3["even:1"]["ell2"][0] == 0.015
gate("g6 the deflation closure wired: even:1 carries the "
     "pole-free count row (2.058e-4 at nu 0.01, the interlacing "
     "ceiling) AND a certified temple cell at ell2 = 0.015 = "
     "the certified pole row's nu", ok)

# ---------------------------------------------------------------- g7
ok = all(P3[k]["temple_lo"] <= P3[k]["rho"][0]
         and P3[k]["rho"][1] < P3[k]["ell2"][0]
         for k in TEMPLE_PINS)
gate("g7 internal consistency: temple_lo <= rho.lo and "
     "rho.hi < ell2.lo per cell", ok)

# ---------------------------------------------------------------- g8
ok = all(P3[k]["S"][0] >= 0 and 0.5 < P3[k]["n"][0]
         and P3[k]["n"][1] < 2.0
         and P3[k]["sigma2_hi"]
         < P3[k]["ell2"][0]*(P3[k]["ell2"][0]
                             - P3[k]["rho"][1])
         for k in TEMPLE_PINS)
gate("g8 stored-enclosure sanity: S >= 0, n in [0.5, 2], and "
     "sigma2_hi < ell2 (ell2 - rho.hi) -- the Temple gap "
     "condition from the stored intervals", ok)

# ---------------------------------------------------------------- g9
def cert_ok(cell):
    return (cell["certified"] and cell["premise_ok"]
            and cell["temple_lo"] is not None
            and cell["temple_lo"] > 0
            and cell["rho"][1] < cell["ell2"][0])
m1_ = dict(P3["even:0.95"]); m1_["temple_lo"] = -m1_["temple_lo"]
m2_ = dict(P3["odd:1.09"]); m2_["ell2"] = [m2_["rho"][1]*0.5]*2
ok = all(cert_ok(P3[k]) for k in TEMPLE_PINS)
ok &= (not cert_ok(m1_)) and (not cert_ok(m2_))
gate("g9 mangle probes: the certificate predicate fails on a "
     "sign-flipped temple_lo and a premise-violating ell2", ok)

# ---------------------------------------------------------------- g10
from cascade_tower import chain_ok
gate("g10 the chain obligation to cascade_floor_theory.py "
     "(Theorem 1bi) met", chain_ok("cascade_floor_theory.py"))

# ---------------------------------------------------------------- g11
import re
normp = re.sub(r"\s+", " ", paper)
plain = normp.replace("**", "")
needles = [
    "Theorem 1bj (the one-prime window certified",
    "the one-prime form is the full functional below log 3",
    "every ingredient an interval enclosure",
    "the full form on [log 2, 1.0] and the odd sector through 1.09",
    "the first explicit unconditional positivity threshold beyond log 2",
    "no Riemann Hypothesis consequence is claimed",
    "the even ground state is near-degenerate at the top of the window",
    "the pole kept inside the counting operator",
    "with no interlacing loss",
    "(1.0 \u2212 log 2)/(log 3 \u2212 log 2) = 75.7%",
    "2.6832\u00d710\u207b\u2077 (1.0)",
]
ok = all(nd in plain for nd in needles)
for nd in needles:
    if nd not in plain:
        print(f"  g11 MISSING: {nd!r}", flush=True)
ok &= paper.count("`cascade_oneprime_interval.py`") >= 2
ok &= "the **86 scripts cited in place** above" in normp
ok &= "extended by Theorems 1i–1bj:" in normp
gate("g11 the 1bj paper needles and the footer census "
     "(backticked >= 2; the anchored count and range needles)",
     ok)

# --------------------------------------------------------------- g12
ok = all(P4[k]["certified"] and pin4(P4[k]["gmargin"], v)
         and P4[k]["g"][1] < 0.0
         and P4[k]["gap_lo"] > 0 and P4[k]["gap_hi"] > 0
         for k, v in POLE_PINS.items())
mp_ = dict(P4[f"even:{NUSTAR_POLE:g}:2.5"])
mp_["g"] = [mp_["g"][0], abs(mp_["g"][1])]

def pole_ok(row):
    return (row["certified"] and row["g"][1] < 0.0
            and row["gap_lo"] > 0 and row["gap_hi"] > 0)

ok &= all(pole_ok(P4[k]) for k in POLE_PINS)
ok &= not pole_ok(mp_)
gate("g12 the Stage II-b rows: certified, g(beta') < 0 "
     "strictly, margins pinned (2.486e-3, 3.016e-3), count-"
     "regime gaps positive; mangle probe fails", ok)

print(("\nALL GATES PASS (13/13)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
