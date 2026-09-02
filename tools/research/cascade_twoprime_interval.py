#!/usr/bin/env python3
"""Theorem 1bk -- the two-prime window opened: interval-rigorous
Weil positivity beyond log 3 in the odd sector. Tower member 20
(top).

THE CLAIM GATED. For test support length delta in [log 3, log 4)
the semi-local two-prime Weil form (the real place plus the
primes 2 and 3) IS Weil's full quadratic functional (the prime
powers inside the autocorrelation window are exactly log 2 and
log 3). At delta = 1.10 the ODD sector is certified positive,
lambda_1(T_odd) >= the pinned Temple value, every ingredient an
interval enclosure: Stage 1 the POLE-INCLUSIVE Birman-Schwinger
count (the odd pole enters the counting operator with a positive
sign, so the bordered frame Gram is a genuine Gram and the
verified eigen-enclosure certifies lambda_2(T_odd) >= nu* = 0.05
directly -- no interlacing, no secular gate); Stage 2 the Kato-
Temple ratio-form certificate at ell2 = nu* on a frozen pure-
harmonic entire trial through the two-shift closed-form operator.
By domain nesting the certified value bounds the odd-sector margin
at the log 3 threshold and on the whole one-prime window: the
rigorous odd-sector answer to A418's structural question (the
margin does not vanish at the threshold).

This verifier loads the two checkpoints AT THEIR CURRENT
EXECUTABLE-CONTENT KEYS (a stale or mangled instrument cannot
match), pins the certified margins, re-checks the premise wiring
and the window arithmetic (including the tail lemma constant and
the two kink positions), demonstrates the certificate predicate
can fail (mangle probes), and carries the chain and census
obligations of the tower.

Gates (eleven, g0-g10):
  g0  the two checkpoints load at the current keys with
      complete states (the count row; the temple cell + theorem)
  g1  the count row: certified, nu 0.05, beta 2.0, a 0.55,
      rmax 600, H 0.02; margin pinned (9.054e-3 to 4 sf);
      mu2 + EOP < beta from the stored enclosures; the pole's
      cost mu2 - mu2_polefree in (0.03, 0.06) (its strength
      <g,g> = 2(sinh a - a) = 0.0563 pinned); m and the support
      length pinned
  g2  the temple cell: certified, premise_ok, theorem True,
      temple_lo pinned to 4 sf
  g3  the premise wiring: temple ell2 = [nu*, nu*] with nu* =
      the certified count row's nu = ROW nu; the fixture's a
      = the count row's a = 0.55
  g4  the window arithmetic, LIVE: delta = 2a = 1.10 in
      (log 3, log 4); both kinks log 2 - a and log 3 - a inside
      (0, a); the tail lemma constant h+(600) - C2 - C3 > nu +
      beta recomputed from the interval core; C3 = 2 log 3 /
      sqrt 3 pinned
  g5  internal consistency: temple_lo <= rho.lo; rho.hi <
      ell2.lo; S.lo >= 0; n in [0.5, 2]; sigma2_hi <
      ell2 (ell2 - rho.hi)
  g6  mangle probes: the certificate predicate fails on a
      sign-flipped temple_lo, a premise-violating ell2, and a
      count row with mu2 + EOP >= beta
  g7  the nesting corollary's arithmetic: 1.10 > log 3, so the
      certified bound applies at the threshold
  g8  the chain obligation to cascade_oneprime_interval.py
      (Theorem 1bj) met
  g9  the 1bk paper needles and the footer census (declared
      surface)
  g10 the float-fixture consistency: the stored fixture's
      rho_float within 1e-4 of the enclosed rho; its Temple
      float within a factor 3 of the certified value

Checks 7/8 clean: Kato-Temple, Birman-Schwinger, Weyl
monotonicity, Binet, IEEE-754 intervals -- classical; no
semiclassics; no hypothesis input (Riemann-side).
"""
import math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from twoprime_interval_count import run as run_C, ROW, A_CELL, RMAX, C3I, C2I, LOG3
from twoprime_interval_temple import run as run_T
from oneprime_interval_core import W_enclose, I, LOG2, icos, _d

# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g9', 's': 'Theorem 1bk (the two-prime window opened', 'form': 'plain'},
    {'g': 'g9', 's': 'the two-prime form is the full functional on [log 3, log 4)', 'form': 'plain'},
    {'g': 'g9', 's': 'the odd sector at support length 1.10', 'form': 'plain'},
    {'g': 'g9', 's': 'the pole-inclusive count', 'form': 'plain'},
    {'g': 'g9', 's': 'the margin at the log 3 threshold does not vanish', 'form': 'plain'},
    {'g': 'g9', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 2},
    {'g': 'g9', 's': 'the even sector is open on the whole two-prime window', 'form': 'plain'},
    {'s': '`cascade_twoprime_interval.py`', 'min': 2, 'g': 'g9'},
    {'s': 'the **87 scripts cited in place** above', 'form': 'ws', 'g': 'g9'},
    {'s': 'extended by Theorems 1i–1bk:', 'form': 'ws', 'g': 'g9'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

PC = run_C()
PT = run_T()

COUNT_PIN = 9.054e-3
TEMPLE_PIN = None            # set at the landing from the Stage-2 checkpoint
GG_PIN = 0.05632
M_PIN = 4616
SUPPORT_PIN = 87.0

def pin4(x, pin):
    return abs(x - pin) <= 5e-4*abs(pin)

# ---------------------------------------------------------------- g0
ok = set(PC) == {"odd:1.1"} and set(PT) == {"odd:1.1", "theorem"}
row = PC.get("odd:1.1", {})
cell = PT.get("odd:1.1", {})
ok &= all(k in row for k in ("certified", "margin", "mu2", "mu2_polefree", "eop",
                             "nu", "beta", "a", "rmax", "H", "m", "support_len", "gg"))
ok &= all(k in cell for k in ("certified", "premise_ok", "temple_lo", "rho", "ell2",
                              "n", "S", "sigma2_hi", "fixture"))
gate("g0 the two checkpoints load at the current keys with complete "
     "states (the count row; the temple cell + theorem)", ok)

# ---------------------------------------------------------------- g1
ok = row["certified"] and row["nu"] == 0.05 and row["beta"] == 2.0 \
    and row["a"] == 0.55 and row["rmax"] == 600.0 and row["H"] == 0.02
ok &= pin4(row["margin"], COUNT_PIN)
ok &= row["mu2"][1] + row["eop"] < row["beta"]
ok &= 0.03 < row["mu2"][0] - row["mu2_polefree"][1] < 0.06
ok &= pin4(0.5*(row["gg"][0] + row["gg"][1]), GG_PIN)
ok &= row["m"] == M_PIN and pin4(row["support_len"], SUPPORT_PIN)
gate("g1 the count row: certified at (0.05, 2.0, a 0.55, rmax 600, H "
     "0.02); margin pinned 9.054e-3; mu2 + EOP < beta; pole cost in "
     "(0.03, 0.06), <g,g> pinned; m and support pinned", ok)

# ---------------------------------------------------------------- g2
ok = bool(PT["theorem"]) and cell["certified"] and cell["premise_ok"] \
    and cell["temple_lo"] is not None and cell["temple_lo"] > 0
ok &= TEMPLE_PIN is not None and pin4(cell["temple_lo"], TEMPLE_PIN)
gate("g2 the temple cell certified, premise_ok, theorem True, temple_lo "
     f"pinned ({TEMPLE_PIN})", ok)

# ---------------------------------------------------------------- g3
lo, hi = cell["ell2"]
ok = lo == hi == row["nu"] == ROW["nu"]
ok &= cell["fixture"]["a"] == row["a"] == A_CELL
gate("g3 the premise wiring: temple ell2 = [nu*, nu*] = the certified "
     "count row's nu = ROW nu; the fixture's a = the count row's a", ok)

# ---------------------------------------------------------------- g4
a = cell["fixture"]["a"]
L3, L4 = math.log(3.0), math.log(4.0)
delta = 2*a
ok = L3 < delta < L4 and abs(delta - 1.10) < 1e-12
ok &= 0 < math.log(2.0) - a < a and 0 < L3 - a < a
wr = W_enclose(RMAX)
hplus_lo = (wr + C2I*icos(I(RMAX)*LOG2)).lo
ok &= _d(_d(hplus_lo - C2I.hi) - C3I.hi) > row["nu"] + row["beta"]
ok &= pin4(0.5*(C3I.lo + C3I.hi), 2*math.log(3)/math.sqrt(3))
gate("g4 the window arithmetic LIVE: delta 1.10 in (log 3, log 4); both "
     "kinks inside (0, a); tail lemma h+(600) - C2 - C3 > nu + beta "
     "from the interval core; C3 pinned", ok)

# ---------------------------------------------------------------- g5
ok = cell["temple_lo"] <= cell["rho"][0] and cell["rho"][1] < cell["ell2"][0]
ok &= cell["S"][0] >= 0 and 0.5 < cell["n"][0] and cell["n"][1] < 2.0
ok &= cell["sigma2_hi"] < cell["ell2"][0]*(cell["ell2"][0] - cell["rho"][1])
gate("g5 internal consistency: temple_lo <= rho.lo; rho.hi < ell2.lo; "
     "S >= 0; n in [0.5, 2]; sigma2_hi < ell2 (ell2 - rho.hi)", ok)

# ---------------------------------------------------------------- g6
def cert_ok(c):
    return (c["certified"] and c["premise_ok"] and c["temple_lo"] is not None
            and c["temple_lo"] > 0 and c["rho"][1] < c["ell2"][0])
def count_ok(r):
    return r["certified"] and r["mu2"][1] + r["eop"] < r["beta"]
m1_ = dict(cell); m1_["temple_lo"] = -m1_["temple_lo"]
m2_ = dict(cell); m2_["ell2"] = [m2_["rho"][1]*0.5]*2
m3_ = dict(row); m3_["eop"] = m3_["beta"]
ok = cert_ok(cell) and count_ok(row)
ok &= (not cert_ok(m1_)) and (not cert_ok(m2_)) and (not count_ok(m3_))
gate("g6 mangle probes: the certificate predicate fails on a sign-flipped "
     "temple_lo, a premise-violating ell2, and a count row with mu2 + EOP "
     ">= beta", ok)

# ---------------------------------------------------------------- g7
gate("g7 the nesting corollary's arithmetic: 1.10 > log 3, so the "
     "certified odd bound applies at the threshold and below",
     delta > L3)

# ---------------------------------------------------------------- g8
from cascade_tower import chain_ok
gate("g8 the chain obligation to cascade_oneprime_interval.py (Theorem "
     "1bj) met", chain_ok("cascade_oneprime_interval.py"))

# ---------------------------------------------------------------- g9
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g9 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g9 the 1bk paper needles and the footer census (declared surface)", ok)

# ---------------------------------------------------------------- g10
fx = cell["fixture"]
ok = abs(0.5*(cell["rho"][0] + cell["rho"][1]) - fx["rho_float"]) < 1e-4
ok &= cell["temple_lo"] > 0 and fx["temple_float"] > 0 \
    and 1/3 < fx["temple_float"]/cell["temple_lo"] < 3
gate("g10 the float-fixture consistency: rho within 1e-4; the float "
     "Temple within a factor 3 of the certified value", ok)

print(("\nALL GATES PASS (11/11)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
