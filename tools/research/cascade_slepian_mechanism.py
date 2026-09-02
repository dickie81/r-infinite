#!/usr/bin/env python3
"""Theorem 1bl -- positivity by mechanism: Weil's full functional
positive on [0, 1.3828125] in BOTH sectors, uniformly over every
probe, by Slepian concentration and a verified head matrix. Tower
member 21 (top).

THE CLAIM GATED. For a real probe g of fixed parity supported on
[-a, a], the S-local Weil form Q(g) = (1/2pi) int |ghat|^2 W dr
+/- 2 <chi, g>^2 is Weil's full functional whenever 2a is below the
next prime-power lag. For any Omega with W_out = W_inf(Omega) -
sum w > 0, Q(g) >= <g, M g> with M = A_in + W_out (I - K) +/- 2 chi
chi^T (K the Slepian concentration operator of (a, Omega)), and in
the prolate basis lambda_min(Q) >= lambda_min of the 2x2
[[lambda_min(M_head), -b], [-b, q_perp]] (A425). The substrate
slepian_arb_certificate.py evaluates every quantity in 256-bit ball
arithmetic (python-flint): verified prolates (residual + Sturm count +
gap), Slepian eigenvalues through NH+1, band integrals by 30-point
Gauss-Legendre with Trefethen's Bernstein-ellipse error bound, a
verified Cholesky lower bound on the head, the 2x2 in balls. Four
cells: one-prime a = 35/64 (delta 1.09375 < log 3, Omega 64) and
two-prime a = 177/256 (delta 1.3828125 < log 4, Omega 128), even and
odd. By domain nesting the certified value at a cell bounds the
margin at every shorter support.

This verifier loads the four checkpoints AT THEIR CURRENT
EXECUTABLE-CONTENT KEYS (a stale or mangled instrument cannot
match), pins the certified bounds in the safe direction, re-checks
the cells' arithmetic and the outside bound W_out > 0 LIVE (acb
digamma), re-derives the 2x2 from the stored head/tail/coupling
data, checks the monotonicity consistency with the interval
instruments' certified cells, demonstrates the certificate predicate
can fail (mangle probes), and carries the chain and census
obligations of the tower.

Gates (eleven, g0-g10):
  g0  the four checkpoints load at the current keys with complete
      states (verdict THEOREM, final > 0, every field present)
  g1  the certified bounds pinned in the safe direction: the paper's
      stated bound <= the stored final, and within 5e-4 relative
      (one/even 4.3420e-8, one/odd 1.3566e-5, two/even 5.7134e-13,
      two/odd 3.9537e-10)
  g2  the cells LIVE: a = 35/64 -> delta = 1.09375 < log 3, a = 177/256
      -> delta = 1.3828125 < log 4; c = a Omega = 35, 88.5; the
      outside bound W_out = Re psi(1/4 + i Omega/2) - log pi - sum w
      recomputed with acb digamma, positive and within 1e-9 of the
      stored lower bound; the strip/disk conditions of the
      quadrature error bound recomputed (rho = 3)
  g3  the 2x2 re-derived from the stored (lam_head, q_perp, b): equal
      to the stored final to 1e-9 relative, positive, b^2 < lam_head
      q_perp
  g4  internal consistency: every prolate through NH+1 resolved
      (kstar >= NH+2), Lambda_tail <= 1e-40, max eps <= 1.1e-40,
      min gap > 60, ||Gamma - I|| <= 1e-40, quadrature error <= 1e-19,
      P_perp^2 >= 0, prec 256, NH/h/Omega as configured
  g5  the head's slack is small: final >= 0.99 lam_head (the 2x2
      costs under 1 percent -- the tail carries the mechanism)
  g6  mangle probes: the certificate predicate fails on a sign-flipped
      final, on a coupling with b^2 >= lam_head q_perp, and on a
      truncated head (kstar < NH+2)
  g7  the nesting corollary: the new tops exceed the interval
      instruments' (even 1.3828125 > 1.0 of 1bj; odd 1.3828125 > 1.10
      of 1bk; one-prime 1.09375 < log 3 within 0.005)
  g8  the chain obligation to cascade_twoprime_interval.py (Theorem
      1bk) met
  g9  the 1bl paper needles and the footer census (declared surface)
  g10 monotonicity consistency with the interval instruments: a
      rigorous lower bound at LARGER support never exceeds the Temple
      instrument's enclosed ground-state estimate rho at SMALLER
      support (one-prime odd 1.09375 vs the Temple's odd 1.09 cell;
      one-prime even 1.09375 vs the Temple's even 1.0 cell), the
      Temple checkpoint loaded at its current key

Checks 7/8 clean: Slepian, Paley-Wiener, Bernstein ellipses, Binet,
Stirling, ball arithmetic -- classical; no semiclassics; no hypothesis
input (Riemann-side).
"""
import math, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)

from slepian_arb_certificate import run as run_SM, CELLS, PREC
from oneprime_interval_temple import run as run_T1

# declared paper surface (the needle-precheck arc, A397): the
# member touches the paper ONLY through these entries.
PAPER_NEEDLES = [
    {'g': 'g9', 's': 'Theorem 1bl (positivity by mechanism', 'form': 'plain'},
    {'g': 'g9', 's': 'positive for every even and every odd probe of support length', 'form': 'plain'},
    {'g': 'g9', 's': 'the uncertainty principle is the tail', 'form': 'plain'},
    {'g': 'g9', 's': 'no Temple trial, no Birman', 'form': 'plain'},
    {'g': 'g9', 's': 'no Riemann Hypothesis consequence is claimed', 'form': 'plain', 'min': 3},
    {'g': 'g9', 's': 'net state after Theorem 1bl', 'form': 'plain'},
    {'s': '`cascade_slepian_mechanism.py`', 'min': 2, 'g': 'g9'},
    {'s': 'the **88 scripts cited in place** above', 'form': 'ws', 'g': 'g9'},
    {'s': 'extended by Theorems 1i–1bl:', 'form': 'ws', 'g': 'g9'},
]

fails = []
def gate(label, ok):
    print(("PASS " if ok else "FAIL ") + label, flush=True)
    if not ok:
        fails.append(label)

ST = {(k, p): run_SM(k, p) for k in ("one", "two") for p in ("even", "odd")}
PT = run_T1()

PINS = {("one", "even"): 4.3420e-8, ("one", "odd"): 1.3566e-5,
        ("two", "even"): 5.7134e-13, ("two", "odd"): 3.9537e-10}
FIELDS = ("kernel", "parity", "a", "delta", "Omega", "NH", "h", "NGL", "nmax", "prec", "lam_head",
          "normE", "Lam_tail", "Pperp2", "q_perp", "b", "final", "W_out_lo", "M_W", "max_quad_err",
          "max_residual", "min_gap", "max_eps", "kstar", "verdict")

def pin4(x, pin):
    return abs(x - pin) <= 5e-4*abs(pin)

# ---------------------------------------------------------------- g0
ok = all(all(f in st for f in FIELDS) for st in ST.values())
ok &= all(st["verdict"].startswith("THEOREM") and st["final"] > 0 for st in ST.values())
ok &= all(st["kernel"] == k and st["parity"] == p for (k, p), st in ST.items())
gate("g0 the four checkpoints load at the current keys with complete states "
     "(verdict THEOREM, final > 0)", ok)

# ---------------------------------------------------------------- g1
ok = all(PINS[kp] <= st["final"] and pin4(st["final"], PINS[kp]) for kp, st in ST.items())
gate("g1 the certified bounds pinned in the safe direction (stated <= stored; "
     "within 5e-4 relative): 4.3420e-8, 1.3566e-5, 5.7134e-13, 3.9537e-10", ok)

# ---------------------------------------------------------------- g2
from flint import acb, arb, ctx
def W_out_live(kernel, Omega):
    with ctx.workprec(PREC):      # precision by context manager, never a store (clause G)
        z = acb(arb(1)/4, arb(Omega)/2)
        v = z.digamma().real - arb.pi().log() - arb(2).sqrt()*arb(2).log()
        if kernel == "two":
            v = v - 2*arb(3).log()/arb(3).sqrt()
        return float(v.lower())
A_EXACT = {"one": 35/64, "two": 177/256}
NEXT = {"one": math.log(3.0), "two": math.log(4.0)}
ok = True
for (k, p), st in ST.items():
    ok &= abs(st["a"] - A_EXACT[k]) < 1e-15 and abs(st["delta"] - 2*A_EXACT[k]) < 1e-15
    ok &= st["delta"] < NEXT[k]
    ok &= abs(A_EXACT[k]*st["Omega"] - {"one": 35.0, "two": 88.5}[k]) < 1e-12
    wl = W_out_live(k, st["Omega"])
    ok &= wl > 0 and abs(wl - st["W_out_lo"]) < 1e-9
    rho = 3.0; h = st["h"]
    ok &= (h/2)*(rho - 1/rho)/2 < 0.5/st["Omega"]
    ok &= st["Omega"]*((h/2)*(rho + 1/rho)/2)/2 < 0.25
gate("g2 the cells LIVE: delta = 2a below the next prime-power lag; c = a Omega exact; "
     "W_out recomputed with acb digamma, positive, matching the stored bound; the "
     "strip/disk conditions hold at rho = 3", ok)

# ---------------------------------------------------------------- g3
def two_by_two(lh, qp, b):
    # in ball arithmetic, as the instrument does it (a float sqrt cancels
    # catastrophically when lam_head ~ 1e-13 against q_perp ~ 1): the lower
    # endpoint of 0.5 (tr - sqrt(tr^2 - 4 det))
    with ctx.workprec(PREC):
        lh, qp, b = arb(lh), arb(qp), arb(b)
        tr = lh + qp; det = lh*qp - b*b
        return float((0.5*(tr - (tr*tr - 4*det).sqrt())).lower())
ok = True
for st in ST.values():
    f2 = two_by_two(st["lam_head"], st["q_perp"], st["b"])
    ok &= abs(f2 - st["final"]) <= 1e-9*abs(st["final"]) and f2 > 0
    ok &= st["b"]**2 < st["lam_head"]*st["q_perp"]
gate("g3 the 2x2 re-derived from the stored head/tail/coupling in ball arithmetic "
     "equals the stored final (1e-9 relative), positive, b^2 < lam_head q_perp", ok)

# ---------------------------------------------------------------- g4
ok = True
for (k, p), st in ST.items():
    cfg = CELLS[k]
    ok &= st["kstar"] >= st["NH"] + 2 and st["Lam_tail"] <= 1e-40 and st["max_eps"] <= 1.1e-40
    ok &= st["min_gap"] > 60 and st["normE"] <= 1e-40 and st["max_quad_err"] <= 1e-19
    ok &= st["Pperp2"] >= 0 and st["prec"] == 256
    ok &= st["NH"] == cfg["NH"] and st["h"] == cfg["h"] and st["Omega"] == cfg["Omega"]
gate("g4 internal consistency: every prolate through NH+1 resolved; Lambda_tail, eps, "
     "||Gamma - I|| <= 1e-40; min gap > 60; quadrature error <= 1e-19; configuration "
     "as declared", ok)

# ---------------------------------------------------------------- g5
ok = all(st["final"] >= 0.99*st["lam_head"] for st in ST.values())
gate("g5 the 2x2 costs under one percent of the head's minimum eigenvalue "
     "(the tail carries the mechanism)", ok)

# ---------------------------------------------------------------- g6
def cert_ok(st):
    return (st["verdict"].startswith("THEOREM") and st["final"] > 0
            and st["b"]**2 < st["lam_head"]*st["q_perp"] and st["kstar"] >= st["NH"] + 2)
s0 = ST[("two", "even")]
m1 = dict(s0); m1["final"] = -m1["final"]
m2 = dict(s0); m2["b"] = math.sqrt(m2["lam_head"]*m2["q_perp"])*1.01
m3 = dict(s0); m3["kstar"] = m3["NH"]
ok = cert_ok(s0) and not cert_ok(m1) and not cert_ok(m2) and not cert_ok(m3)
gate("g6 mangle probes: the certificate predicate fails on a sign-flipped final, a "
     "coupling with b^2 >= lam_head q_perp, and a truncated head", ok)

# ---------------------------------------------------------------- g7
d2 = ST[("two", "even")]["delta"]; d1 = ST[("one", "even")]["delta"]
ok = d2 > 1.0 and d2 > 1.10 and d1 < math.log(3.0) and math.log(3.0) - d1 < 0.005
gate("g7 the nesting corollary: 1.3828125 exceeds 1bj's even top 1.0 and 1bk's odd top "
     "1.10; the one-prime cell sits within 0.005 of log 3", ok)

# ---------------------------------------------------------------- g8
from cascade_tower import chain_ok
gate("g8 the chain obligation to cascade_twoprime_interval.py (Theorem 1bk) met",
     chain_ok("cascade_twoprime_interval.py"))

# ---------------------------------------------------------------- g9
import paper_needles
ok, _miss = paper_needles.verify(PAPER_NEEDLES)
for _d_, _n in _miss:
    print(f"  g9 MISSING (count {_n}): {_d_.get('s')!r}", flush=True)
gate("g9 the 1bl paper needles and the footer census (declared surface)", ok)

# ---------------------------------------------------------------- g10
odd109 = PT.get("odd:1.09", {}); even10 = PT.get("even:1", {})
ok = bool(odd109) and bool(even10) and odd109.get("certified") and even10.get("certified")
ok &= ST[("one", "odd")]["final"] <= odd109["rho"][1]*(1 + 1e-3)
ok &= ST[("one", "even")]["final"] <= even10["rho"][1]*(1 + 1e-3)
gate("g10 monotonicity consistency: the mechanism's one-prime bounds at 1.09375 do not "
     "exceed the Temple instrument's enclosed rho at 1.09 (odd) and 1.0 (even), the "
     "Temple checkpoint loaded at its current key", ok)

print(("\nALL GATES PASS (11/11)" if not fails else
       f"\nFAILURES: {fails}"), flush=True)
sys.exit(1 if fails else 0)
