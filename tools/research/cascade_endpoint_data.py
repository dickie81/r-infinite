#!/usr/bin/env python3
"""Theorem 1z verifier: the endpoint data attacked.

Claim under test: member two's live content -- the site-E closure
windows' endpoint data (Definition-6.1 instantiation plus the
strict-boundary stipulation, part4b) -- is menu-bounded with ZERO
free numbers: every committed window endpoint is a forced-menu layer
(Bott generation set {5,13,21}; Adams gauge set {12,13,14}; Part-0
critical set), and over the non-sink distinguished menu M = {5, 7,
12, 13, 14, 19, 21} every in-menu alternative selection is
data-excluded while the committed selection sits within observation.
The strict-boundary stipulation makes exactly two binary decisions,
both alternatives excluded. Check-8 discipline: the selections are
C1 instantiation; uniqueness-within-menu is corroboration
(cross-check), not forcing; NO closure is claimed -- member two
persists, sharpened.

Gates:
  Z1 -- the committed closures recomputed from the primitives alone
        (Gamma/digamma; no imports from other verifiers): tau/mu =
        16.81731 (+0.28 sigma of 16.8170 +- 0.0011); mu/e = 206.7707
        (+0.0012% of 206.7683); alpha_s = 0.117917 (+0.09 sigma of
        0.1180 +- 0.0009).
  Z2 -- menu membership: all six committed endpoints in M; the
        part4b menu sentences anchored verbatim ("not chosen from a
        menu; they are the complete set of non-sink distinguished
        layers").
  Z3 -- the exclusion census, 21 ordered pairs per window: the
        committed pair is the minimum-deviation selection in all
        three windows; runner-ups gated at their computed values
        (tau/mu: (7,13) at 524 sigma; mu/e: 33%; alpha_s: (12,14)
        at 3.15 sigma -- the census's weakest exclusion, gated
        exactly, with all other alpha_s alternatives >= 18 sigma).
  Z4 -- the stipulation priced: tau/mu without the U(1) shift at
        -261 sigma; mu/e with it at +1.74% (~1,400x the committed
        residual). Both binary alternatives excluded.
  Z5 -- surface anchors, verbatim: part4b's strict-boundary sentence
        ("begins at the U(1) layer and does not receive the shift");
        1l(ii)'s endpoint-data sentence; 1z's key sentences (zero
        free numbers; corroboration-not-forcing; no closure); the
        two net-state markers (1l(ii); 1y(iii)'s member-two line).

Data consumed (disclosed): 16.8170 +- 0.0011, 206.7683, 0.1180 +-
0.0009 -- for the exclusion census only, the cross-check class
1l(ii)'s re-grade licenses. No number changes; no new prediction.
Sabotage record (run on scratchpad copies at the landing commit):
(a) perturbing the committed tau/mu computation to window (7,13)
flips Z1, exit 1 (Z3's census recomputes independently and still
finds (5,13) minimal -- it gates the census, not the Z1 recital);
(b) deleting the 1l(ii) marker flips Z5, exit 1.
"""
import math
import os
import sys

from scipy.special import digamma

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
PART4B = os.path.join(ROOT, "src", "cascade-series-part4b.tex")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


SQRTPI = math.sqrt(math.pi)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(math.pi)


def Phi(a, b):
    return sum(p(d) for d in range(a, b + 1))


A_EM = 1 / 137.028  # the record's cascade-derived value (part4b Tier-2 (k))
RAD = 1 + A_EM / (2 * math.pi) + A_EM * alpha(21)  # the mu/e radiative slot
A_GUT = (SQRTPI * R(12)) ** 2 / (4 * math.pi)

OBS_TM, SIG_TM = 16.8170, 0.0011
OBS_ME = 206.7683
OBS_AS, SIG_AS = 0.1180, 0.0009


def tau_mu(a, b):
    return math.exp(Phi(a + 1, b) + alpha(14) / 2) * 2 * SQRTPI


def mu_e(a, b):
    return math.exp(Phi(a + 1, b)) * 2 * SQRTPI * RAD


def alpha_s(a, b):
    return A_GUT * math.exp(Phi(a, b) + alpha(14) / 2)


print("Z1 -- the committed closures from the primitives")
tm = tau_mu(5, 13)
me = mu_e(13, 21)
als = alpha_s(5, 12)
gate("tau/mu = 16.81731, +0.28 sigma", abs(tm - 16.81731) < 5e-5
     and abs((tm - OBS_TM) / SIG_TM - 0.28) < 0.05, f"{tm:.5f}")
gate("mu/e = 206.7707, +0.0012%", abs(me - 206.7707) < 5e-4
     and abs((me - OBS_ME) / OBS_ME * 100 - 0.0012) < 3e-4, f"{me:.4f}")
gate("alpha_s = 0.117917, +0.09 sigma", abs(als - 0.117917) < 5e-6
     and abs((als - OBS_AS) / SIG_AS) < 0.15, f"{als:.6f}")

print("Z2 -- menu membership + the part4b menu anchors")
M = [5, 7, 12, 13, 14, 19, 21]
endpoints = [5, 13, 13, 21, 5, 12]
gate("all six committed endpoints in the non-sink distinguished menu",
     all(e in M for e in endpoints), f"endpoints {endpoints} in {M}")
part4b = open(PART4B, encoding="utf-8").read()


def norm(s):
    return " ".join(s.split())


ok2 = "The cascade has five structurally distinguished layers" in norm(part4b)
ok2 &= ("not chosen from a menu; they are the complete set of non-sink "
        "distinguished layers in the cascade" in norm(part4b))
gate("part4b menu sentences anchored verbatim", ok2)

print("Z3 -- the exclusion census (21 pairs per window)")


def census(f, obs, scale):
    rows = []
    for i, a in enumerate(M):
        for b in M[i + 1:]:
            rows.append((abs(f(a, b) - obs) / scale, a, b, f(a, b)))
    rows.sort()
    return rows


c_tm = census(tau_mu, OBS_TM, SIG_TM)
gate("tau/mu: committed (5,13) is the census minimum; runner-up (7,13) at 524 sigma",
     c_tm[0][1:3] == (5, 13) and c_tm[1][1:3] == (7, 13)
     and abs(c_tm[1][0] - 524.2) < 1.0,
     f"min ({c_tm[0][1]},{c_tm[0][2]}) {c_tm[0][0]:.2f}s; next "
     f"({c_tm[1][1]},{c_tm[1][2]}) {c_tm[1][0]:.1f}s")
c_me = census(mu_e, OBS_ME, OBS_ME)  # relative deviation
gate("mu/e: committed (13,21) is the minimum; runner-up at 33%",
     c_me[0][1:3] == (13, 21) and abs(c_me[1][0] * 100 - 33.0) < 0.5,
     f"min ({c_me[0][1]},{c_me[0][2]}) {c_me[0][0]*100:.4f}%; next "
     f"({c_me[1][1]},{c_me[1][2]}) {c_me[1][0]*100:.1f}%")
c_as = census(alpha_s, OBS_AS, SIG_AS)
third = c_as[2][0]
gate("alpha_s: committed (5,12) minimum; runner-up (12,14) at 3.15 sigma "
     "(weakest exclusion, exact); all others >= 18 sigma",
     c_as[0][1:3] == (5, 12) and c_as[1][1:3] == (12, 14)
     and abs(c_as[1][0] - 3.15) < 0.05 and third >= 18,
     f"min ({c_as[0][1]},{c_as[0][2]}) {c_as[0][0]:.2f}s; next "
     f"({c_as[1][1]},{c_as[1][2]}) {c_as[1][0]:.2f}s; third {third:.1f}s")

print("Z4 -- the stipulation priced (two binary decisions)")
tm_noshift = math.exp(Phi(6, 13)) * 2 * SQRTPI
me_shift = math.exp(Phi(14, 21) + alpha(14) / 2) * 2 * SQRTPI * RAD
s1 = (tm_noshift - OBS_TM) / SIG_TM
r2 = (me_shift - OBS_ME) / OBS_ME * 100
gate("tau/mu without the U(1) shift: -261 sigma", abs(s1 + 260.9) < 1.0,
     f"{tm_noshift:.4f}, {s1:.1f} sigma")
gate("mu/e with the U(1) shift: +1.74% (~1,400x the committed residual)",
     abs(r2 - 1.739) < 0.01 and r2 / 0.0012 > 1000,
     f"{me_shift:.4f}, {r2:.3f}%")

print("Z5 -- surface anchors (verbatim, failable)")
paper = open(PAPER, encoding="utf-8").read()
np_ = norm(paper)
ok5 = ("begins at the $\\mathrm{U}(1)$ layer and does not receive the shift"
       in norm(part4b))
gate("part4b: the strict-boundary sentence anchored", ok5)
ok6 = "the closure windows' **endpoint data** — Definition-6.1 instantiation" in np_
ok6 &= "menu-bounded with zero free\nnumbers".replace("\n", " ") in np_.replace("**", "")
ok6 &= "corroboration, not\nforcing".replace("\n", " ") in np_.replace("**", "")
ok6 &= "no closure is claimed" in np_.replace("**", "")
gate("paper: 1l's endpoint sentence + 1z's key sentences anchored", ok6)
ok7 = np_.count("Net-state, Theorem 1z round 109") >= 1
ok7 &= "net-state, Theorem 1z round\n109: sharpened".replace("\n", " ") in np_
gate("the two 1z net-state markers anchored (1l(ii); 1y(iii))", ok7)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (13 gates)")
print("READING: the endpoint data is menu-bounded -- zero free numbers;")
print("the committed selections are unique within observation over the")
print("non-sink distinguished menu (weakest exclusion 3.15 sigma, alpha_s")
print("(12,14), reported exactly); the stipulation's two binary")
print("alternatives are excluded at -261 sigma and +1.74%. The selections")
print("are C1 instantiation; uniqueness is corroboration, not forcing;")
print("member two persists, sharpened. No closure; no number changes.")
sys.exit(0 if n_fail == 0 else 1)
