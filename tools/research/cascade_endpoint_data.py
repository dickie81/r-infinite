#!/usr/bin/env python3
"""Theorem 1z verifier: the endpoint data attacked (round-109 swept).

Claim under test: member two's live content -- the site-E closure
windows' endpoint data -- carries ZERO free numbers: the two lepton
windows are host-pair paths (path-start-exclusive) with all four
endpoints in forced menus (Bott {5,13,21}; Adams {12,13,14}); the
alpha_s window is the committed descent Phi(12->4) = sum_{d=5..12}
p(d), upper terminus 12 menu-anchored, lower terminus the OBSERVER
DIMENSION d = 4 -- C1-anchored, not a menu layer (round-109 F1
corrected the first draft's "every endpoint is a forced-menu layer",
which rested on an undisclosed per-window convention switch). Over
the union menu M = {5,7,12,13,14,19,21} (this paper's construction
-- part4b's non-sink set {5,7,14,19} UNION the two part4a sets;
round-109 F6 corrected the draft's misappropriation of part4b's
term) every in-menu alternative is data-excluded, endpoint-only
ceteris paribus (round-109 F8). The strict-boundary rule governs
THREE attachment instances (round-109 F2 corrected "exactly two"):
tau/mu receives, alpha_s receives, mu/e does not; all three
alternatives excluded, the weakest -- alpha_s unshifted -- at
-2.22 sigma, the weakest exclusion in the entire analysis. Check-8
discipline: the selections are C1 instantiation; uniqueness is
corroboration, not forcing; NO closure claimed.

Gates:
  Z1 -- the committed closures recomputed from the primitives, gated
        at half-ULP of the quoted digits (round-109 F10): tau/mu =
        16.81731 (+0.28 sigma of 16.8170 +- 0.0011); mu/e = 206.7707
        (+0.0012% of 206.7683; part4b's -0.0012% is the same number
        under its obs-vs-pred definition); alpha_s = 0.117917
        (+0.019 sigma of the COMMITTED 0.1179 +- 0.0009 -- round-109
        F3/F4 corrected the draft's "+0.09 sigma" wrong sign and its
        uncommitted 0.1180 observation).
  Z2 -- the committed addressing read from committed surfaces
        (round-109 F7: the first gate compared hardcoded lists and
        could not fail against the record): the window strings
        anchored in cascade_leptons.py (Phi(6, 13); Phi(14, 21);
        Phi(5, 12)) and part4b (Delta Phi(5 -> 13); d=14..21; the
        Phi(12 -> 4) descent display); the lepton host-pair
        endpoints {5,13}, {13,21} in the menus; the descent's upper
        terminus 12 in the Adams set; part4b's menu sentences
        verbatim.
  Z3 -- the exclusion census, 21 unordered pairs per window
        (round-109 F11), endpoint-only ceteris paribus: committed
        selections minimal; runner-ups gated (tau/mu (7,13) 524
        sigma; mu/e 33%; alpha_s (12,14) 3.26 sigma under the
        committed observation, all others >= 18 sigma).
  Z4 -- the three attachment instances priced: tau/mu unshifted
        -261 sigma; alpha_s unshifted -2.22 sigma (the analysis's
        weakest exclusion, gated as such); mu/e shifted +1.74%
        (~1,400x the committed residual).
  Z5 -- surface anchors, verbatim: part4b's strict-boundary
        sentence; 1l(ii)'s endpoint sentence; 1z's round-109 key
        sentences (the observer-dimension terminus; three attachment
        instances; endpoint-only ceteris paribus; the union menu;
        corroboration-not-forcing; no closure); the four net-state
        markers (1l(ii), 1l(iv) x2, 1y(iii)).

Data consumed (disclosed): 16.8170 +- 0.0011, 206.7683, 0.1179 +-
0.0009 (the committed values) -- for the census only. No number
changes; no new prediction. Sabotage record: at the round-109 sweep,
(a) flipping the committed tau/mu computation to window (7,13) trips
Z1, exit 1 (Z3's census recomputes independently); (b) deleting the
1l(ii) marker trips Z5, exit 1; (c) corrupting the cascade_leptons
window anchor trips Z2, exit 1.
"""
import math
import os
import sys

from scipy.special import digamma

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
PART4B = os.path.join(ROOT, "src", "cascade-series-part4b.tex")
LEPTONS = os.path.join(ROOT, "tools", "research", "cascade_leptons.py")

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
OBS_AS, SIG_AS = 0.1179, 0.0009  # the committed observation (round-109 F4)


def tau_mu(a, b):
    return math.exp(Phi(a + 1, b) + alpha(14) / 2) * 2 * SQRTPI


def mu_e(a, b):
    return math.exp(Phi(a + 1, b)) * 2 * SQRTPI * RAD


def alpha_s(a, b):
    # the committed descent Phi(b -> a-1) = sum_{d=a..b} p(d)
    return A_GUT * math.exp(Phi(a, b) + alpha(14) / 2)


print("Z1 -- the committed closures (half-ULP recitals, round-109 F10)")
tm = tau_mu(5, 13)
me = mu_e(13, 21)
als = alpha_s(5, 12)
gate("tau/mu = 16.81731, +0.28 sigma", abs(tm - 16.81731) < 5e-6
     and abs((tm - OBS_TM) / SIG_TM - 0.28) < 0.05, f"{tm:.7f}")
gate("mu/e = 206.7707, +0.0012% (pred-vs-obs signing)",
     abs(me - 206.7707) < 5e-5
     and abs((me - OBS_ME) / OBS_ME * 100 - 0.0012) < 3e-4, f"{me:.6f}")
gate("alpha_s = 0.117917, +0.019 sigma of the committed 0.1179 (F3/F4)",
     abs(als - 0.117917) < 5e-7
     and abs((als - OBS_AS) / SIG_AS - 0.019) < 0.005, f"{als:.8f}")

print("Z2 -- committed addressing read from committed surfaces (round-109 F7)")
leptons_src = open(LEPTONS, encoding="utf-8").read()
part4b = open(PART4B, encoding="utf-8").read()


def norm(s):
    return " ".join(s.split())


ok_win = ("Phi(6, 13)" in leptons_src and "Phi(14, 21)" in leptons_src
          and "Phi(5, 12)" in leptons_src)
gate("cascade_leptons.py carries the three committed window sums", ok_win)
ok_4b = "\\Delta\\Phi(5\\to 13)" in part4b and "d=14..21" in part4b
ok_4b &= "\\Phi(12\\to4)" in part4b.replace(" ", "") or "\\Phi(12 \\to 4)" in part4b
gate("part4b carries the two path labels + the Phi(12->4) descent display", ok_4b)
BOTT, ADAMS = {5, 13, 21}, {12, 13, 14}
gate("lepton host pairs {5,13},{13,21} in the Bott set; descent upper terminus "
     "12 in the Adams set; lower terminus 4 in NO menu (C1-anchored)",
     {5, 13} <= BOTT and {13, 21} <= BOTT and 12 in ADAMS
     and 4 not in BOTT | ADAMS | {5, 7, 14, 19})
ok2 = "The cascade has five structurally distinguished layers" in norm(part4b)
ok2 &= ("not chosen from a menu; they are the complete set of non-sink "
        "distinguished layers in the cascade" in norm(part4b))
gate("part4b menu sentences anchored verbatim", ok2)

print("Z3 -- the exclusion census (21 unordered pairs per window)")
M = [5, 7, 12, 13, 14, 19, 21]


def census(f, obs, scale):
    rows = []
    for i, a in enumerate(M):
        for b in M[i + 1:]:
            rows.append((abs(f(a, b) - obs) / scale, a, b, f(a, b)))
    rows.sort()
    return rows


c_tm = census(tau_mu, OBS_TM, SIG_TM)
gate("tau/mu: committed (5,13) minimal; runner-up (7,13) at 524 sigma",
     c_tm[0][1:3] == (5, 13) and c_tm[1][1:3] == (7, 13)
     and abs(c_tm[1][0] - 524.2) < 1.0,
     f"min ({c_tm[0][1]},{c_tm[0][2]}) {c_tm[0][0]:.2f}s; next {c_tm[1][0]:.1f}s")
c_me = census(mu_e, OBS_ME, OBS_ME)
gate("mu/e: committed (13,21) minimal; runner-up at 33%",
     c_me[0][1:3] == (13, 21) and abs(c_me[1][0] * 100 - 33.0) < 0.5,
     f"min ({c_me[0][1]},{c_me[0][2]}) {c_me[0][0]*100:.4f}%; next {c_me[1][0]*100:.1f}%")
c_as = census(alpha_s, OBS_AS, SIG_AS)
gate("alpha_s: committed (5,12) minimal at +0.019s; runner-up (12,14) at 3.26 "
     "sigma (endpoint census's weakest, exact); all others >= 18 sigma",
     c_as[0][1:3] == (5, 12) and c_as[1][1:3] == (12, 14)
     and abs(c_as[1][0] - 3.26) < 0.05 and c_as[2][0] >= 18,
     f"min {c_as[0][0]:.3f}s; next {c_as[1][0]:.2f}s; third {c_as[2][0]:.1f}s")

print("Z4 -- the three attachment instances priced (round-109 F2)")
tm_noshift = math.exp(Phi(6, 13)) * 2 * SQRTPI
als_noshift = A_GUT * math.exp(Phi(5, 12))
me_shift = math.exp(Phi(14, 21) + alpha(14) / 2) * 2 * SQRTPI * RAD
s1 = (tm_noshift - OBS_TM) / SIG_TM
s2 = (als_noshift - OBS_AS) / SIG_AS
r3 = (me_shift - OBS_ME) / OBS_ME * 100
gate("tau/mu unshifted: -261 sigma", abs(s1 + 260.9) < 1.0,
     f"{tm_noshift:.4f}, {s1:.1f}s")
gate("alpha_s unshifted: -2.22 sigma -- the analysis's weakest exclusion",
     abs(s2 + 2.22) < 0.05, f"{als_noshift:.6f}, {s2:.2f}s")
gate("mu/e shifted: +1.74% (~1,400x the committed residual)",
     abs(r3 - 1.739) < 0.01 and r3 / 0.0012 > 1000, f"{me_shift:.4f}, {r3:.3f}%")

print("Z5 -- surface anchors (verbatim, failable)")
paper = open(PAPER, encoding="utf-8").read()
np_ = norm(paper).replace("**", "")
ok5 = ("begins at the $\\mathrm{U}(1)$ layer and does not receive the shift"
       in norm(part4b))
gate("part4b: the strict-boundary sentence anchored", ok5)
ok6 = "the closure windows' endpoint data — Definition-6.1 instantiation" in np_
ok6 &= "the observer dimension d = 4 — C1-anchored, the hypothesis's own fixed point" in np_
ok6 &= "governs three attachment instances" in np_
ok6 &= "endpoint-only ceteris paribus" in np_
ok6 &= "the union menu M = {5, 7, 12, 13, 14, 19, 21}" in np_
ok6 &= "corroboration, not forcing" in np_
ok6 &= "no closure is claimed" in np_
gate("paper: 1z's round-109 key sentences anchored", ok6)
ok7 = np_.count("Net-state, Theorem 1z round 109") >= 1
ok7 &= "net-state, Theorem 1z round 109: sharpened" in np_
ok7 &= np_.count("net-state, Theorem 1z round 109: menu-bounded") >= 1
ok7 &= "the endpoint items sharpened — menu-bounded" in np_
gate("the four 1z net-state markers anchored (1l(ii), 1l(iv) x2, 1y(iii))", ok7)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (16 gates)")
print("READING: the endpoint data is menu-bounded except at the descent's")
print("lower terminus, which is the observer dimension d = 4 -- C1's own")
print("fixed point; zero free numbers either way. The committed selections")
print("are unique within observation; the strict-boundary rule governs")
print("three attachment instances, all alternatives excluded, the weakest")
print("(alpha_s unshifted) at -2.22 sigma. The selections are C1")
print("instantiation; uniqueness is corroboration, not forcing; member two")
print("persists, sharpened. No closure; no number changes.")
sys.exit(0 if n_fail == 0 else 1)
