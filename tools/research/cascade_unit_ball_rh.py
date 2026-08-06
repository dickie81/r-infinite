#!/usr/bin/env python3
"""
THEOREM 1ao -- the infinite unit ball RH theorem: the Li criterion
at the tower's edge.

THE COMMISSION.  The owner: "Investigate an infinite unit ball RH
theorem."  Result: the classical Li criterion stated and gated in
the committed unit-ball decomposition at the tower's singular edge
d = 0 -- a resolution-free RH-equivalent the committed objects can
EXPRESS; no proof leverage claimed; the wall stands.

THE DECOMPOSITION (exact).  xi = B * A with B(s) = (1/2) s Gamma_R(s)
the unit-ball (Archimedean) factor and A(s) = (s-1) zeta(s) the
pole-removed arithmetic factor, both analytic and nonzero at s = 1.
The ball factor's log-derivative is the committed potential plus
the prefactor's pole ladder: d/ds ln B(s) = p(s-1) + 1/s exactly.  Li's ladder
lambda_n = (1/(n-1)!) (d^n/ds^n)[s^(n-1) ln xi(s)] at s = 1 splits
exactly by linearity: lambda_n = lambda_n^B + lambda_n^A -- the ball
rungs are the committed potential's derivative ladder at the edge
d = 0 (closed series form through psi^(k)(1/2), ln pi, and the
prefactor's elementary 1/s ladder), the
arithmetic rungs come from zeta's Stieltjes expansion.  First-rung
identities, exact: lambda_1^A = EulerGamma and lambda_1^B = 1 + p(0)
= 1 - (1/2)ln pi - gamma/2 - ln 2, so lambda_1 = 1 + p(0) + gamma.

THE CRITERION (classical, cited).  RH <=> lambda_n >= 0 for all
n >= 1 (Li; the Bombieri-Lagarias complement) -- a COUNTABLE
positivity ladder requiring no test-function concentration: it
sidesteps 1an's resolution wall entirely (the wall bounds the
committed Lorentzian cone; Li's family is not in it) [net-state,
Theorem 1ap: the wall's width coordinate is struck -- the cone
concentrates at height -- so the sidestep rests solely on the
decay-rate exclusion, untouched].

THE CROSSOVER (the honest structure -- the landing's own draft said
"the ball dominates at every rung", wrong at the low rungs and
corrected before landing): the ball rungs are NEGATIVE for n = 1..7
exactly (minimum -1.01305... at n = 3), positive and growing from
n = 8; the arithmetic rungs stay positive and bounded on the
computed range (their minimum there is the first rung, gamma; the
dip near n = 24 bottoms at 0.5944 > gamma) -- positivity is
arithmetic-carried at the low rungs; the ball's drag ends at
n = 8 (its rungs turn positive) and its share of the rung passes
half near n = 11 (round 164 F3: the landing's "ball-carried from
n = 8" was over-definite -- the ball's share at 8 is 1.4%).

THE TEETH (counterfactual, labeled).  An off-line quadruple at
beta = 0.95, gamma = 2 -- a region classically zero-free; the
injection is pure instrument-teeth -- drives the perturbed ladder
negative by n = 13 (minimum ~ -84 within n <= 50) while the true
ladder's minimum on the range is lambda_1 = 0.0230957... > 0.

ROUND-164 SWEEP (the landing's hostile round; 0 majors, 4 minors
+ 2 cosmetics, all statement-discipline, verified by the lead and
swept): F1 -- the paper's tie residual was an unscoped dps-80
drafting-run numeric (struck; the committed 7.8e-62 quoted).
F2 -- the wall-sidestep membership clause was ungated; the
decay-rate separation is now argued in the paper and the lattice
floor 3/2 > 1/2 gated in g1.  F3 -- "ball-carried from n = 8" was
over-definite (the ball's share at 8 is 1.4%, crossing half near
11); reworded on all three tellings, the old sabotage-(a) needle
surviving only at the landing tree.  F4 -- the three routes'
committed scopes stated (series 1..50; direct 1..8; zeros sampled
{1,3,5,10}).  F5/F6 (cosmetic) -- the pole-ladder term named; the
half-axis referents named.

HONEST SCOPE.  Category (a) -- no data, no closures, no new
physics.  The criterion is classical; new for the program is only
the edge-ladder expression, the exact ball/arithmetic split with
the committed-potential tie, and the gating.  NO PROOF LEVERAGE:
proving lambda_n >= 0 for all n is as hard as RH; nothing
cascade-side forces it; internal consistency in Check 8's sense,
never forcing; claimed in neither direction.  Check 7 clean (Gamma/
psi series arithmetic, the Stieltjes expansion, classical zero
data; no semiclassics); Check 8 clean (no hypothesis input).

VERIFICATION (13 gates, exit-gated).
  V1 -- g1 the tie d/ds ln B = p(s-1) + 1/s (five samples,
       < 1e-50) plus the rate-floor conjunct 3/2 > 1/2 in exact
       rationals (round 164 F2); g2 the series ladder reproduces the classical
       values (lambda_1..lambda_4 bracketed at 10 digits; lambda_50
       bracketed); g3 route agreement (direct high-precision
       differentiation of ln xi to n = 8 vs the series route,
       < 1e-25); g4 the zero route (200 paired true zeros, sampled
       n: the deficit positive and matching the paired-tail model
       n^2 sum_{gamma>T} gamma^-2 within (0.9, 1.1)x -- the first
       draft's first-order model failed its own clean run 12/1,
       the binomial second-order term being same-order in the
       tail; redesigned pre-commit, disclosed).
  V2 -- g5 the first-rung identities exact (lambda_1^A = gamma;
       lambda_1^B = 1 + p(0) = 1 - ln pi/2 - gamma/2 - ln 2;
       each < 1e-50); g6 the crossover (ball negative exactly
       n = 1..7, minimum at n = 3 bracketed, increasing on 8..50;
       arithmetic positive throughout with argmin at n = 1 and the
       n = 24 dip bracketed above gamma); g7 the teeth (first
       perturbed-negative index exactly 13; perturbed minimum
       < -80; the true argmin at n = 1); g8 positivity
       lambda_n > 0 for all n = 1..50.
  V3 -- g9 1ao's key sentences anchored by content; g10 the
       honest-scope anchors (NO PROOF LEVERAGE; as-hard-as-RH;
       claimed-in-neither-direction count >= 2; the counterfactual
       teeth label); g11 the classical-inputs additions in the
       footer (Li and Bombieri-Lagarias; Stieltjes); g12 the
       sibling chain green (windows_overlap 13/0, transitively
       chaining riemann_selection, type_counting, and the two
       Weil-arc siblings); g13 the footer census (this script
       backticked; "68 scripts cited in place"; "Theorems
       1i-1ar" -- the census advances with each landing).

Sabotage record (full-tree scratchpad copy, tar --exclude=.git,
serial, abort-on-mangle-failure, at the landing; three disclosed
mishaps, per-entry actual censuses): (a) the paper's crossover
sentence mangled mid-anchor ("hand positivity to each other across
n ~ 8" -> "n ~ 9"; the FIRST attempt aborted at its count assert --
the phrase wraps a line break, the recurring single-line-pattern
class -- redone newline-aware) -> g9 trips, 12/1, exit 1
[round-164 F3 replaced this sentence: entry (a) reproduces at the
LANDING tree 3936ede; the reworded sentence's trip is probe (d)
below]; (b) the
teeth quadruple flipped ON-line in the copy (beta 0.95 -> 0.5, the
growth factor collapsing to 1): the FIRST run CRASHED at the bare
next() (StopIteration -- an on-line quadruple has no negative rung)
instead of tripping the gate -- a robustness defect in the
instrument itself, fixed in place (default None) and disclosed;
redone -> g7 trips, 12/1, exit 1; (c) the ball series' ln pi term
dropped in the copy (the k == 1 subtraction) -> SIX gates trip --
g2, g3, g4, g5, g6, g7 (the corrupted ladder breaks the values,
both cross-routes, the first-rung identity, the crossover, and the
teeth indices), 7/6, exit 1 -- the drafted census "g2+g5+g6,
10/3" undercounted and is corrected to the actual run, per the
record-actuals rule.  At the round-164 sweep (serial, fresh tree,
abort-safe): (d) the REWORDED handoff sentence mangled mid-anchor
("two marks" -> "three marks") -> g9 trips, 12/1, exit 1; (e) the
rate-floor lattice decoupled in the copy (range(1, 218) ->
range(0, 218), the floor collapsing to 1/2) -> g1 trips (detail
"floor 1/2"), 12/1, exit 1.  At the round-165 sweep (serial,
fresh tree): (f) rung 10 corrupted x1.01 in the copy (the
round-165 reviewer's prepared probe, run by the lead) -> g4 trips
ALONE (the zero route's ~1% cross-check on the sampled rung
biting; ratio pushed to ~1.108 > 1.1), 12/1, exit 1 -- the
corrected route-scope clause's quantitative claim demonstrated.
Clean baselines 13/0 exit 0 before
and after every entry.  Thirteen gates (count checked against the
gate() census pre-commit).
"""
import os
import subprocess
import sys

from mpmath import (mp, mpf, mpc, log, pi as mppi, gamma as mpgamma, zeta,
                    zetazero, taylor, stieltjes, polygamma, euler, binomial,
                    factorial, digamma)

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")

mp.dps = 60
N = 50
results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


def B(s):
    return mpf("0.5") * s * mppi ** (-s / 2) * mpgamma(s / 2)


def A(s):
    if s == 1:
        return mpf(1)
    return (s - 1) * zeta(s)


def p(d):
    return -log(mppi) / 2 + digamma((mpf(d) + 1) / 2) / 2


print("V1 -- the decomposition, the ladder, and the routes")
worst = mpf(0)
for sv in ("2.0", "3.7", "7.25", "20.0", "218.6"):
    s = mpf(sv)
    worst = max(worst, abs(mp.diff(lambda t: log(B(t)), s) - (p(s - 1) + 1 / s)))
# round 164 F2: the wall-sidestep clause's membership exclusion is
# now argued via the decay-rate separation -- the lattice floor
# min_{d>=1}(d + 1/2) = 3/2 exceeds the Li members' 1/2 scale --
# gated here in exact rationals.
from fractions import Fraction as Fr
floor = min(d + Fr(1, 2) for d in range(1, 218))
ok = worst < mpf("1e-50")
ok &= floor == Fr(3, 2) and floor > Fr(1, 2)
gate("g1 the tie: d/ds ln B(s) = p(s-1) + 1/s at five samples (the "
     "ball factor's log-derivative = the committed potential + the "
     "prefactor's pole ladder); AND the decay-rate floor over the "
     "lattice = 3/2 > 1/2, the Li scale (round 164 F2)",
     ok, f"worst {float(worst):.1e}, floor {floor}")

# the series route: ln A from the Stieltjes expansion, ln B from
# polygamma at 1/2; composed through s = 1/(1-z); lambda_n = n c_n.
c = [mpf(1)] + [(-1) ** (k - 1) * stieltjes(k - 1) / factorial(k - 1)
                for k in range(1, N + 1)]
lnA = [mpf(0)] * (N + 1)
for n in range(1, N + 1):
    t = c[n]
    for k in range(1, n):
        t -= mpf(k) / n * lnA[k] * c[n - k]
    lnA[n] = t
lnB = [log(mpf(1) / 2)] + [mpf(0)] * N
for k in range(1, N + 1):
    t = mpf(-1) ** (k + 1) / k
    if k == 1:
        t -= log(mppi) / 2
    t += polygamma(k - 1, mpf(1) / 2) / (2 ** k * factorial(k))
    lnB[k] = t


def compose(a):
    out = [a[0]] + [mpf(0)] * N
    for j in range(1, N + 1):
        out[j] = sum(a[k] * binomial(j - 1, k - 1) for k in range(1, j + 1))
    return out


lamB = [n * compose(lnB)[n] for n in range(1, N + 1)]
lamA = [n * compose(lnA)[n] for n in range(1, N + 1)]
lam = [lamB[i] + lamA[i] for i in range(N)]
ok = mpf("0.02309570896") < lam[0] < mpf("0.02309570897")
ok &= mpf("0.0923457352") < lam[1] < mpf("0.0923457353")
ok &= mpf("0.2076389205") < lam[2] < mpf("0.2076389206")
ok &= mpf("0.3687904794") < lam[3] < mpf("0.3687904795")
ok &= mpf("43.5310") < lam[49] < mpf("43.5312")
gate("g2 the series ladder (Stieltjes + polygamma, composed through "
     "s = 1/(1-z)) reproduces the classical values: lambda_1..4 at "
     "10 digits, lambda_50 bracketed (the series route's own value; "
     "rungs 9 and 11..50 single-route, n = 10 cross-checked at the "
     "zero-sum's ~1% level -- scoped round 164 F4, corrected round "
     "165 F1)",
     ok, f"l1={mp.nstr(lam[0], 10)} l50={mp.nstr(lam[49], 8)}")

with mp.workdps(40):
    co = taylor(lambda z: log(B(1 / (1 - z)) * A(1 / (1 - z))), 0, 9)
    direct = [n * co[n] for n in range(1, 9)]
worst = max(abs(direct[i] - lam[i]) for i in range(8))
gate("g3 route agreement: direct high-precision differentiation of "
     "ln xi (n = 1..8) vs the series route",
     worst < mpf("1e-25"), f"worst {float(worst):.1e}")

M = 200
with mp.workdps(30):
    zs = [zetazero(k) for k in range(1, M + 1)]
    T = float(zs[-1].imag)
import math
# The tail model is n^2 * sum_{gamma>T} gamma^-2, NOT first-order in
# n: per zero pair 1-(1-1/rho)^n expands to [n + n(n-1)]/gamma^2 =
# n^2/gamma^2 -- the binomial second-order term is same-order in the
# gamma-tail.  The landing's first g4 modeled the tail at first
# order and FAILED its own clean run (12/1); redesigned pre-commit,
# disclosed.  Observed ratio deficit/(n^2 t1) = 0.998 uniformly.
tail1 = (math.log(T / (2 * math.pi)) + 1) / (2 * math.pi * T)
ok = True
for n in (1, 3, 5, 10):
    zsum = sum(2 * (1 - (1 - 1 / rho) ** n).real for rho in zs)
    d = lam[n - 1] - zsum
    ok &= 0.9 * n * n * tail1 < d < 1.1 * n * n * tail1
gate("g4 the zero route: 200 paired true zeros, sampled n in "
     "{1, 3, 5, 10} -- the deficit positive (convergence from "
     "below) and MATCHING the paired-tail model n^2 * "
     "sum_{gamma>T} gamma^-2 within (0.9, 1.1)x (the first draft's "
     "first-order model failed its own clean run; redesigned "
     "pre-commit, disclosed)", ok)

print("V2 -- the first rungs, the crossover, the teeth, positivity")
ok = abs(lamA[0] - euler) < mpf("1e-50")
ok &= abs(lamB[0] - (1 + p(0))) < mpf("1e-50")
ok &= abs(lamB[0] - (1 - log(mppi) / 2 - euler / 2 - log(2))) < mpf("1e-50")
gate("g5 the first-rung identities EXACT: lambda_1^A = EulerGamma; "
     "lambda_1^B = 1 + p(0) = 1 - ln(pi)/2 - gamma/2 - ln 2 -- the "
     "first Li rung is the committed edge potential plus one plus "
     "gamma", ok)

negs = [i + 1 for i, x in enumerate(lamB) if x < 0]
mnB = min(range(N), key=lambda i: lamB[i])
mnA = min(range(N), key=lambda i: lamA[i])
ok = negs == list(range(1, 8))
ok &= mnB == 2 and mpf("-1.0131") < lamB[2] < mpf("-1.0130")
ok &= all(lamB[i + 1] > lamB[i] for i in range(7, N - 1))
ok &= all(x > 0 for x in lamA)
ok &= mnA == 0
ok &= mpf("0.594") < lamA[23] < mpf("0.595") and lamA[23] > euler
gate("g6 the crossover: ball rungs negative EXACTLY n = 1..7 (min at "
     "n = 3, bracketed), increasing from 8; arithmetic rungs "
     "positive with argmin at n = 1 (gamma) and the n = 24 dip "
     "above gamma",
     ok, f"ball min {float(lamB[2]):.6f}, arith dip {float(lamA[23]):.6f}")

rho = mpc("0.95", "2")
w, v = 1 - 1 / rho, 1 - 1 / (1 - rho)
pert = [lam[n - 1] + 2 * (1 - w ** n).real + 2 * (1 - v ** n).real
        for n in range(1, N + 1)]
# default None (not a bare next()): an on-line quadruple has NO
# negative rung, and the first sabotage-(b) run CRASHED here on
# StopIteration instead of tripping the gate -- a robustness defect,
# fixed in place and disclosed; None now fails the gate gracefully.
first_neg = next((n for n in range(1, N + 1) if pert[n - 1] < 0), None)
ok = first_neg == 13
ok &= min(pert) < -80
ok &= min(range(N), key=lambda i: lam[i]) == 0
gate("g7 the teeth (counterfactual off-line quadruple beta = 0.95, "
     "gamma = 2, a classically zero-free region): perturbed ladder "
     "first negative at n = 13, minimum < -80; the true ladder's "
     "minimum is lambda_1 at n = 1",
     ok, f"first neg {first_neg}, min {float(min(pert)):.2f}")

gate("g8 positivity: lambda_n > 0 for every n = 1..50 (the "
     "criterion's computed depth)", all(x > 0 for x in lam))

print("V3 -- the paper: key sentences, scope, classical inputs, siblings, footer")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = ("the first Li rung is the committed edge potential plus one "
      "plus γ" in paper)
ok &= "it sidesteps 1an's resolution wall entirely" in paper
# round 164 F3: the handoff sentence reworded (the old needle "hand
# positivity to each other across n ≈ 8" now lives only at the
# landing tree; sabotage (a) reproduces there, the new wording's
# trip is probe (d)).  F2: the rate-separation sentence anchored.
# F1/F3 strike frames counted.
ok &= ("the drag's end at n = 8 and the share crossing near n = 11 "
       "are the two marks of the handoff" in paper)
ok &= "rates 3/2 versus ½" in paper
ok &= paper.count("struck round 164 F1") == 1
ok &= paper.count("struck round 164 F3") == 1
ok &= "wrong at the low rungs and corrected before landing" in paper
gate("g9 1ao's key sentences anchored by content (the first-rung "
     "identity; the wall sidestep; the REWORDED handoff + the "
     "rate-separation sentence + the two strike frames -- round "
     "164; the corrected-draft disclosure)", ok,
     f"164 frames {paper.count('struck round 164 F1')}+"
     f"{paper.count('struck round 164 F3')}")

ok = "NO PROOF LEVERAGE" in paper
ok &= "as hard as RH" in paper
ok &= paper.count("claimed in neither direction") >= 2
ok &= ("a region classically zero-free; the injection is pure "
       "instrument-teeth" in paper)
gate("g10 the honest-scope anchors: no-proof-leverage; as-hard-as-RH; "
     "neither-direction (count >= 2, it also lives in 1aj); the "
     "counterfactual teeth label",
     ok, f"neither-direction count {paper.count('claimed in neither direction')}")

# "positivity ladder", NOT the bigram "positivity"+"criterion"
# (adjacent): that two-word phrase is a census term of the 1ai
# prior-pursuit gate (cascade_weil_positivity_status.py V1), and the
# landing's first footer wording collided with it -- caught by the
# battery (31/32); a first repair then wrote the bigram into THIS
# comment and failed the census again (repo-wide 1) -- both reworded,
# the census kept strong rather than allowlisted.
ok = "Li and Bombieri–Lagarias, the positivity ladder" in paper
ok &= "Stieltjes, the Laurent constants of ζ" in paper
gate("g11 the classical-inputs additions anchored in the footer list "
     "(Li; Bombieri–Lagarias; Stieltjes; the census-safe wording, "
     "disclosed)", ok)

rr = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_windows_overlap.py")],
                    capture_output=True, text=True)
ok = rr.returncode == 0 and "13 pass / 0 fail" in rr.stdout
gate("g12 the sibling chain green after the census advance "
     "(windows_overlap 13/0, transitively chaining "
     "riemann_selection, type_counting, and the two Weil-arc "
     "siblings)", ok)

ok = "`cascade_unit_ball_rh.py`" in paper
ok &= "68 scripts cited in place" in paper
ok &= "Theorems 1i–1ar" in paper
gate("g13 the footer census (advanced at this landing, disclosed): "
     "this script backticked; 68 cited in place; the range 1i–1ar "
     "(advance disclosed; label re-synced round 175 F2)", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (13 gates)")
print("READING: the infinite unit ball RH theorem -- the Li criterion")
print("at the tower's edge.  The committed decomposition xi = B * A")
print("(ball x arithmetic) splits Li's ladder exactly; the ball")
print("factor's log-derivative = the committed potential + the")
print("prefactor's pole ladder (d/ds ln B")
print("= p(s-1) + 1/s), so the ball rungs are the potential's")
print("derivative ladder at the edge d = 0.  First rungs exact:")
print("lambda_1^A = gamma, lambda_1^B = 1 + p(0).  RH <=> every rung")
print(">= 0 (Li; Bombieri-Lagarias -- classical, cited): a COUNTABLE")
print("criterion needing no concentration, sidestepping 1an's")
print("resolution wall via the decay-rate exclusion (Li's family is")
print("not in the committed cone; net-state 1ap: the wall's width")
print("coordinate is struck, the exclusion stands on rates alone).")
print("The crossover: ball rungs negative exactly n = 1..7, positive")
print("and growing from 8; arithmetic rungs positive and bounded --")
print("positivity is arithmetic-carried early; the ball's drag ends")
print("at n = 8 and its share of the rung passes half near n = 11")
print("(round 164 F3; the landing's draft said 'the ball dominates")
print("at every rung' -- wrong at the low rungs, corrected before")
print("landing).  The Li family sits outside the committed cone by")
print("decay-rate separation: the lattice floor 3/2 vs the Li scale")
print("1/2 (round 164 F2, gated).")
print("The teeth: a counterfactual off-line quadruple (beta 0.95,")
print("gamma 2 -- classically zero-free region, pure")
print("instrument-teeth) drives the ladder negative by n = 13.  NO")
print("PROOF LEVERAGE: positivity for all n is as hard as RH;")
print("nothing cascade-side forces it; the wall stands; internal")
print("consistency only, claimed in neither direction.  No data, no")
print("closures, no new physics.")
sys.exit(0 if n_fail == 0 else 1)
