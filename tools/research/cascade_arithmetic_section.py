#!/usr/bin/env python3
"""
THEOREM 1aq -- the arithmetic section: the half-shift lattice's
distinguished status among Weil test-function cones.

THE COMMISSION.  The owner asked: check whether the half-shift
lattice w = d+1/2 has any distinguished status among Weil
test-function cones -- and commissioned the landing.  Result: YES on
the arithmetic side, NO on the positivity side.  Under the
critical-line coordinate w = s - 1/2 the lattice is exactly the
integer ladder s = d+1 in {2, 3, ...}: one fact, seen independently
on all four sides of the explicit formula.  The lattice is the
unique arithmetic-rational section of a positivity-generic cone
family, and the two-sidedness locates the R4 wall.

THE CONTENT (four integralities, each an iff at alpha = 1/2 among
unit-spaced translates w = d + alpha, plus the alpha-free
coordinate fact A4; a genericity counter-theorem; the wall
reframe).  ROUND-175 SWEEP (the landing's hostile round; 1 MAJOR +
3 minors + 1 cosmetic, all verified by the lead and swept): F1
MAJOR -- the landing's umbrella "five integralities, each an iff"
quantified falsely over A4, whose evenness is an identity for
EVERY s (the kernel's two terms exchange) -- struck at the
carrier, the iff scoped to A1/A2/A3/A5 with the
all-real-translates upgrade gated (the P3 discriminant is the
perfect square (2m^2+2m+1)^2); F2 -- seven sibling gate labels
and two docstring remnants still carried 66/1ap, synced (the
weil_route label's census VALUE was missed in that pass -- its
label wraps differently -- completed round 176 F2, the class's
ninth recurrence); F3 --
"maximal exactly-computable slice ... in closed form" struck (no
ordering named; -zeta'/zeta(d+1) has no closed form), re-scoped
to the exactly-structured slice with the rational/integer-argument
split stated; F4 -- g3's tautological isinstance conjunct removed
(a gate that cannot fail), the integrality stated as arithmetic;
F5 (cosmetic) -- g9's "full committed suite" label corrected to
the actual Weil-arc chain.  ROUND-176 SWEEP (the convergence
test; 0 majors + 3 minors + 3 cosmetics, all verified by the lead
and swept): F1 -- the paper's honest-scope carrier still said
"five integralities" (the struck umbrella's count), synced; F2 --
the weil_route label above; F3 -- the wall reframe's two-case
evaluation split read as exhaustive while the archimedean leg
(psi closed forms, A5's ladder) is neither exact-rational nor a
zeta-argument -- the third leg added; cosmetics: the negative
root's off-lattice exclusion stated ([-1/6, 0) vs w >= 1 -- the
round-176 open interval and 3/2 floor corrected round 177 F2), the
irrational-powers clause scoped to rational translates, and
"DEFINES w = s-1/2" weakened to defines-up-to-scale (the evenness
pins the center; the unit scale is the integralities').
ROUND-177 SWEEP (the convergence test; 0 majors + 3 minors + 3
cosmetics, all verified by the lead and swept): F1 -- the
three-leg split was STILL not exhaustive (the strip-boundary
crossing heights gamma_b are algebraic irrationals -- the
observer pair's gamma_b^2 is the root of an exact-rational
cubic, lead-verified; the gamma/gamma^2 apposition in this note's
first form corrected round 178 F2 -- fitting no leg); the fourth
leg added and gated;
F2 -- the round-176 exclusion clause's two numbers were both
false (the root equals -1/6 EXACTLY at m = 1, so the interval is
[-1/6, 0); the translate floor is w >= 1, not 3/2 -- the
committed lattice's own floor misattributed to every translate);
corrected on both carriers; F3 -- this docstring's WALL REFRAME
paragraph still carried the two-leg split its own sweep note said
was replaced (the class's tenth recurrence), synced; cosmetics:
the honest-scope coordinate-fact mention, the g8/V5 needle-census
enumerations, and g9's ambiguous "the two Weil-arc siblings"
(three Weil-titled siblings exist; the chained pair is now named,
with 1ai's verifier noted as chained by no suite script).
ROUND-178 SWEEP (the convergence test; 0 majors + 2 minors + 1
cosmetic, all verified by the lead and swept): F1 -- the
four-leg split failed exhaustiveness a THIRD consecutive round
(ln pi in every committed p(d) = -1/2 ln pi + 1/2 psi((d+1)/2);
W(h*)'s ln pi content is exactly -ln pi/11, lead-verified); the
Gamma_R leg extended AND the claim's form changed: the leg list
is now declared A CENSUS, NOT A COMPLETENESS THEOREM -- the
recurrence mechanism retired the way the 1ap question slot was;
F2 -- the gamma_b/gamma_b^2 conflation (0.4806 is a root of the
QUARTIC 4g^4+103g^2-24, not of the cubic -- the cubic's root is
its square; minimal polynomial lead-verified in sympy); both
carriers corrected; F3 (cosmetic) -- g9's chain enumeration
gains precedence_vacuity (chained via type_counting g2).
  A1 (prime side): the Weil pairing of e^(-w|x|) is
      sum Lambda(n) n^(-(w+1/2)) = -zeta'/zeta(w+1/2); on the
      lattice the argument is the INTEGER d+1 and every Euler term
      is ln p/(p^(d+1)-1), integer denominators.  The bridge
      identity carries this silently (s = d+1).
  A2 (pole term): 2w/(w^2-1/4) = 1/d + 1/(d+1) -- unit fractions,
      exactly; integer-w values (16/15-type) are consecutive-unit-
      fraction sums for NO integer (odd vs even reduced
      denominators).
  A3 (displaced curve): (gamma+i/2)^2 + w^2 =
      (gamma - i d)(gamma + i(d+1)) -- kernel poles at INTEGER
      heights, iff w in Z+1/2; algebraically w^2 - 1/4 = d(d+1),
      exact over the committed range [1, 217].  The source of the
      (s, s-1) telescoping and the 2s-1 = 2w normalization.
  A4 (functional equation -- the coordinate fact, alpha-free,
      round 175 F1): s <-> 1-s acts as w <-> -w exactly in the
      half-shift coordinate; R1's cosh((beta-1/2)t) symmetrization
      is this evenness; K_s(beta+i gamma) = K_s(1-beta+i gamma)
      identically IN s -- the frame in which A1/A2/A3/A5 become
      integralities, not itself a translate iff.
  A5 (archimedean): the Gamma-term argument 1/4 + w/2 = (d+1)/2 --
      the psi closed-form ladder (integers and half-integers;
      -gamma_E + H_n and -gamma_E - 2 ln 2 + 2 sum 1/(2k-1));
      1/4 + w/2 in (1/2)Z iff alpha = 1/2 mod 1.
  GENERICITY (the counter-theorem): R2's cone geometry -- the
      on-line closed form L(gamma), the edge ratio -w1/w2, the
      strip-boundary sign F(0) < 0 -- holds VERBATIM at non-lattice
      weights (1.7, 2.9) and (2.13, 5.41).  The half-shift buys no
      positivity advantage; the 1/4 in F(0) is the strip
      boundary's, fixed by zeta, not by the lattice.
  THE WALL REFRAME (re-scoped round 175 F3; legs completed
      rounds 176-177).  The lattice is the exactly-structured
      slice of the Weil framework -- unique among unit-spaced
      translates, gated -- on which every committed quantity
      evaluates unconditionally, in the types so far cataloged:
      exact rationals; integer zeta-arguments (the prime side; no
      closed form is claimed); the Gamma_R/psi closed forms
      (A5's ladder PLUS the -1/2 ln pi normalization constant in
      every committed p(d), round 178 F1); and algebraic roots of
      exact-rational polynomials (the gamma_b heights -- gamma_b
      itself a root of the quartic 4g^4+103g^2-24, its square the
      cubic's root, the apposition corrected round 178 F2).  THE
      LEG LIST IS A CENSUS, NOT A COMPLETENESS THEOREM (rounds
      176-178 each found a type beyond the then-current list; no
      further exhaustiveness is asserted) -- why the arc's exact
      rationals
      (9/11, 1/297, 1/243, the bridge's unit fractions) had to
      appear -- and R4's wall is the same fact from the other side:
      the rational section is where positivity is classical
      bookkeeping; beyond its reach (the dense class) is RH.

HONEST SCOPE.  Category (a) -- classical explicit-formula
bookkeeping, exact arithmetic, psi/Gamma special values; no data,
no closures, no new physics.  The four integralities and the
coordinate fact are individually classical background; the theorem is the IDENTIFICATION (the
committed lattice is that unique section, iff at alpha = 1/2) and
the two-sidedness.  The 1/2-critical/integer-dimension
decomposition is consistency texture under Check 8, not forcing;
no RH leverage in either direction.  Check 7 clean
(explicit-formula bookkeeping; no semiclassics); Check 8 clean (no
hypothesis input).

VERIFICATION (10 gates, exit-gated).
  V1 -- g1 A2 in exact rationals (d = 1..6: 2w/(w^2-1/4) =
       1/d + 1/(d+1)) PLUS the integer-w counter-gate (w = 2..7:
       no consecutive-unit-fraction representation, m-scan);
       g2 A3 exact: w^2 - 1/4 = d(d+1) as Fractions over the FULL
       committed range d in [1, 217], plus the complex
       factorization at samples to machine precision.
  V2 -- g3 A1: the sieved Lambda-sum sum_{n<=1e5} Lambda(n)n^(-s)
       vs mpmath -zeta'/zeta(s) at s = 2, 3, 4, within the
       integral tail bound (ln N + 1/(s-1)) N^(1-s)/(s-1) (the
       Euler-denominator integrality stated as arithmetic, not
       gated -- round 175 F4);
       g4 A5: psi((d+1)/2) against BOTH closed-form families
       (d = 1..6), residuals < 1e-25 at dps 30.
  V3 -- g5 A4: K_s(beta+i gamma) = K_s(1-beta+i gamma) at samples
       (machine precision) + the paper's R1 transform sentence
       anchored (the cosh((beta-1/2)t) symmetrization);
       g6 the genericity counter-theorem: at (1.7, 2.9) and
       (2.13, 5.41), L rebuilt from kernels matches the closed
       form < 1e-12, min L >= 0 on the grid, F(0) < 0 matching its
       closed form.
  V4 -- g7 the iff scan over the FOUR integralities: predicates
       P1 (w+1/2 integer), P2 (w-1/2 integer), P3 (pole term a
       consecutive-unit-fraction sum), P4 (1/4+w/2 in (1/2)Z) --
       ALL true at alpha = 1/2 (d = 1..5), ALL false at every
       alpha in {0, 1/4, 1/3, 3/4} (d = 1..5); PLUS the
       all-real-translates upgrade (the P3 discriminant a perfect
       square, roots exactly m+1/2 and -1/(2(2m+1)), exact
       rationals, m = 1..6 -- round 175 F1 sweep).
  V5 -- g8 1aq's key sentences anchored by content (the unique
       arithmetic-rational section; NO positivity advantage; the
       two round-175 strike frames; the scoped four-iff sentence
       + the coordinate fact; the exactly-structured slice WITH
       the leg census (Gamma_R/psi closed forms incl. -1/2 ln pi;
       algebraic roots incl. the gamma_b quartic; the
       census-not-theorem sentence -- rounds 176-178); one
       fact/four sides; the Check 8 texture clause; no RH
       leverage); g9 the sibling chain green
       (cascade_concentration_regrade.py 12/0, transitively
       chaining the Weil-arc sibling chain -- the "full suite"
       label corrected round 175 F5); g10 the footer census (this
       script backticked >= 2; "89 scripts cited in place";
       "Theorems 1i-1bm").

Sabotage record (full-tree scratchpad copy, tar --exclude=.git,
serial, per-mangle restore from pristine copies, abort-safe; clean
baselines 10/0 exit 0 around every entry; actual censuses): (a)
the paper's section-identification needle mangled ("cone family"
-> "cone bundle", whitespace-aware) -> g8 trips ALONE, 9/1, exit 1
-- the first attempt aborted safely at a wrong count guess (the
lead asserted 2 where the needle appears once; the abort guard
left the tree clean at 10/0, disclosed); (b) the pole-term
identity decoupled in the verifier copy (Fr(1, d+1) ->
Fr(1, d+2)) -> g1 trips ALONE, 9/1, exit 1; (c) the genericity
closed form decoupled in the verifier copy (w2^2 - 0.25 ->
w2^2 - 0.35 in F0c) -> g6 trips ALONE, 9/1, exit 1.  At the
round-175 sweep: (d) the all-real-translates discriminant
conjunct decoupled in the verifier copy ((2m^2+2m+1)^2 ->
(2m^2+2m+2)^2) -> g7 trips ALONE, 9/1, exit 1; (e) the paper's
coordinate-fact needle mangled ("not a translate iff" -> "not a
translate law", whitespace-aware) -> g8 trips ALONE, 9/1, exit 1;
clean baselines 10/0 around both, serial fresh tree, per-mangle
restore, gate identity in the first pass.  At the round-176
sweep: (f) the third-leg needle mangled in the paper copy
("archimedean" -> "arithmetic", whitespace-aware) -> g8 trips
ALONE, 9/1, exit 1; clean baselines 10/0 around it.  At the
round-177 sweep: (g) the fourth-leg needle mangled in the paper
copy ("exact-rational polynomials" -> "exact-integer
polynomials", whitespace-aware) -> g8 trips ALONE, 9/1, exit 1;
clean baselines 10/0 around it.  At the round-178 sweep: (h) the
census-not-theorem needle mangled in the paper copy ("NOT A
COMPLETENESS THEOREM" -> "NOW A ...", whitespace-aware) -> g8
trips ALONE, 9/1, exit 1; clean baselines 10/0 around it.  Also
disclosed from the sweep itself: the paper restructure broke two
pre-existing g8 needles and the first clean run FAILED 9/1 at g8
-- the gate catching its own needle lag before commit (the
needles re-synced to the current text and verified); and one
scripted edit wrote a syntactically-broken placeholder before
its post-write ast.parse caught it (repaired in the next write;
the write-then-parse order is the residual exposure of the
per-edit pattern).  Ten gates (count checked against the gate()
census pre-commit).
"""
import os
import subprocess
import sys
from fractions import Fraction as Fr

import numpy as np

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())



# declared paper surface (round-264 F264-1: chain
# scripts in tower members' reaches mirror their
# inline paper conjuncts here; run_tower's harvest
# meta-gate verifies this declaration COVERS every
# inline compare, so drift fails the precheck)
import paper_needles
PAPER_NEEDLES = [
    {'s': '89 scripts cited in place', 'form': 'plain', 'min': 1},
    {'s': "PLUS the −½ln π of Γ_ℝ's normalization", 'form': 'plain', 'min': 1},
    {'s': 'THE LEG LIST IS A CENSUS, NOT A COMPLETENESS THEOREM', 'form': 'plain', 'min': 1},
    {'s': 'Theorem 1aq', 'form': 'plain', 'min': 1},
    {'s': 'Theorems 1i–1bn', 'form': 'plain', 'min': 1},
    {'s': '`cascade_arithmetic_section.py`', 'form': 'plain', 'min': 2},
    {'s': 'algebraic roots of exact-rational polynomials where it is a crossing', 'form': 'plain', 'min': 1},
    {'s': 'buys NO positivity advantage', 'form': 'plain', 'min': 1},
    {'s': 'consistency texture under Check 8, not forcing', 'form': 'plain', 'min': 1},
    {'s': 'cosh((β−½)t)', 'form': 'plain', 'min': 1},
    {'s': 'each of A1, A2, A3, and A5 below is true for α = ½', 'form': 'plain', 'min': 1},
    {'s': 'no RH leverage is claimed in either direction', 'form': 'plain', 'min': 1},
    {'s': 'one fact, seen independently on all four sides of the explicit formula', 'form': 'plain', 'min': 1},
    {'s': 'quartic 4γ⁴ + 103γ² − 24, its minimal polynomial', 'form': 'plain', 'min': 1},
    {'s': 'struck round 175 F1, MAJOR', 'form': 'plain', 'min': 1, 'max': 1},
    {'s': 'struck round 175 F3', 'form': 'plain', 'min': 1, 'max': 1},
    {'s': 'the coordinate fact, not a translate iff', 'form': 'plain', 'min': 1},
    {'s': 'the exactly-structured slice of the Weil framework', 'form': 'plain', 'min': 1},
    {'s': 'the unique arithmetic-rational section of a positivity-generic cone family', 'form': 'plain', 'min': 1},
    {'s': 'the Γ_ℝ/ψ closed forms where it is archimedean', 'form': 'plain', 'min': 1},
    {'s': 'unique among unit-spaced translates, gated', 'form': 'plain', 'min': 1},
]


def unit_fraction_pair(q):
    """Is q = 1/m + 1/(m+1) for some positive integer m?"""
    for m in range(1, 2000):
        if Fr(1, m) + Fr(1, m + 1) == q:
            return True
        if Fr(1, m) + Fr(1, m + 1) < q:
            return False
    return False


print("V1 -- A2/A3: the pole term and the displaced-curve factorization, exact")
ok = True
for d in range(1, 7):
    w = Fr(2 * d + 1, 2)
    ok &= 2 * w / (w * w - Fr(1, 4)) == Fr(1, d) + Fr(1, d + 1)
counter = []
for wi in range(2, 8):                    # integer-w lattice counter-gate
    q = 2 * Fr(wi) / (Fr(wi) ** 2 - Fr(1, 4))
    counter.append(unit_fraction_pair(q))
ok &= not any(counter)
gate("g1 A2: 2w/(w^2-1/4) = 1/d + 1/(d+1) exactly (d = 1..6, rationals) "
     "AND integer-w values are consecutive-unit-fraction sums for no m "
     "(w = 2..7 counter-gated)", ok,
     f"counter {counter}")

ok = True
for d in range(1, 218):                   # the full committed range
    ok &= Fr(2 * d + 1, 2) ** 2 - Fr(1, 4) == d * (d + 1)
for d in (1, 4, 12):                      # complex factorization at samples
    w = d + 0.5
    for g in (0.7, 14.134725):
        lhs = (g + 0.5j) ** 2 + w * w
        rhs = (g - 1j * d) * (g + 1j * (d + 1))
        ok &= abs(lhs - rhs) < 1e-12
gate("g2 A3: w^2 - 1/4 = d(d+1) exact over d in [1, 217] (Fractions); "
     "(gamma+i/2)^2 + w^2 = (gamma-id)(gamma+i(d+1)) at samples", ok)

print("V2 -- A1/A5: the prime side at integer arguments; the psi ladder")
from mpmath import mp, mpf, zeta, diff, digamma, euler, log as mplog

mp.dps = 30
N = 100000
lam = np.zeros(N + 1)
spf = np.zeros(N + 1, dtype=np.int64)
for p in range(2, N + 1):
    if spf[p] == 0:
        spf[p::p] = np.where(spf[p::p] == 0, p, spf[p::p])
for n in range(2, N + 1):
    p = spf[n]
    m = n
    while m % p == 0:
        m //= p
    if m == 1:
        lam[n] = np.log(p)
ok = True
details = []
for s in (2, 3, 4):
    direct = sum(lam[n] * mpf(n) ** (-s) for n in range(2, N + 1))
    target = -diff(zeta, mpf(s)) / zeta(mpf(s))
    tail = (mplog(N) + mpf(1) / (s - 1)) * mpf(N) ** (1 - s) / (s - 1)
    ok &= abs(direct - target) < tail
    details.append(f"s={s}: |diff| {float(abs(direct-target)):.2e} < tail {float(tail):.2e}")
gate("g3 A1: the sieved Lambda-sum equals -zeta'/zeta at the INTEGER "
     "arguments s = d+1 = 2, 3, 4 within the integral tail bound (the "
     "Euler-denominator integrality is arithmetic, stated not gated -- "
     "the round-175 F4 tautology removed)", ok,
     "; ".join(details))

ok = True
for d in range(1, 7):
    arg = mpf(d + 1) / 2
    psi_val = digamma(arg)
    if (d + 1) % 2 == 0:
        n = (d + 1) // 2
        closed = -euler + sum(mpf(1) / k for k in range(1, n))
    else:
        n = d // 2 + 1
        closed = -euler - 2 * mplog(2) + 2 * sum(mpf(1) / (2 * k - 1) for k in range(1, n))
    ok &= abs(psi_val - closed) < mpf("1e-25")
gate("g4 A5: psi((d+1)/2) matches BOTH closed-form families (d = 1..6; "
     "-gamma_E + H_n on integers, -gamma_E - 2ln2 + 2*sum on "
     "half-integers) at dps 30", ok)

print("V3 -- A4 and the genericity counter-theorem")


def K(s, b, g):
    return (s - b) / ((s - b) ** 2 + g ** 2) + (s - 1 + b) / ((s - 1 + b) ** 2 + g ** 2)


ok = True
for d in (1, 4, 12):
    s = d + 1
    for b in (0.0, 0.3):
        for g in (0.7, 14.134725):
            ok &= abs(K(s, b, g) - K(s, 1 - b, g)) < 1e-14
ok &= paper_needles.needle(PAPER_NEEDLES, 'cosh((β−½)t)', 'plain')
gate("g5 A4: K_s(beta+i gamma) = K_s(1-beta+i gamma) at samples (the "
     "FE involution as w-evenness; an identity for EVERY s -- the "
     "coordinate fact, not a translate iff, round 175 F1) + R1's "
     "cosh((beta-1/2)t) transform sentence anchored", ok)

ok = True
for (w1, w2) in ((1.7, 2.9), (2.13, 5.41)):
    s1, s2 = w1 + 0.5, w2 + 0.5
    gs = np.linspace(0.01, 50, 1500)
    L = np.array([K(s2, 0.5, g) - (w1 / w2) * K(s1, 0.5, g) for g in gs])
    closed = 2 * gs ** 2 * (w2 ** 2 - w1 ** 2) / (w2 * (w1 ** 2 + gs ** 2) * (w2 ** 2 + gs ** 2))
    ok &= float(np.max(np.abs(L - closed))) < 1e-12
    ok &= float(np.min(L)) >= -1e-15
    F0 = K(s2, 0.0, 0.0) - (w1 / w2) * K(s1, 0.0, 0.0)
    F0c = -(w2 ** 2 - w1 ** 2) / (2 * w2 * (w2 ** 2 - 0.25) * (w1 ** 2 - 0.25))
    ok &= abs(F0 - F0c) < 1e-12 and F0 < 0
gate("g6 genericity: R2's on-line closed form, edge ratio, and "
     "strip-boundary sign hold verbatim at the NON-lattice pairs "
     "(1.7, 2.9) and (2.13, 5.41) -- the positivity geometry is "
     "lattice-independent", ok)

print("V4 -- the iff scan over translates")


def predicates(d, alpha):
    w = Fr(d) + alpha
    p1 = (w + Fr(1, 2)).denominator == 1
    p2 = (w - Fr(1, 2)).denominator == 1
    p3 = unit_fraction_pair(2 * w / (w * w - Fr(1, 4)))
    p4 = (Fr(1, 4) + w / 2) % Fr(1, 2) == 0
    return (p1, p2, p3, p4)


ok = True
for d in range(1, 6):
    ok &= predicates(d, Fr(1, 2)) == (True, True, True, True)
    for alpha in (Fr(0), Fr(1, 4), Fr(1, 3), Fr(3, 4)):
        ok &= predicates(d, alpha) == (False, False, False, False)
# round 175 F1 sweep: the iffs hold over ALL real translates -- the
# P3 quadratic (2m+1)w^2 - 2m(m+1)w - (2m+1)/4 = 0 has discriminant
# 4m^2(m+1)^2 + (2m+1)^2 = (2m^2+2m+1)^2, a perfect square, so its
# roots are exactly w = m+1/2 and w = -1/(2(2m+1)).
for m in range(1, 7):
    disc = 4 * Fr(m) ** 2 * Fr(m + 1) ** 2 + Fr(2 * m + 1) ** 2
    ok &= disc == Fr(2 * m * m + 2 * m + 1) ** 2
    root_p = (Fr(2 * m * (m + 1)) + Fr(2 * m * m + 2 * m + 1)) / (2 * (2 * m + 1))
    root_m = (Fr(2 * m * (m + 1)) - Fr(2 * m * m + 2 * m + 1)) / (2 * (2 * m + 1))
    ok &= root_p == Fr(2 * m + 1, 2) and root_m == -Fr(1, 2 * (2 * m + 1))
gate("g7 the iff over the FOUR integralities A1/A2/A3/A5 (A4 is the "
     "alpha-free coordinate fact, round 175 F1): all four predicates "
     "true at alpha = 1/2 (d = 1..5), all false at alpha in "
     "{0, 1/4, 1/3, 3/4}; AND the all-real-translates upgrade -- the "
     "P3 discriminant is the perfect square (2m^2+2m+1)^2 with roots "
     "exactly m+1/2 and -1/(2(2m+1)) (m = 1..6, exact rationals)", ok)

print("V5 -- anchors, chain, census")
ok = paper_needles.needle(PAPER_NEEDLES, 'the unique arithmetic-rational section of a positivity-generic cone family', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'buys NO positivity advantage', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'struck round 175 F1, MAJOR', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'struck round 175 F3', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'each of A1, A2, A3, and A5 below is true for α = ½', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the coordinate fact, not a translate iff', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the exactly-structured slice of the Weil framework', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'the Γ_ℝ/ψ closed forms where it is archimedean', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'algebraic roots of exact-rational polynomials where it is a crossing', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, "PLUS the −½ln π of Γ_ℝ's normalization", 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'THE LEG LIST IS A CENSUS, NOT A COMPLETENESS THEOREM', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'quartic 4γ⁴ + 103γ² − 24, its minimal polynomial', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'unique among unit-spaced translates, gated', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'one fact, seen independently on all four sides of the explicit formula', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'consistency texture under Check 8, not forcing', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'no RH leverage is claimed in either direction', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'Theorem 1aq', 'plain')
gate("g8 1aq's key sentences anchored by content (the section "
     "identification; no positivity advantage; the two round-175 "
     "strike frames; the scoped four-iff sentence + the coordinate "
     "fact; the exactly-structured slice with the leg CENSUS "
     "(four legs + the census-not-theorem sentence, rounds "
     "176-178); one fact/four sides; the "
     "Check 8 texture clause; no RH leverage)", ok)

r = subprocess.run(
    [sys.executable,
     os.path.join(ROOT, "tools", "research", "cascade_concentration_regrade.py")],
    capture_output=True, text=True, timeout=3600)
ok = r.returncode == 0 and "12 pass / 0 fail" in r.stdout
gate("g9 the sibling chain green (cascade_concentration_regrade.py "
     "12/0, transitively chaining: unit_ball_rh, windows_overlap, "
     "riemann_selection, type_counting, precedence_vacuity (via "
     "type_counting g2 -- round 178 F3), quarter_square, and "
     "weil_route_traveled -- the chained pair named round 177 F6; "
     "1ai's weil_positivity_status is chained by no suite script; "
     "the 'full committed suite' label corrected round 175 F5)", ok)

ok = paper_needles.needle(PAPER_NEEDLES, '`cascade_arithmetic_section.py`', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, '89 scripts cited in place', 'plain')
ok &= paper_needles.needle(PAPER_NEEDLES, 'Theorems 1i–1bn', 'plain')
gate("g10 the footer census (this script backticked in body and "
     "footer; \"89 scripts cited in place\"; \"Theorems 1i-1bm\")", ok)

n_fail = sum(1 for x in results if not x)
print(f"RESULT: {len(results) - n_fail} pass / {n_fail} fail ({len(results)} gates)")
print("READING.  The half-shift lattice is the arithmetic-rational")
print("section of the Weil cone family: prime side at integer zeta")
print("arguments, pole term in unit fractions, kernel poles at integer")
print("heights, psi closed-form ladder -- the FOUR integralities, each")
print("an iff at alpha = 1/2 (over all real translates, gated) -- with")
print("the FE evenness the alpha-free coordinate fact (round 175 F1);")
print("the cone's positivity geometry is lattice-independent (gated at")
print("non-lattice weights).")
print("The section is the exactly-structured slice, unique among")
print("unit-spaced translates (re-scoped round 175 F3); R4's wall")
print("is the same fact from the other side.  No data, no closures,")
print("no RH leverage in either direction.")
sys.exit(0 if n_fail == 0 else 1)
