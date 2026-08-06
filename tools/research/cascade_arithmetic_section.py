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

THE CONTENT (five integralities, each an iff at alpha = 1/2 among
unit-spaced translates w = d + alpha; a genericity counter-theorem;
the wall reframe).
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
  A4 (functional equation): s <-> 1-s acts as w <-> -w exactly in
      the half-shift coordinate; R1's cosh((beta-1/2)t)
      symmetrization is this evenness; K_s(beta+i gamma) =
      K_s(1-beta+i gamma) identically.
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
  THE WALL REFRAME.  The lattice is the maximal exactly-computable
      slice of the Weil framework -- why the arc's exact rationals
      (9/11, 1/297, 1/243, the bridge's unit fractions) had to
      appear -- and R4's wall is the same fact from the other side:
      the rational section is where positivity is classical
      bookkeeping; beyond its reach (the dense class) is RH.

HONEST SCOPE.  Category (a) -- classical explicit-formula
bookkeeping, exact arithmetic, psi/Gamma special values; no data,
no closures, no new physics.  The integralities are individually
classical background; the theorem is the IDENTIFICATION (the
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
       integral tail bound (ln N + 1/(s-1)) N^(1-s)/(s-1);
       g4 A5: psi((d+1)/2) against BOTH closed-form families
       (d = 1..6), residuals < 1e-25 at dps 30.
  V3 -- g5 A4: K_s(beta+i gamma) = K_s(1-beta+i gamma) at samples
       (machine precision) + the paper's R1 transform sentence
       anchored (the cosh((beta-1/2)t) symmetrization);
       g6 the genericity counter-theorem: at (1.7, 2.9) and
       (2.13, 5.41), L rebuilt from kernels matches the closed
       form < 1e-12, min L >= 0 on the grid, F(0) < 0 matching its
       closed form.
  V4 -- g7 the iff scan: predicates P1 (w+1/2 integer), P2
       (w-1/2 integer), P3 (pole term a consecutive-unit-fraction
       sum), P4 (1/4+w/2 in (1/2)Z) -- ALL true at alpha = 1/2
       (d = 1..5), ALL false at every alpha in {0, 1/4, 1/3, 3/4}
       (d = 1..5).
  V5 -- g8 1aq's key sentences anchored by content (the unique
       arithmetic-rational section; NO positivity advantage; the
       maximal exactly-computable slice; one fact/four sides; iff
       at alpha = 1/2; the Check 8 texture clause; no RH
       leverage); g9 the sibling chain green
       (cascade_concentration_regrade.py 12/0, transitively
       chaining the full suite); g10 the footer census (this
       script backticked >= 2; "67 scripts cited in place";
       "Theorems 1i-1aq").

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
w2^2 - 0.35 in F0c) -> g6 trips ALONE, 9/1, exit 1.  Ten gates
(count checked against the gate() census pre-commit).
"""
import os
import subprocess
import sys
from fractions import Fraction as Fr

import numpy as np

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")


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
ok &= all(isinstance(2 ** (d + 1), int) for d in range(1, 7))
gate("g3 A1: the sieved Lambda-sum equals -zeta'/zeta at the INTEGER "
     "arguments s = d+1 = 2, 3, 4 within the integral tail bound; the "
     "Euler denominators p^(d+1)-1 are integers", ok,
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
ok &= "cosh((β−½)t)" in paper
gate("g5 A4: K_s(beta+i gamma) = K_s(1-beta+i gamma) at samples (the "
     "FE involution as w-evenness) + R1's cosh((beta-1/2)t) transform "
     "sentence anchored", ok)

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
gate("g7 the iff: all four integrality predicates true at alpha = 1/2 "
     "(d = 1..5), all false at alpha in {0, 1/4, 1/3, 3/4}", ok)

print("V5 -- anchors, chain, census")
ok = "the unique arithmetic-rational section of a positivity-generic cone family" in paper
ok &= "buys NO positivity advantage" in paper
ok &= "the maximal exactly-computable slice of the Weil framework" in paper
ok &= "one fact, seen independently on all four sides of the explicit formula" in paper
ok &= "true for α = ½ and false for every other translate mod 1" in paper
ok &= "consistency texture under Check 8, not forcing" in paper
ok &= "no RH leverage is claimed in either direction" in paper
ok &= paper.count("Theorem 1aq") >= 1
gate("g8 1aq's key sentences anchored by content (the section "
     "identification; no positivity advantage; the computable slice; "
     "one fact/four sides; the iff; the Check 8 texture clause; no RH "
     "leverage)", ok)

r = subprocess.run(
    [sys.executable,
     os.path.join(ROOT, "tools", "research", "cascade_concentration_regrade.py")],
    capture_output=True, text=True, timeout=3600)
ok = r.returncode == 0 and "12 pass / 0 fail" in r.stdout
gate("g9 the sibling chain green (cascade_concentration_regrade.py "
     "12/0, transitively chaining the full committed suite)", ok)

ok = paper.count("`cascade_arithmetic_section.py`") >= 2
ok &= "67 scripts cited in place" in paper
ok &= "Theorems 1i–1aq" in paper
gate("g10 the footer census (this script backticked in body and "
     "footer; \"67 scripts cited in place\"; \"Theorems 1i-1aq\")", ok)

n_fail = sum(1 for x in results if not x)
print(f"RESULT: {len(results) - n_fail} pass / {n_fail} fail ({len(results)} gates)")
print("READING.  The half-shift lattice is the arithmetic-rational")
print("section of the Weil cone family: prime side at integer zeta")
print("arguments, pole term in unit fractions, kernel poles at integer")
print("heights, FE involution as evenness, psi closed-form ladder --")
print("each an iff at alpha = 1/2 -- while the cone's positivity")
print("geometry is lattice-independent (gated at non-lattice weights).")
print("The section is the maximal exactly-computable slice; R4's wall")
print("is the same fact from the other side.  No data, no closures,")
print("no RH leverage in either direction.")
sys.exit(0 if n_fail == 0 else 1)
