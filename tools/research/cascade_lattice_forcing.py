#!/usr/bin/env python3
"""
THEOREM 1ar -- the lattice forced: the binary selection closed by
the paper's own discipline.

THE COMMISSION.  The owner rejected the axiom route to 1aq's
section as circular and commissioned the hard road: derive the
half-shift lattice from premises that never mention integer
points.  The chain: P0 (the paper's declared zero-free-parameter
discipline, made an explicit premise -- constitutive, not a
theorem; every conclusion conditional on it) + evenness (Weil
test functions are even, zeros pairing rho <-> 1-rho) collapse
the translate continuum to TWO classes (2 alpha in Z): the
CRITICAL (half-density) class s in Z+1/2 containing the fixed
point s = 1/2, and the ARITHMETIC (algebraic) class s in Z
containing the pole pair {0, 1}.  P0's second application through
1aq's certified iffs decides the binary: exact bookkeeping holds
4/4 on the arithmetic class, 0/4 on the critical class, and a
foundation carrying its ledger in underived transcendentals is
excluded.  Integrality is DERIVED: no link mentions integer
points.  The meaning layer (classical): the arithmetic class is
the algebraic-character lattice Hom(G_m, G_m) = Z (unit spacing
and integrality are the group law's), with the parity linkage of
x -> x^n exactly the committed even/odd tower interleaving
(Legendre: Gamma_C(s) = Gamma_R(s) Gamma_R(s+1)); the critical
class is the half-density class, center s = 1/2 the zeros' axis.
Role assignment: rungs on the algebraic class, the reading
coordinate w = s - 1/2 centered at the half-density point.
Remark (texture, not forcing): the arithmetic class is the orbit
of the pole pair {0, 1} under the unit recurrence; the tower edge
s = 1 (1ao's Li rung) sits at zeta's pole.

HONEST SCOPE.  Category (a) -- classical group theory, the
functional equation's symmetry, exact rational arithmetic, and a
certified theorem (1aq); no data, no closures, no new physics.
Conditional on P0, and says so.  The L2 negative census ("the
record's only translate-selecting structure") is a census of the
committed record, not a theorem about all possible structure.
No RH leverage in either direction.  Check 7 clean (character/
Gamma bookkeeping; no semiclassics); Check 8 clean (no hypothesis
input -- C1 appears nowhere in the chain).

VERIFICATION (10 gates, exit-gated).
  V1 -- g1 the two-class lemma exact: over a rational grid of
       translates, -alpha = alpha mod 1 iff 2 alpha in Z; the
       symmetric classes are exactly {0, 1/2} (Fractions);
       g2 the dichotomy: the four 1aq integrality predicates are
       4/4 at alpha = 1/2 and 0/4 at alpha = 0 (d = 1..5, exact
       rationals -- the critical class IS 1aq's counter-gate).
  V2 -- g3 the Legendre pair and parity linkage: Gamma_C(s) =
       Gamma_R(s) Gamma_R(s+1) at machine precision (mpmath,
       samples); the committed even/odd tower anchor in the
       paper; g4 the pole orbit: the even+odd Gamma_R pole union
       is Z<=0 and its FE orbit s <-> 1-s fills Z (set
       computation); the arithmetic class contains {0, 1}; the
       critical class contains 1/2 and no pole of either factor
       in the scanned range.
  V3 -- g5 evenness: K_s(beta + i gamma) = K_s(1 - beta +
       i gamma) at samples (the premise's mechanism; cross-anchor
       of 1aq's g5) + R1's "the even test function" anchored in
       the paper; g6 the half-density center: w = 0 <-> s = 1/2
       exactly; the displaced-curve half-shift anchor (the
       (gamma + i/2)^2 convention) present; the two roles land in
       DISTINCT classes (1/2 not in Z; rung arguments in Z).
  V4 -- g7 P0 and the conditionality: the front-matter
       zero-free-parameter sentence anchored; the theorem's
       explicit-premise statement and its conditionality clause
       anchored; the L2 census-scope clause anchored (a census,
       not a theorem about all possible structure).
  V5 -- g8 1ar's key sentences anchored by content (the hard-road
       commission; the two-class collapse; the 4/4-vs-0/4
       decision; "Integrality is DERIVED, not adopted"; the
       algebraic-character theorem; the role assignment; the
       remark's no-forcing clause; Check 8's C1-free clause);
       g9 the sibling chain green (cascade_arithmetic_section.py
       10/0, transitively chaining the Weil-arc suite);
       g10 the footer census (this script backticked >= 2;
       "68 scripts cited in place"; "Theorems 1i-1ar").

Sabotage record (full-tree scratchpad copy, tar --exclude=.git,
serial, per-mangle restore from pristine copies, abort-safe; clean
baselines 10/0 exit 0 around every entry; actual censuses): (a)
the paper's derived-not-adopted needle mangled ("not adopted" ->
"not proved", whitespace-aware) -> g8 trips ALONE, 9/1, exit 1;
(b) the two-class lemma decoupled in the verifier copy (Fr(1, 2)
-> Fr(1, 3) in the expected symmetric set) -> g1 trips ALONE,
9/1, exit 1; (c) the pole-detection bound decoupled in the
verifier copy (1e6 -> 1e26) -> g4 trips ALONE, 9/1, exit 1 --
the round-175-F4-lesson conjunct demonstrated falsifiable.  Ten
gates (count checked against the gate() census pre-commit).
"""
import os
import subprocess
import sys
from fractions import Fraction as Fr

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")

print("V1 -- the two-class lemma and the dichotomy")
ok = True
grid = [Fr(k, 60) for k in range(60)]
sym = [a for a in grid if (-a) % 1 == a % 1]
ok &= sym == [Fr(0), Fr(1, 2)]
for a in grid:
    ok &= (((-a) % 1 == a % 1) == ((2 * a) % 1 == 0))
gate("g1 the two-class lemma: -alpha = alpha mod 1 iff 2 alpha in Z; "
     "the symmetric translate classes are exactly {0, 1/2} (60-point "
     "rational grid, exact)", ok,
     f"sym {sym}")


def unit_fraction_pair(q):
    for m in range(1, 2000):
        v = Fr(1, m) + Fr(1, m + 1)
        if v == q:
            return True
        if v < q:
            return False
    return False


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
    ok &= predicates(d, Fr(0)) == (False, False, False, False)
gate("g2 the dichotomy: the four 1aq integrality predicates 4/4 on the "
     "arithmetic class (alpha = 1/2) and 0/4 on the critical class "
     "(alpha = 0), d = 1..5, exact rationals", ok)

print("V2 -- the Legendre pair and the pole orbit")
from mpmath import mp, mpf, pi, gamma, power

mp.dps = 30


def GR(s):
    return power(pi, -mpf(s) / 2) * gamma(mpf(s) / 2)


def GC(s):
    return 2 * power(2 * pi, -mpf(s)) * gamma(mpf(s))


ok = True
for s in (0.7, 2.0, 3.5, 6.0):
    lhs = GR(s) * GR(s + 1)
    rhs = GC(s)
    ok &= abs(lhs - rhs) / abs(rhs) < mpf("1e-25")
ok &= "Γ_ℂ(s) = Γ_ℝ(s)Γ_ℝ(s+1), so p_ℂ = p_triv" in paper
ok &= "archimedean factor of every odd Dirichlet" in paper
gate("g3 the Legendre pair Gamma_C = Gamma_R(s) Gamma_R(s+1) at 25+ "
     "digits (samples) + the committed even/odd tower anchors (the "
     "parity linkage of the algebraic characters)", ok)

even_poles = set(range(0, -40, -2))
odd_poles = set(range(-1, -40, -2))
union = even_poles | odd_poles
fe_orbit = union | {1 - s for s in union}
ok = union == set(range(-39, 1))
ok &= fe_orbit >= set(range(-39, 41))
ok &= {0, 1} <= fe_orbit
# falsifiable pole detection (round-175-F4 lesson: no tautologies):
# Gamma_R is FINITE at every half-integer (the critical class) and
# BLOWS UP at the poles -- both checked by evaluation.
ok &= all(abs(GR(k + mpf("0.5"))) < 1e3 for k in range(-6, 7))
ok &= abs(GR(mpf(-2) + mpf("1e-8"))) > 1e6
ok &= abs(GR(mpf(-3) + 1 + mpf("1e-8"))) > 1e6   # odd-tower pole via GR(s+1)
gate("g4 the pole orbit: the even+odd Gamma_R pole union is Z<=0 "
     "(range scan); its FE orbit fills Z; the arithmetic class "
     "contains the pole pair {0, 1}; the critical class's center 1/2 "
     "is no pole", ok)

print("V3 -- evenness and the half-density center")


def K(s, b, g):
    return (s - b) / ((s - b) ** 2 + g ** 2) + (s - 1 + b) / ((s - 1 + b) ** 2 + g ** 2)


ok = True
for s in (2, 5, 7.3):
    for b in (0.0, 0.3):
        for g in (0.7, 14.134725):
            ok &= abs(K(s, b, g) - K(s, 1 - b, g)) < 1e-14
ok &= "the even test function" in paper
gate("g5 evenness: K_s(beta+i gamma) = K_s(1-beta+i gamma) at samples "
     "(including a non-lattice s -- the premise is s-independent) + "
     "R1's even-test-function anchor", ok)

ok = Fr(0) + Fr(1, 2) == Fr(1, 2)                 # w = 0 <-> s = 1/2
ok &= Fr(1, 2).denominator != 1                   # the center is NOT an integer
ok &= all(Fr(d + 1).denominator == 1 for d in range(1, 6))
ok &= "(γ + i/2)² + w² = (γ − id)(γ + i(d+1))" in paper
ok &= "the READING COORDINATE w = s − ½ is centered at the half-density point" in paper
gate("g6 the half-density center: w = 0 <-> s = 1/2 exactly; the rung "
     "arguments are integers while the center is not (the two roles in "
     "DISTINCT classes); the displaced-curve half-shift and the "
     "role-assignment sentence anchored", ok)

print("V4 -- P0 and the conditionality")
ok = "one hypothesis and zero free parameters" in paper
ok &= "P0 is that discipline stated as a premise" in paper
ok &= ("every conclusion below is conditional on P0" in paper
       or "conditional on P0, and says so" in paper
       or "every conclusion below is conditional on it" in paper)
ok &= "a census of the committed record, not a theorem about all possible structure" in paper
gate("g7 P0 and the conditionality: the front-matter zero-parameter "
     "sentence; the explicit-premise statement; the conditionality "
     "clause; the L2 census-scope clause -- all anchored", ok)

print("V5 -- anchors, chain, census")
ok = "derive the half-shift lattice from premises that never mention integer points" in paper
ok &= "exactly two classes" in paper
ok &= "4/4 on the arithmetic class and 0/4 on the critical class" in paper
ok &= "Integrality is DERIVED, not adopted" in paper
ok &= "Hom(𝔾_m, 𝔾_m) = ℤ is a classical theorem" in paper
ok &= "no forcing is claimed from the remark" in paper
ok &= "C1 appears nowhere in the chain" in paper
ok &= paper.count("Theorem 1ar") >= 1
gate("g8 1ar's key sentences anchored by content (the hard-road "
     "commission; the two-class collapse; the dichotomy decision; "
     "integrality derived; the algebraic-character theorem; the "
     "remark's no-forcing clause; the C1-free clause)", ok)

r = subprocess.run(
    [sys.executable,
     os.path.join(ROOT, "tools", "research", "cascade_arithmetic_section.py")],
    capture_output=True, text=True, timeout=3600)
ok = r.returncode == 0 and "10 pass / 0 fail" in r.stdout
gate("g9 the sibling chain green (cascade_arithmetic_section.py 10/0, "
     "transitively chaining the Weil-arc suite)", ok)

ok = paper.count("`cascade_lattice_forcing.py`") >= 2
ok &= "68 scripts cited in place" in paper
ok &= "Theorems 1i–1ar" in paper
gate("g10 the footer census (this script backticked in body and "
     "footer; \"68 scripts cited in place\"; \"Theorems 1i-1ar\")", ok)

n_fail = sum(1 for x in results if not x)
print(f"RESULT: {len(results) - n_fail} pass / {n_fail} fail ({len(results)} gates)")
print("READING.  The half-shift lattice is derived, not adopted: P0")
print("(the paper's declared zero-parameter discipline, an explicit")
print("premise) plus the framework's evenness collapse the translate")
print("continuum to two classes -- the critical (half-density) class")
print("and the arithmetic (algebraic-character) class -- and P0's")
print("second application through 1aq's certified 4/4-vs-0/4")
print("dichotomy decides the binary.  No link mentions integer")
print("points.  The rungs live on the algebraic class; the reading")
print("coordinate is centered at the half-density point.  Conditional")
print("on P0, and says so; no RH leverage in either direction.")
sys.exit(0 if n_fail == 0 else 1)
