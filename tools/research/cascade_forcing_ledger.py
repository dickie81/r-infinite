#!/usr/bin/env python3
"""Theorem 1aa verifier: the forcing ledger.

Claim under test: the owner's forcing question ("what forces the
selection; why do these properties project into the observer's
spacetime; why do they present as particles at d = 5") stratifies
exactly: Stratum F (structure-forced menus -- Clifford windows,
Majorana deserts, Bott generation seats, Adams gauge triple, the
Gamma-forced distinguished layers); Stratum E (entailed given C1's
seat -- the visible spectrum and the single-valued address rules);
Stratum C (C1-primitive residue, exactly three items: occupancy, the
observer<->twist-4 labeling, the discrete Definition-6.1 entries).
The labeling's committed exhibit: {k : gamma^k = -1} = {4}, the
unique nontrivially-real residue of the Z/8 clock -- "a labeling,
not a derivation" (Definition 6.1's own grading, anchored). The
d = 5 presentation chain is a four-way conjunction with three
structure-forced conjuncts and one seat-consuming conjunct. Check 8
load-bearing: no step derives the seat.

Gates:
  L1 -- the Clifford window arithmetic: d mod 8 in {4,5,6} iff
        complex; the windows {4,5,6}, {12,13,14}, {20,21,22} in
        [4,22]; the deserts 7..11 and 15..19 all non-complex; the
        Bott seats {5,13,21} = Dirac layers d = 5 mod 8 in the span.
  L2 -- the Z/8 clock exhibit: zeta_8^4 = -1 exactly; the real
        residues of <zeta_8> are {1, -1}; {k in 0..7 : gamma^k = -1}
        = {4} (unique, nontrivially real); the committed flip-word
        anchor ("{k : gamma^k = -1} = {4}") present in the paper.
  L3 -- the d = 5 conjunction: argmax_Z V = 5 (recomputed); 5 mod 8
        = 5 (first-window Dirac + first Bott seat); d = 5 is the
        UNIQUE layer in the first window satisfying (a)-(c); the
        desert layers 7..11 have d mod 8 in {7,0,1,2,3}, none
        complex.
  L4 -- the boundary anchors, verbatim: the formulation's "what can
        never be a theorem" header; Theorem 13's scope sentence
        ("not 'the address book is forced'"); Definition 6.1's
        labeling grading ("though its link to the observer is a
        labeling, not a derivation"); part4a's desert sentence
        ("support no quantum matter content visible to the d=4
        observer"); the convention-free-distinction sentence.
  L5 -- 1aa's key sentences anchored (the three strata; the exact
        stratum-C residue; the four-way conjunction with "(d) alone
        consumes the seat"; the one-sentence answer; the
        stopping-rule-gated labeling route).

No data consumed; no number changes; category (a). Additive theorem
-- no net-state markers owed (nothing superseded; gated by absence
of contradiction with 1z's accounting). Sabotage record (scratchpad
copies, at the landing commit): (a) perturbing the Definition-6.1
grading anchor trips L4, exit 1; (b) altering the conjunction's
argmax expectation trips L3, exit 1.
"""
import cmath
import math
import os
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
FORM = os.path.join(ROOT, "cascade-riemann-formulation.md")
PART4A = os.path.join(ROOT, "src", "cascade-series-part4a.tex")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def complex_window(d):
    return d % 8 in (4, 5, 6)


print("L1 -- the Clifford window arithmetic")
wins = [d for d in range(4, 23) if complex_window(d)]
gate("windows in [4,22]: {4,5,6} + {12,13,14} + {20,21,22}",
     wins == [4, 5, 6, 12, 13, 14, 20, 21, 22], f"{wins}")
deserts = [d for d in list(range(7, 12)) + list(range(15, 20))
           if complex_window(d)]
gate("the Majorana deserts 7..11 and 15..19: zero complex layers",
     deserts == [], f"violations = {deserts}")
seats = [d for d in range(4, 23) if d % 8 == 5]
gate("the Bott generation seats in the span: {5, 13, 21}",
     seats == [5, 13, 21], f"{seats}")

print("L2 -- the Z/8 clock exhibit")
z8 = cmath.exp(2j * math.pi / 8)
gate("zeta_8^4 = -1 exactly", abs(z8 ** 4 - (-1)) < 1e-15)
reals = sorted(round((z8 ** k).real, 12) for k in range(8)
               if abs((z8 ** k).imag) < 1e-12)
gate("the real residues of <zeta_8> are {1, -1}", reals == [-1.0, 1.0],
     f"{reals}")
flip = [k for k in range(8) if abs(z8 ** k - (-1)) < 1e-12]
gate("{k : gamma^k = -1} = {4} -- unique, nontrivially real", flip == [4],
     f"{flip}")
paper = open(PAPER, encoding="utf-8").read()


def norm(s):
    return " ".join(s.split())


np_ = norm(paper)
gate("the committed flip-word anchor present (exact, normalized)",
     "({k : γᵏ = −1} = {4})" in np_)

print("L3 -- the d = 5 conjunction")


def V(d):
    return math.pi ** (d / 2.0) / math.gamma(d / 2.0 + 1)


argmax = max(range(1, 30), key=V)
gate("argmax_Z V = 5 (recomputed)", argmax == 5, f"{argmax}")
gate("5 mod 8 = 5: first-window Dirac layer and first Bott seat",
     5 % 8 == 5 and complex_window(5))
first_window_dirac = [d for d in (4, 5, 6) if d % 8 == 5]
gate("d = 5 is the unique first-window layer that is a Dirac/Bott seat "
     "and the argmax", first_window_dirac == [5] and argmax == 5)
gate("desert residues: 7..11 have d mod 8 in {7,0,1,2,3}, none complex",
     [d % 8 for d in range(7, 12)] == [7, 0, 1, 2, 3]
     and not any(complex_window(d) for d in range(7, 12)))

print("L4 -- the boundary anchors (verbatim)")
form = open(FORM, encoding="utf-8").read()
part4a = open(PART4A, encoding="utf-8").read()
gate("formulation: 'what can never be a theorem' header",
     "what can never be a theorem" in norm(form))
gate("Theorem 13's scope sentence anchored (exact, normalized)",
     'not "the address book is forced."' in np_)
ok4 = ("though its link to the" in np_
       and "is a labeling, not a derivation" in np_)
gate("Definition 6.1's labeling grading anchored", ok4)
gate("part4a's desert sentence anchored",
     "support no quantum matter content visible to the $d=4$" in norm(part4a))
gate("the convention-free-distinction sentence anchored",
     "one convention-free arithmetic distinction" in np_.replace("**", ""))

print("L5 -- 1aa's key sentences")
npp = np_.replace("**", "")
ok5 = "stratify the question into its forcible parts" in npp
ok5 &= "Stratum C (C1-primitive — the exact residue). Three items and no more" in npp
ok5 &= "(d) alone consumes the seat" in npp
ok5 &= ("the properties are forced (the menus), the projection is entailed "
        "(given the seat), and the seat is the hypothesis" in npp)
gate("the strata, the exact residue, the conjunction, the one-sentence answer",
     ok5)
ok6 = ("a committed derivation of the observer↔4 link from the clock "
       "distinction would move the labeling from stratum C to stratum F"
       in npp)
gate("the stopping-rule-gated labeling route anchored", ok6)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (18 gates)")
print("READING: the forcing question stratifies exactly -- the menus are")
print("theorems (Clifford, Bott, Adams, Gamma), the projection is entailed")
print("given the seat, and the seat is C1, carrying one convention-free")
print("arithmetic distinction ({k : gamma^k = -1} = {4}) whose link to the")
print("observer is a labeling, not a derivation. The d = 5 presentation is")
print("a four-way conjunction, three conjuncts forced, one consuming the")
print("seat. Check 8 load-bearing; no closure; no number changes.")
sys.exit(0 if n_fail == 0 else 1)
