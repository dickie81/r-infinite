#!/usr/bin/env python3
"""Theorem 1aa verifier: the forcing ledger.

Claim under test: the owner's forcing question ("what forces the
selection; why do these properties project into the observer's
spacetime; why do they present as particles at d = 5") stratifies
(as corrected round 112): Stratum F (structure-forced -- the window
ARITHMETIC: Clifford residues, the first desert's committed sentence,
Adams gauge triple with N_c act-conditional and disclosed, the
Gamma-forced distinguished layers); Stratum D (empirically anchored
terminations, added round 112: the charged Bott ladder's Tier-4 cut;
the third window's non-seat layers without committed disposition);
Stratum E (entailed given the seat PLUS the convention ledger);
Stratum C (C1-primitive residue, exactly three items: occupancy, the
observer<->twist-4 labeling, the discrete Definition-6.1 entries).
The labeling's committed exhibit: {k : gamma^k = -1} = {4} -- the
index at which the clock reaches its unique nontrivially-real
residue, -1 (round-113 F3 corrected the docstring's conflation of
index and residue) -- "a labeling, not a derivation" (Definition
6.1's own grading, anchored). The
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
        = {4}, the index of the unique nontrivially-real residue,
        -1 (round-114 F2 swept the Gates summary's last
        conflation); the committed flip-word
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
# round-112 F6: zeta_8^4 = -1 is a literal identity -- DECLARED, not gated
# (the 1l(iv) discipline: a tautology cannot fail)
print("  IDENTITY (declared, not gated): zeta_8^4 = -1 -- literal arithmetic")
reals = sorted(round((z8 ** k).real, 12) for k in range(8)
               if abs((z8 ** k).imag) < 1e-12)
gate("the real residues of <zeta_8> are {1, -1}", reals == [-1.0, 1.0],
     f"{reals}")
flip = [k for k in range(8) if abs(z8 ** k - (-1)) < 1e-12]
gate("{k : gamma^k = -1} = {4} -- the index of the unique nontrivially-real "
     "residue, -1", flip == [4],
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
# round-112 F6: 5 mod 8 = 5 is constant arithmetic -- DECLARED, not gated
print("  IDENTITY (declared, not gated): 5 mod 8 = 5, in the complex class")
first_window_dirac = [d for d in (4, 5, 6) if d % 8 == 5]
gate("d = 5 is the unique first-window layer that is a Dirac/Bott seat "
     "and the argmax", first_window_dirac == [5] and argmax == 5)
# round-112 F6: the desert-residue list is constant arithmetic -- DECLARED
print("  IDENTITY (declared, not gated): 7..11 mod 8 = {7,0,1,2,3}, none complex")
part4a_txt = open(PART4A, encoding="utf-8").read()
gate("part4a's infinite-ladder sentence anchored (round-112 F1)",
     "with no cascade-internal termination of the replication"
     in norm(part4a_txt))
gate("part4a's Tier-4 empirical-anchor sentence anchored (round-112 F1)",
     "relies on empirical non-observation at LEP, atomic, fixed-target, and "
     "cosmological observations" in norm(part4a_txt))

print("L4 -- the boundary anchors (verbatim)")
form = open(FORM, encoding="utf-8").read()
part4a = open(PART4A, encoding="utf-8").read()
gate("formulation: 'what can never be a theorem' header",
     "what can never be a theorem" in norm(form))
gate("Theorem 13's scope sentence anchored (exact, normalized)",
     'not "the address book is forced."' in np_)
i_d61 = paper.find("**Definition 6.1 (address book).**")
i_end = paper.find("## 7. Uniqueness", i_d61)
d61_span = norm(paper[i_d61:i_end])
gate("Definition 6.1's labeling grading anchored WITHIN Definition 6.1's span "
     "(round-112 F7: the draft gate matched anywhere, so 1aa's own recital "
     "satisfied it)",
     i_d61 > 0 and i_end > i_d61
     and "is a labeling, not a derivation" in d61_span)
gate("part4a's FIRST-desert sentence anchored (round-112 F3: it covers "
     "d=7..11 only)",
     "five real (Majorana) layers $d=7,8,9,10,11$" in norm(part4a)
     and "support no quantum matter content visible to the $d=4$" in norm(part4a))
gate("the convention-free-distinction sentence anchored",
     "one convention-free arithmetic distinction" in np_.replace("**", ""))

print("L5 -- 1aa's key sentences")
npp = np_.replace("**", "")
ok5 = "stratify the question into its forcible parts" in npp
ok5 &= "Stratum C (C1-primitive — the exact residue). Three items and no more" in npp
ok5 &= "(d) alone consumes the seat" in npp
ok5 &= "Stratum D (empirically anchored — the terminations; added round 112" in npp
ok5 &= "given the seat plus the convention ledger" in npp
ok5 &= ("the window arithmetic is forced (Clifford, Adams, Γ), the charged "
        "ladder's termination is empirically anchored" in npp)
ok5 &= "the index at which the clock reaches its unique nontrivially-real residue, −1" in npp
gate("the strata (incl. D), the corrected answer, the F5 wording anchored", ok5)
ok6 = ("a committed derivation of the observer↔4 link from the clock "
       "distinction would move the labeling from stratum C to stratum F"
       in npp)
gate("the stopping-rule-gated labeling route anchored", ok6)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (17 gates; 3 identities declared, not counted -- round-112 F6)")
print("READING (round-113 F2 corrected the pre-sweep summary): the window")
print("arithmetic is forced (Clifford, Adams, Gamma); the charged ladder's")
print("termination is empirically anchored (Stratum D, Tier 4, part4a's")
print("own grading); the projection is entailed given the seat PLUS the")
print("convention ledger; the seat is C1, carrying one convention-free")
print("arithmetic distinction -- {k : gamma^k = -1} = {4}, the index of")
print("the clock's unique nontrivially-real residue, -1 -- whose link to")
print("the observer is a labeling, not a derivation. The d = 5")
print("presentation is a four-way conjunction, three conjuncts forced,")
print("one consuming the seat. Check 8 load-bearing; no closure.")
sys.exit(0 if n_fail == 0 else 1)
