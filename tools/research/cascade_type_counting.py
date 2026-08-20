#!/usr/bin/env python3
"""Theorem 1al verifier: the type-counting close, upgraded to its
exact residue.

Claim under test: the "weakest link" of 1ae(iii)'s exhaustiveness
chain -- part4b's remark-level type counting ("no fifth source
TYPE") -- upgrades to exact combinatorics plus enumerated
precedence-idleness plus ONE named open lemma.  It does not close;
it sharpens.

T1 (count mechanics, exact): a linear short-circuit decision list
  on k binary flags has exactly k+1 outcome classes (enumerated
  for k = 1..6); with the committed k = 3, exactly four types, and
  the 8 possible flag vectors partition 4+2+1+1 (P subsumes 4,
  L 2, G 1, default 1).  "No fifth type without a new structural
  element" upgrades to: within the committed linear short-circuit
  format, a fifth type requires a FOURTH FLAG -- exact, not
  remark-grade (format scope round 156 F4; a tree split is itself
  a new structural element and dead-ends at the same
  fifth-layer wall).
T2 (precedence idleness -- the round-9 vacuity verdict upgraded
  to a gated theorem; the landing's "NEW" struck round 156 F1,
  the verdict pre-existing in cascade_precedence_vacuity.py and
  two paper passages): the committed record's realized
  flag vectors are exactly the four at-most-one-hot vectors
  {TFF, FTF, FFT, FFF}, two observables each (max true flags = 1
  across all eight); ALL 3! = 6 precedence orders classify the
  committed eight identically.  The open P > L > G precedence
  derivation is NOT load-bearing on the committed record -- idle;
  multi-flag vectors occur only under the sibling vacuity
  instrument's four tested VARIANT readings (13-109 sigma
  exclusions there, conditional -- scoped round 156 F1).
T3 (the bijection, with the source side theorem-grade): the four
  types map bijectively onto the four non-sink distinguished
  layers {19, 5, 14, 7}, reproducing all eight committed
  assignments; the SOURCE side's count is theorem-grade -- Part
  0's tower completeness (Gamma-mechanism closed), Adams within
  the committed scan whose interval has a Gamma-named UPPER
  endpoint (part4a's notation "[5,d_1=19]" writes it as the first
  threshold BY NAME; the lower endpoint is a bare 5 in the
  committed scan text -- de-pluralized round 156 F3), and the
  sink exclusion forced by the committed
  dynamics (the 1af arc's constraint-node theorem).
The residue, named exactly: the categorical flag derivation --
  part4b's own "Does not" item ("derive the three syntactic flags
  (P,L,G) themselves from a formal category of cascade
  observables").  Under the committed flag<->layer correspondence
  (P<->19, L<->5, G<->14, default<->7) the fourth-flag question
  REDUCES to the fifth-non-sink-layer question: closed by theorem
  on the Gamma mechanism, closed relative to the committed scan
  on the Adams mechanism (recurrences at 20, 28, 36 lie beyond
  the first threshold), open only as "a new structural mechanism
  would reopen it" -- the round-126 barrier, now carrying exact
  combinatorics on every other step.

No data; no closures; no new physics; category (a).  Check 7
clean (finite enumeration + committed anchors; no semiclassics).
Check 8 clean (no hypothesis input -- the flags and layers are
committed structure).

Gates (twelve):
  V1 (T2) -- g1 the committed eight imported from the COMMITTED
       verifier (tools/verifiers/verify_selection_rule.py):
       realized vectors exactly the four at-most-one-hot, two
       observables each, max true flags 1; g2 all 6 precedence
       orders classify the committed eight identically, PLUS (round
       156 F1, scope fixed round 157 F3) the sibling
       cascade_precedence_vacuity.py subprocess green and both
       pre-existing paper carriers anchored distinctly (the remark
       phrase counted >= 2; the front-matter wording separate).
  V2 (T1) -- g3 the 8 flag vectors partition 4+2+1+1 into exactly
       4 classes; k-flag linear lists give k+1 classes for
       k = 1..6.
  V3 (T3) -- g4 the bijection types -> {19, 5, 14, 7} with all
       eight committed paper assignments reproduced, and the
       committed verifier subprocess exit 0; g5 the source side's
       theorem anchors (part0 tower completeness verbatim;
       part4b's sink-removal sentence; the paper's
       forced-by-the-committed-dynamics sink upgrade); g6 the
       flag<->layer pairing rationales anchored in part4b (the
       unique non-sink threshold; structurally adjacent; the
       window's highest layer; the unique equilibrium).
  V4 (the residue) -- g7 part4b's "Does not" flag-derivation item
       + the no-fifth-type remark sentence anchored; g8 the
       Adams-scan interval's committed notation "[5,d_1=19]"
       anchored in part4a + the paper's relative-closure sentence
       anchored.
  V5 -- g9 1al's key sentences anchored; g10 the two net-state
       markers on the weakest-link sentences anchored; g11 the
       footer census (the new script backticked; "83 scripts cited in place"; "Theorems 1i–1bg" -- advanced at the
       1am-1ap landings, the census-evolution class, disclosed); g12 the two Weil-arc
       footer-gating siblings re-run green after the census
       advance (quarter_square 12/0; route_traveled 22/0).

Sabotage record (full-tree scratchpad copy, at the landing
commit; mid-anchor perturbations): (a) the paper's "a fifth type
requires a FOURTH FLAG" sentence perturbed mid-anchor -> g9
trips, 11/1, exit 1; (b) one committed flag flipped in the COPY's
verify_selection_rule.py (theta_C gauge_mediated False -> True)
-> g1 trips (the two-observables-each census breaks: the flipped
vector joins the FFT class, making it 3 and emptying FFF to 1)
AND g4 trips (theta_C reclassifies to Gauge -> source 14 != the
committed 7, and the committed classifier subprocess itself
exits 1), 10/2, exit 1 (the landing said 11/1 -- census corrected
round 156 F2);
(c) the 1al net-state marker at the 1af weakest-link sentence
perturbed mid-anchor (sharpens -> narrows) -- DISCLOSED PRE-COMMIT
CATCH: the first attempt did NOT trip (12/0) because g10's first
draft counted the marker labels only (the count-only-gate class);
content anchors were added and the redone sabotage trips g10,
11/1, exit 1.  At the round-157 sweep (the READING resweep + the
g2 anchor-scope fix): (d) the occupancy remark's body phrase
mangled (vacuous -> inert) -> g2 trips, 11/1, exit 1 -- the
strike frame's self-quote alone no longer satisfies (the count
>= 2 condition, the round-157 F3 fix biting); (e) the
front-matter residue wording mangled -> g2 trips, 11/1, exit 1.
Clean baselines
12/0 exit 0 before and after each.  Twelve gates (count checked
against the gate() census pre-commit; the count defect's history
noted).
"""
import itertools
import os
import subprocess
import sys
from collections import Counter

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
PART0 = os.path.join(ROOT, "src", "cascade-series-part0.tex")
PART4A = os.path.join(ROOT, "src", "cascade-series-part4a.tex")
PART4B = os.path.join(ROOT, "src", "cascade-series-part4b.tex")

sys.path.insert(0, os.path.join(ROOT, "tools", "verifiers"))
import verify_selection_rule as vsr  # noqa: E402

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


def paper_for_g2():
    return norm(open(PAPER, encoding="utf-8").read()).replace("**", "")


print("V1 -- T2: the precedence is idle on the committed record")
obs = vsr.OBSERVABLES
vecs = [(o.planck_anchored, o.observer_local, o.gauge_mediated) for o in obs]
census = Counter(vecs)
onehot = {(True, False, False), (False, True, False),
          (False, False, True), (False, False, False)}
gate("g1 the committed eight (imported from the committed verifier): "
     "realized vectors exactly the four at-most-one-hot, two "
     "observables each, max true flags 1",
     len(obs) == 8 and set(census) == onehot
     and all(v == 2 for v in census.values())
     and max(sum(v) for v in vecs) == 1,
     f"census {sorted(census.values())}")


def classify_order(v, order):
    val = dict(zip("PLG", v))
    for f in order:
        if val[f]:
            return f
    return "default"


base = [classify_order(v, ("P", "L", "G")) for v in vecs]
idle = all([classify_order(v, o) for v in vecs] == base
           for o in itertools.permutations("PLG"))
# round 156 F1: the pre-existing verdict cross-referenced and gated.
# Round 157 F3: the first draft anchored ONE needle satisfiable by
# 1al's own strike-frame quote (the self-satisfying-anchor class);
# now BOTH pre-existing carriers are gated distinctly -- the
# occupancy remark's phrase counted >= 2 (the strike frame's
# self-quote alone cannot satisfy it) and the front-matter residue
# list's distinct wording anchored separately.
rv = subprocess.run([sys.executable,
                     os.path.join(ROOT, "tools", "research",
                                  "cascade_precedence_vacuity.py")],
                    capture_output=True, text=True)
idle &= rv.returncode == 0
_pg2 = paper_for_g2()
idle &= _pg2.count("vacuous on primary readings") >= 2
idle &= ("vacuous on the papers' uniform expression-tree flag readings"
         in _pg2)
gate("g2 ALL 6 precedence orders classify the committed eight "
     "identically -- the round-9 vacuity verdict upgraded, not "
     "discovered (cross-referenced round 156 F1; anchor scope fixed "
     "round 157 F3: the sibling cascade_precedence_vacuity.py green; "
     "BOTH pre-existing carriers anchored distinctly -- the remark "
     "phrase counted >= 2, the front-matter wording separate)", idle,
     f"vacuity exit {rv.returncode}, remark-count "
     f"{_pg2.count('vacuous on primary readings')}, front-matter "
     f"{'ok' if 'vacuous on the papers' in _pg2 else 'MISSING'} "
     "(detail widened round 158 F1)")

print("V2 -- T1: the count mechanics, exact")
all8 = list(itertools.product([True, False], repeat=3))
part = Counter(classify_order(v, ("P", "L", "G")) for v in all8)
ok = part == Counter({"P": 4, "L": 2, "G": 1, "default": 1})
for k in range(1, 7):
    allv = list(itertools.product([True, False], repeat=k))

    def leaf(v):
        for i, x in enumerate(v):
            if x:
                return i
        return len(v)

    ok &= len(set(leaf(v) for v in allv)) == k + 1
gate("g3 the 8 flag vectors partition 4+2+1+1 into exactly 4 classes; "
     "a k-flag linear list has k+1 classes for k = 1..6 -- a fifth "
     "type requires a fourth flag, exactly", ok,
     f"partition {dict(part)}")

print("V3 -- T3: the bijection, with the source side theorem-grade")
types = [vsr.classify(o) for o in obs]
srcs = {t: vsr.predict_source(t) for t in set(types)}
ok = sorted(srcs.values()) == [5, 7, 14, 19] and len(srcs) == 4
ok &= all(vsr.predict_source(vsr.classify(o)) == o.paper_d_star for o in obs)
r = subprocess.run([sys.executable,
                    os.path.join(ROOT, "tools", "verifiers",
                                 "verify_selection_rule.py")],
                   capture_output=True, text=True)
ok &= r.returncode == 0
gate("g4 types -> {19, 5, 14, 7} bijective, all eight committed "
     "assignments reproduced; the committed verifier exit 0", ok,
     f"exit {r.returncode}")
part0 = norm(open(PART0, encoding="utf-8").read())
part4b = norm(open(PART4B, encoding="utf-8").read())
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = ("The Gamma function produces exactly four distinguished dimensions "
      "in the cascade. No fifth exists." in part0)
ok &= "Removing $d_2=217$ as the Planck sink leaves exactly four" in part4b
ok &= "forced by the committed dynamics" in paper
gate("g5 the source side's theorem anchors (tower completeness; the "
     "sink-removal accounting; the 1af sink-dynamics upgrade)", ok)
ok = "The unique non-sink threshold is $d_1=19$" in part4b
ok &= "the unique one structurally adjacent to the observer" in part4b
ok &= "The highest layer of the window is $d=14$" in part4b
ok &= "the unique cascade equilibrium between the observer and the" in part4b
gate("g6 the flag<->layer pairing rationales anchored in part4b "
     "(P<->19; L<->5; G<->14; default<->7)", ok)

print("V4 -- the residue, named exactly")
ok = "derive the three syntactic flags $(P,L,G)$" in part4b
ok &= ("No fifth type is definable without introducing a new structural "
       "element" in part4b)
gate("g7 the residue's committed anchors (the Does-not flag-derivation "
     "item; the no-fifth-type remark sentence)", ok)
part4a = norm(open(PART4A, encoding="utf-8").read())
ok = "unique} dimension in $[5,d_1=19]$ where $\\rho(d)-1=3$" in part4a
ok &= "closed relative to the committed source set" in paper
gate("g8 the Adams-scan interval's committed notation (the upper "
     "endpoint is d_1 BY NAME) + the paper's relative-closure sentence",
     ok)

print("V5 -- the anchors and the footer")
ok = "a fifth type requires a FOURTH FLAG" in paper
ok &= ("the open P > L > G precedence derivation is idle on the "
       "committed record" in paper)
ok &= "the weakest link sharpens but does not vanish" in paper
ok &= ("the fourth-flag question REDUCES to the fifth-non-sink-layer "
       "question" in paper)
gate("g9 1al's key sentences anchored (the fourth-flag upgrade; the "
     "idleness; the sharpened link; the reduction)", ok)
# DISCLOSED PRE-COMMIT CATCH: the first draft counted the marker
# labels only ("Net state (1al):" == 2) and the mid-marker sabotage
# (sharpens -> narrows) passed 12/0 -- the count-only-gate class.
# Content anchors added; the redone sabotage trips.
ok = paper.count("Net state (1al):") == 2
ok &= ("the barrier is upgraded — the count mechanics are exact "
       "combinatorics" in paper)
ok &= ("the weakest link sharpens to one named open lemma (the "
       "categorical flag derivation)" in paper)
gate("g10 the two net-state markers anchored BY CONTENT (the 1ae-chain "
     "passage; the 1af passage; count-only first draft caught by "
     "sabotage pre-commit, disclosed)", ok,
     f"count {paper.count('Net state (1al):')}")
# 1am landing: the footer census advanced (62 -> 63; range -> 1am);
# then 1an (63 -> 64) and 1ao (64 -> 65; range -> 1ao) -- the
# census-evolution class, disclosed each time.
ok = "`cascade_type_counting.py`" in paper
ok &= "83 scripts cited in place" in paper
ok &= "Theorems 1i–1bg" in paper
gate("g11 the footer census (advanced at the 1am-1ap landings, "
     "disclosed): this script backticked; 83 cited in place; the "
     "range 1i–1bg (label re-synced rounds 167 F6, 175 F2, 213 F3)", ok)
ok = True
for s, expect in (("cascade_quarter_square", "12 pass / 0 fail"),
                  ("cascade_weil_route_traveled", "22 pass / 0 fail")):
    rr = subprocess.run([sys.executable,
                         os.path.join(ROOT, "tools", "research", s + ".py")],
                        capture_output=True, text=True)
    ok &= rr.returncode == 0 and expect in rr.stdout
gate("g12 the two footer-gating siblings green after the census advance "
     "(quarter_square 12/0; route_traveled 22/0)", ok)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (12 gates)")
print("READING: the type-counting close, upgraded to its exact residue.")
print("T1: a linear short-circuit list on k flags has k+1 types (k=1..6")
print("enumerated); committed k=3 -> exactly four; the 8 vectors")
print("partition 4+2+1+1 -- a fifth type requires a fourth flag")
print("within the committed linear format (scoped round 156 F4).")
print("T2 (the round-9 vacuity verdict upgraded to a gated theorem --")
print("novelty struck round 156 F1; READING resweep round 157 F1, the")
print("un-swept-print class): the committed record realizes only the four")
print("at-most-one-hot vectors (two observables each), so ALL six")
print("precedence orders agree on the committed eight -- the open")
print("P > L > G derivation carries no load on the committed record.")
print("T3: the type->source bijection reproduces all eight committed")
print("assignments, and the SOURCE side is theorem-grade (tower")
print("completeness; the Adams scan with its Gamma-named UPPER endpoint")
print("(de-pluralized round 156 F3, READING resweep round 157 F2); the")
print("sink exclusion forced by dynamics).  The residue, named: the")
print("categorical flag derivation (part4b's own Does-not item) --")
print("under the committed flag<->layer correspondence the fourth-flag")
print("question reduces to the fifth-non-sink-layer question, closed by")
print("theorem on the Gamma mechanism and closed relative to the")
print("committed scan on the Adams mechanism.  The weakest link")
print("sharpens from remark-level counting to one named open lemma; it")
print("does not vanish.  No data, no closures, no new physics.")
sys.exit(0 if n_fail == 0 else 1)
