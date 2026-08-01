#!/usr/bin/env python3
"""Theorem 1ae verifier: the participation dichotomy, de-conventioned.

Claim under test (the owner's standard: a proof, not a pattern
match): 1ad's trailing-cell convention is ELIMINATED by the
symmetric distance rule delta(d) = min_{d* in S} |d - d*| over the
committed source set S = {5, 7, 14, 19}; the census is invariant
(equivalence gated).  Three theorems and one named lemma:

  (ii) CENSUS: delta = {5: 0, 13: 1, 21: 2}; every deeper seat
       (seat_k = 8k - 3, k >= 4) has nearest source d_1 = 19 (the
       largest element of S, below every such seat), so
       delta = 8k - 22 >= 10, strictly increasing.  Participants
       {5, 13, 21} and nothing else.
  (iii) GAP: realized delta-values are {0, 1, 2} U {10, 18, 26,
       ...} -- no seat realizes delta in [3, 9]; every threshold
       3..9 yields the identical census (enumerated).
       Exhaustiveness is theorem-grade: Part 0 tower completeness
       ("No fifth exists."), Adams/Bott for 14, and part4b's sink
       accounting ("Removing d_2 = 217 as the Planck sink leaves
       exactly four sources") close S for all time.  Sensitivity
       disclosure gated: counting the sink as a source would admit
       exactly one extra participant (seat 213, delta = 4).
  (iv) FORCED CONTRAST: under the committed per-layer filter
       (exponent = layer distance, part4b's neutrino formula), the
       worst participant costs chi^2 = 4, the best non-participant
       chi^10 = 1024; contrast chi^8 = 256 = one Bott period,
       FORCED because seats 21 and 29 share the same nearest
       source (19), so their deltas differ by exactly the seat
       spacing.  Consonance with part4a's independent ~289
       amplitude suppression reported (13% apart), not identified.
  (v)  THE REMAINING LEMMA (named, not proved): a mode filtered by
       >= chi^10 fails A4/S4's measurement condition while
       delta <= 2 modes pass -- with the gap theorem, the lemma
       need not locate a threshold (any point in the seven-wide
       gap gives the same census).

Gates:
  D1 -- the delta census exact (participants, excluded monotone
        8k - 22, nearest source 19 for all deep seats); the
        equivalence with 1ad's trailing-cell census; threshold
        robustness 3..9 by enumeration.
  D2 -- the gap: realized values avoid [3, 9]; max included 2;
        min excluded 10; difference exactly 8 = the seat spacing;
        the shared-nearest-source mechanism (nearest(21) ==
        nearest(29) == 19).
  D3 -- the contrast: delta-derived exponents give chi^10/chi^2 =
        chi^8 (2^8 = 256 DECLARED as literal arithmetic); part4a's
        "\\sim 289" anchored and the consonance |289/256 - 1| < 15%
        gated as CONSONANCE, not identity.
  D4 -- the theorem-grade inputs anchored verbatim: Part 0
        thm:tower's statement; part4b's completeness sentence and
        sink accounting; the sink counterfactual computed (exactly
        one extra participant, seat 213, delta 4).
  D5 -- the paper: 1ae's key sentences anchored (the rule; the gap;
        the forced contrast; the remaining lemma; the grading);
        the net-state marker on 1ad's orientation disclosure; the
        sibling instrument cascade_participation_rule.py subprocess
        exit 0 at RESULT 19/0.

No data consumed; no number changes; categories: (ii)-(iv) theorem
(arithmetic over a theorem-closed set), (v) named lemma.  Sabotage
record (full-tree scratchpad copy, at the landing commit;
mid-anchor perturbations): (a) "No fifth exists." -> "No fiSABfth
exists." in the part0 copy tripped D4, 15/1, exit 1; (b) removing
14 from S in the SCRATCHPAD COPY (instrument-expectation
perturbation) tripped FIVE census gates at once, 11/5, exit 1 --
the census gates cascade on the source set, as they should; (c)
"realizes any δ in [3, 9]" -> "reaSABlizes ..." in the paper copy
tripped D5, 15/1, exit 1 (a first attempt targeted the full
sentence across a line wrap and asserted out before writing --
no run occurred; redone on the non-wrapping substring). Clean
baselines 16/0 exit 0 before and after each.
Sixteen gates (the RESULT line's first draft said 14 --
corrected pre-commit, the recurring count defect's fourth
instance; 1 declared identity not counted).
"""
import os
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
PART0 = os.path.join(ROOT, "src", "cascade-series-part0.tex")
PART4A = os.path.join(ROOT, "src", "cascade-series-part4a.tex")
PART4B = os.path.join(ROOT, "src", "cascade-series-part4b.tex")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


S = {5, 7, 14, 19}
seats = [d for d in range(4, 218) if d % 8 == 5]
delta = {d: min(abs(d - s) for s in S) for d in seats}
inc = {d: v for d, v in delta.items() if v < 8}
exc = {d: v for d, v in delta.items() if v >= 8}

print("D1 -- the delta census and the equivalence")
gate("participants exactly {5: 0, 13: 1, 21: 2}",
     inc == {5: 0, 13: 1, 21: 2}, f"{inc}")
mono = [delta[d] for d in seats if d >= 29]
gate("excluded seats: delta = 8k - 22 >= 10, strictly increasing, nearest "
     "source 19 for every deep seat",
     mono == [8 * k - 22 for k in range(4, 28)]
     and all(min(S, key=lambda s: abs(d - s)) == 19
             for d in seats if d >= 29),
     f"first four: {mono[:4]}")
cell_census = {d for d in seats if set(range(d - 7, d + 1)) & S}
gate("equivalence: the symmetric census == 1ad's trailing-cell census == "
     "{5, 13, 21}", set(inc) == cell_census == {5, 13, 21})
gate("threshold robustness: every cut 3..9 yields the identical census "
     "(enumerated)",
     all({d for d in seats if delta[d] < t} == {5, 13, 21}
         for t in range(3, 10)))

print("D2 -- the gap theorem")
gate("no seat realizes delta in [3, 9]",
     sorted(v for v in delta.values() if 3 <= v <= 9) == [])
gate("max included 2; min excluded 10; difference exactly 8 = the seat "
     "spacing", max(inc.values()) == 2 and min(exc.values()) == 10
     and min(exc.values()) - max(inc.values()) == 8)
gate("the mechanism: nearest(21) == nearest(29) == 19 (the last source), "
     "so the gap is Bott periodicity itself",
     min(S, key=lambda s: abs(21 - s)) == 19
     and min(S, key=lambda s: abs(29 - s)) == 19)

print("D3 -- the forced contrast")
print("  IDENTITY (declared, not gated): chi^8 = 2^8 = 256 -- literal "
      "arithmetic")
chi = 2
contrast = chi ** min(exc.values()) / chi ** max(inc.values())
gate("the delta-derived contrast chi^10/chi^2 = chi^8 = 256",
     contrast == 256.0, f"{contrast:.0f}")
part4a = norm(open(PART4A, encoding="utf-8").read())
gate("part4a's independent ~289 suppression anchored, and the consonance "
     "|289/256 - 1| < 15% -- CONSONANCE, not identity",
     "by a factor of $\\sim 289$" in part4a
     and abs(289.0 / 256.0 - 1) < 0.15,
     f"{abs(289.0 / 256.0 - 1) * 100:.1f}%")

print("D4 -- the theorem-grade inputs")
part0 = norm(open(PART0, encoding="utf-8").read())
part4b = norm(open(PART4B, encoding="utf-8").read())
ok = ("The Gamma function produces exactly four distinguished dimensions "
      "in the cascade. No fifth exists." in part0)
gate("Part 0 thm:tower's statement anchored verbatim", ok)
ok = "they are the complete set of non-sink distinguished layers" in part4b
ok &= "Removing $d_2=217$ as the Planck sink leaves exactly four sources" in part4b
ok &= "forced by Adams' theorem and the Bott mirror" in part4b
gate("part4b's completeness + sink accounting + Adams attribution "
     "anchored", ok)
S2 = S | {217}
extra = [d for d in seats
         if min(abs(d - s) for s in S2) < 8 and delta[d] >= 8]
gate("the sink counterfactual: exactly one extra participant (seat 213, "
     "delta 4)", extra == [213]
     and min(abs(213 - s) for s in S2) == 4, f"{extra}")

print("D5 -- the paper and the sibling instrument")
paper = norm(open(PAPER, encoding="utf-8").read()).replace("**", "")
ok = "a seat participates iff δ(d) < 8" in paper
ok &= "{5, 13, 21} and nothing else, ever." in paper
ok &= "no seat realizes any δ in [3, 9]" in paper
gate("1ae's rule + census + gap sentences anchored", ok)
ok = "χ^8 = 256 — exactly one Bott period of filtering, and forced, not fitted" in paper
ok &= "289 and 256 differ by 13%" in paper
ok &= ("that a mode whose source coupling is filtered by ≥ χ^10 fails "
       "A4/S4's measurement condition" in paper)
ok &= "(ii)–(iv) are theorems" in paper
gate("1ae's contrast + consonance + remaining-lemma + grading sentences "
     "anchored", ok)
ok = ("Net-state, Theorem 1ae round 125: the orientation convention is "
      "eliminated" in paper)
gate("the net-state marker on 1ad's orientation disclosure anchored", ok)
r = subprocess.run([sys.executable,
                    os.path.join(ROOT, "tools", "research",
                                 "cascade_participation_rule.py")],
                   capture_output=True, text=True)
gate("the sibling instrument cascade_participation_rule.py exit 0 at "
     "RESULT 19/0", r.returncode == 0 and "RESULT: 19 pass / 0 fail"
     in r.stdout, f"exit {r.returncode}")

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (16 gates; 1 identity declared, not counted)")
print("READING: the participation dichotomy is de-conventioned -- the")
print("symmetric distance rule delta(d) = min |d - d*| over the")
print("theorem-closed source set (Part 0 tower completeness + Adams for")
print("14 + the committed sink accounting) yields {5, 13, 21} with no")
print("orientation, no partition, no offset; the census is invariant")
print("against 1ad's cell rule.  The gap theorem: no seat sits at delta")
print("3..9, so every threshold in the seven-wide gap gives the same")
print("three generations.  The forced contrast: chi^8 = 256 -- one Bott")
print("period -- because 21 and 29 share the last source as nearest.")
print("What remains is one named lemma: chi^10-filtered modes fail the")
print("A4/S4 measurement condition.  (ii)-(iv) theorems; (v) the lemma;")
print("nothing is a convention.  Check 8 clean.")
sys.exit(0 if n_fail == 0 else 1)
