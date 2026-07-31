#!/usr/bin/env python3
"""Theorem 1x verifier: the Door-4 status probe.

Claim under test: 1t's licensed falsifier ("any future derivation
that routes a grammar entry through the odd bridge's L-side re-opens
the member's derivational weight") is UNFIRED by Theorem 1w, on both
conjuncts: (a) no grammar entry is rerouted -- the cascade tex papers
consume the pairing-act nowhere, and N_c's papers-side carrier is the
Radon-Hurwitz entry the axiom block itself lists (A2's 2-adic row);
(b) 1w's forcing chain is ring-side (the act, the field, the ring,
mu_6), with zero L-side tokens, the mass-arc precedent (1t(iv))
covering the side. The zero-weight grading of 1t(v) is refined,
superseded-true: the act is now consumed by three review-side chains
(1c(ii)/1j minimality, 1r partner, 1w count) while its weight FOR
NUMBERS remains zero. Post-adoption, the axiom block carries zero
odd-reading content (per-token adjudicated) while carrying the ring
side natively: Door 4's asymmetry mirrored inside the axioms.

Gates:
  D1 -- falsifier conjunct (a): "given the (pairing-)act" has zero
        occurrences across all 12 cascade tex sources (gated file by
        file); A2's N_c row anchored verbatim in the live axiom
        block; 1w's no-number-changes tail anchored.
  D2 -- falsifier conjunct (b): 1w's forcing-chain span ((ii)-(iii))
        carries zero L-side tokens (L-values, zeros, prime sum,
        bridge conductor term); "conductor" appears in 1w exactly
        twice, located outside the chain ((i) scoping note, (v)
        exhibit).
  D3 -- consumers census: the "given the (pairing-)act" sites
        outside 1x's own span counted exactly, case-insensitively
        (9 paper, 5 formulation; round-104 F1 corrected the first
        draft's positionally truncated 7) and all review-side (D1
        gates the tex zero); the exhibit |mu(R)| = 2 recomputed.
  D4 -- the axiom block's odd-reading census, per-token adjudicated:
        chi_{-3}, "character" (word), " odd", "conductor", "pairing",
        "Dirichlet", "L(s" all zero; A1's character-substrings are
        two "characterisation" tokens (adjudicated); the chi tokens are
        A2's torsion constant chi = 2 = |mu(R)|; ring side present:
        Q(zeta_3) and Z[omega] named, "N_c = 3" exactly once.
  D5 -- surface anchors, verbatim and failable: both falsifier
        sentences; 1t's scope sentence; the three net-state markers;
        1x's key sentences (unfired-on-both-conjuncts, ring-side-
        native/L-side-extrinsic, the sharpened falsifier).

No data consumed; no number changes anywhere. Sabotage record: at
commit time, two runs on scratchpad copies -- (a) a one-token
perturbation of the 1t(v) marker anchor flips D5, exit 1; (b) a
lowercase act-consumption phrase injected into a tex copy flips D1,
exit 1. Round-104 F2 found the first D1 case-sensitive (a
capitalized injection evaded it, exit 0, reproduced by the
reviewer) and its self-description overclaimed: D1 is now
case-insensitive, and its scope is the censused phrase family
("given the (pairing-)act", any case) -- the sharpened papers-side
falsifier of 1x(v) is wider than any phrase gate, and consumption
worded outside the family is hostile-round territory, not this
instrument's.
"""
import glob
import os
import re
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PAPER = os.path.join(ROOT, "riemann-indistinguishability.md")
FORM = os.path.join(ROOT, "cascade-riemann-formulation.md")

results = []


def gate(name, ok, detail=""):
    results.append(ok)
    print(f"  {name}: {'PASS' if ok else 'FAIL'}" + (f"  ({detail})" if detail else ""))


def norm(s):
    return " ".join(s.split())


paper = open(PAPER, encoding="utf-8").read()
form = open(FORM, encoding="utf-8").read()
npaper, nform = norm(paper), norm(form)

# spans
i_1w = paper.find("**Theorem 1w (the kernel-native colour count")
i_1x = paper.find("**Theorem 1x (the Door-4 status probe")
i_d3 = paper.find("**Remark (Door 3: what the vector-field count load-bears on")
assert 0 < i_1w < i_1x < i_d3
t1w = paper[i_1w:i_1x]
pre_1x = paper[:i_1x]
i_ii = t1w.find("*(ii) The unit-torsion")
i_iv = t1w.find("*(iv) The Check-8 cross-check")
chain = t1w[i_ii:i_iv]
assert i_ii > 0 and i_iv > i_ii

# the live axiom block
i0 = form.find("**A1")
i1 = form.find("(lemma S5).", i0)
block = form[i0:i1 + len("(lemma S5).")]
assert 0 < i0 < i1

print("D1 -- falsifier conjunct (a): no grammar entry rerouted")
tex_hits = {}
for f in sorted(glob.glob(os.path.join(ROOT, "src", "cascade-series-*.tex"))):
    t = open(f, encoding="utf-8").read()
    n = len(re.findall(r"(?i)given the (?:pairing-)?act", t))
    if n:
        tex_hits[os.path.basename(f)] = n
n_tex = len(glob.glob(os.path.join(ROOT, "src", "cascade-series-*.tex")))
gate("tex papers consume the act nowhere (12 files, zero hits)",
     tex_hits == {} and n_tex == 12, f"{n_tex} files scanned, hits = {tex_hits}")
a2_row = "| N_c = 3 = 2^(v₂(12))−1 | Radon–Hurwitz count | a 2-adic invariant (value depends only on v₂) |"
gate("A2's N_c row anchored in the live axiom block", a2_row in block)
gate("1w's no-number-changes tail anchored",
     "no data consumed, no number changes" in norm(t1w))

print("D2 -- falsifier conjunct (b): the route is ring-side")
lside = ["L(s", "p_sgn", "zeros", "Λ(n)", "½ln 3", "critical line"]
hits = {tok: chain.count(tok) for tok in lside if chain.count(tok)}
gate("forcing chain ((ii)-(iii)) carries zero L-side tokens",
     hits == {}, f"hits = {hits}")
n_cond = norm(t1w).count("conductor")
i_v = t1w.find("*(v) Exhibit")
span_i = t1w[:i_ii]
span_v = t1w[i_v:]
gate("'conductor' in 1w exactly twice, both outside the chain ((i) + (v))",
     n_cond == 2 and norm(span_i).count("conductor") == 1
     and norm(span_v).count("conductor") == 1 and chain.count("conductor") == 0,
     f"total {n_cond}; (i): {norm(span_i).count('conductor')}, "
     f"(v): {norm(span_v).count('conductor')}, chain: {chain.count('conductor')}")
t1x = paper[i_1x:i_d3]
gate("chain's two chi_-3 tokens disclosed as attributional (round-104 F3)",
     chain.count("χ₋₃") == 2 and "both **attributional**" in norm(t1x),
     f"chain chi_-3 count {chain.count('χ₋₃')}")

print("D3 -- consumers census (review-side only)")
outside_1x = paper[:i_1x] + paper[i_d3:]
n_p = len(re.findall(r"(?i)given the (?:pairing-)?act", outside_1x))
n_f = len(re.findall(r"(?i)given the (?:pairing-)?act", form))
gate("consumption sites outside 1x's span (round-104 F1): 9 paper, 5 formulation",
     n_p == 9 and n_f == 5, f"paper {n_p}, formulation {n_f}")
mu_R = sum(1 for u in (1, -1) if u * u == 1)  # torsion units of R
gate("|mu(R)| = 2 (the even-side torsion exhibit)", mu_R == 2)

print("D4 -- the axiom block's odd-reading census (per-token)")
absent = {"χ₋₃": 0, "conductor": 0, "pairing": 0, "Dirichlet": 0, "L(s": 0}
bad = {tok: block.count(tok) for tok, want in absent.items()
       if block.count(tok) != want}
gate("absent tokens: chi_-3, conductor, pairing, Dirichlet, L(s all zero",
     bad == {}, f"violations = {bad}")
n_char_word = len(re.findall(r"\bcharacter\b", block))
n_charisation = block.count("characterisation")
gate("'character' as a word: zero (two 'characterisation' tokens, A1 role note)",
     n_char_word == 0 and n_charisation == 2,
     f"word {n_char_word}, characterisation {n_charisation}")
n_odd_word = len(re.findall(r"\bodd\b", block))
gate("'odd' as a word: zero in the block", n_odd_word == 0, f"count {n_odd_word}")
gate("the block's chi tokens are A2's torsion constant (chi = 2 = |mu(R)|)",
     "χ = 2 | \\|μ(ℝ)\\|" in block and "χ·Γ(½)²" in block)
gate("ring side native: Q(zeta_3) and Z[omega] named; 'N_c = 3' exactly once",
     "ℚ(ζ₃)" in block and "ℤ[ω]" in block and block.count("N_c = 3") == 1)

print("D5 -- surface anchors (verbatim, failable)")
fals_p = ("any future derivation that routes a grammar entry through the odd "
          "bridge's L-side re-opens the member's derivational weight.")
fals_f = ("any future grammar entry routed through the odd bridge's L-side "
          "re-opens the member's weight.")
scope = "a census over the record, **not a universal over future derivations**"
ok5 = fals_p in npaper and fals_f in nform and scope in npaper
gate("both falsifier sentences + 1t's scope sentence verbatim", ok5)
ok6 = "unfired on both conjuncts (ring-side route; no" in npaper  # 1t(v) marker
ok6 &= "weight-for-numbers zero; the \"bookkeeping only\" reading persists" in npaper
ok6 &= "the tex papers consume the act nowhere, gated" in nform  # T1t marker
gate("the three net-state markers anchored (1t(v), 1s tail, T1t)", ok6)
ok7 = "unfired on both conjuncts" in npaper
ok7 &= "ring side native, L-side extrinsic" in npaper.replace("**", "")
ok7 &= "should any cascade paper ever carry a number via the act" in npaper.replace("**", "")
ok7 &= "confirmed and sharpened" in npaper.replace("**", "")
gate("1x's key sentences anchored (conjuncts; geography; sharpened falsifier)", ok7)

n_pass, n_fail = sum(results), len(results) - sum(results)
print(f"\nRESULT: {n_pass} pass / {n_fail} fail (16 gates)")
print("READING: Door-4 bookkeeping CONFIRMED post-1w. The falsifier is")
print("unfired (ring-side route; the tex papers consume the act nowhere);")
print("the zero-weight grading refines to zero-for-numbers (three")
print("review-side consumers, none carrying a number); the axiom block")
print("carries the ring side natively and zero odd-reading content --")
print("Door 4's asymmetry mirrored inside the axioms. The member")
print("persists charged; the sharpened papers-side falsifier is licensed.")
sys.exit(0 if n_fail == 0 else 1)
