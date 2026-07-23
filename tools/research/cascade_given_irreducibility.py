#!/usr/bin/env python3
"""THE GIVEN'S IRREDUCIBILITY CLASSIFICATION (Theorem 1u): the
regularity/coherence given adjudicated against the axioms'
committed content -- no committed route from A1-A4 reaches it, and
its subject matter lies off the lattice the axioms govern.
Category (a): text census over the committed axiom block plus
exact arithmetic; no data, no closures, no RH/GRH, no semiclassics
(Check 7); the hypothesis is nowhere an input (Check 8).

CONTEXT.  The 1p/1q arc left one given, in two equivalent faces
(per-label regularity; mirror coherence), with the open question:
derive it, either face, from A1-A4.  This file adjudicates that
question for the committed record.

  U1 THE AXIOMS CARRY ZERO LABELING CONTENT.  Token census over
     the formulation's "## 1. The axiom system" block (A1-A4, the
     canonical statement): sup/max/min, labeling, boundary side,
     parity, odd, mirror, regular, coheren-, and the label
     numerals -- ZERO hits (the block's lone "19" is the year in
     "Wall 1964", gated as such; the block's own selection
     vocabulary -- the A3 flags clause -- gated with per-token
     adjudication, round-94 F1, and LOCATION-gated round 95
     (F1/F2): source/constant/dynamics vocabulary, not label
     selection).  Disclosed adjudications: A2's
     home column names "the functional equation's symmetry point"
     as Gamma(1/2)'s arithmetic home -- provenance of a constant
     at the FIXED POINT s = 1/2, not an asserted condition at
     mirror points (anchored); A3 places source layers "at the
     analytic features of Gamma_R" and attaches "below the phase
     transition" -- feature POSITIONS and regions, not
     boundary-side integer choices (1k's committed distinction:
     what the lattice does not fix is the side).
  U2 THE GIVEN'S SUBJECT MATTER IS OFF-LATTICE.  A1's committed
     state space is "the descent lattice N (layer index d),
     weighted by Gamma_R" (anchored verbatim).  T1's four kernel
     primitives evaluate Gamma_R on the lattice's argument image
     {d+1, d+2} -- strictly positive integers (the T1 definitions
     anchored verbatim, round-94 F3; the positivity is an exhibit
     of the anchored offsets).  Both faces of the given evaluate
     Gamma_R at
     NEGATIVE arguments: gamma_oo(s) = Gamma_R(1-s)/Gamma_R(s)
     needs 1-s = -d <= 0, and the mirror weight 2/Gamma_R(-d)
     needs -d <= 0 (gated at the labels).  The axioms' asserted
     content quantifies over lattice points and their weights; no
     axiom asserts any condition at negative arguments.
     (Expressibility is not the issue -- classical analysis
     continues the weight function; what is missing is any
     axiom-asserted CONDITION there.)
  U3 THE LABELING'S SINGLE ENTRY POINT.  The committed chain
     routes the labeling through exactly one point: part0's
     variational definition, whose own remark grades the
     derivation open (anchored verbatim: "A principled derivation
     of max from the cascade's own axioms ... remains open"); 1k
     records "The sup itself is a second given" (anchored); the
     downstream consumers take the selected labels' OUTPUT
     (part5's 18 Omega_19 Omega_217 / pi^3, anchored) -- not a
     selection principle.  Scope: anchor-based on the committed
     grading statements, declared (not a fresh full-repo census;
     1t's census covers the consumption side).
  U4 THE FIVE COMMITTED FACES COINCIDE AND ARE EACH
     EXTRA-AXIOMATIC.  Re-gated compactly on the eight labelings:
     argmax I = argmin S_dS = the odd-member rule = the unique
     zeta-mirror-nonzero labeling = the unique coherent labeling
     = (7, 19, 217).  Type table (declared, backed by U1's
     census): max and min-S are extremal conventions (no axiom
     asserts a ranking over labelings); the odd-member rule is
     lattice-native but axiom-unbacked; zeta-rationality and
     regularity/coherence route through off-lattice values (the
     even and odd mirror sides).
  U5 THE CLASSIFICATION, THE TRANSFORMED QUESTION, AND THE
     FALSIFIER.  For the committed record: NO committed route
     derives the given from A1-A4, and every committed face
     either lacks axiom backing or constrains off-lattice values
     the axioms nowhere govern -- THE GIVEN IS IRREDUCIBLE
     RELATIVE TO A1-A4 AS COMMITTED.  This is a
     committed-record classification, NOT an in-principle
     impossibility proof (A1-A4 are informal; declared).  The
     open question TRANSFORMS: from "derive the given from
     A1-A4" to the foundational question of whether the weight
     function's global identity (the continuation and functional
     equation of Gamma_R) is axiom content -- i.e., whether A1's
     kernel is Gamma_R-on-the-lattice or Gamma_R entire.  That
     question is stated, not resolved.  Licensed falsifier,
     stopping-rule-gated: any future committed derivation
     routing the labeling through an axiom's asserted content
     re-opens the classification.  The given persists; no
     closure; no number changes.

ROUND-98 NET-STATE.  The transformed question was answered by the
owner: A1 is re-founded on Gamma_R as its full global object
("Gamma_R entire", the owner's phrase -- the function is
meromorphic) with mirror coherence as its selector clause
(Theorem 1v; Addendum 176), and the
labeling is now forced BY THE AMENDED AXIOM.  This file's
classification is therefore HISTORICAL -- it describes A1-A4 as
committed through round 97 (the classified block is embedded below
verbatim, and the census gates run on it, not on the live
formulation, whose amended A1 now carries the clause by design);
1u remains the recorded reason a forced labeling required
axiom-level content (round-98 F4 scoped the earlier "only route"
phrasing: 1u showed no derivation route exists from the old
axioms, not that this adoption is the unique axiom-level route).
"""

import itertools
import math
import os

import sympy as sp
from scipy.special import gammaln

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
PI = math.pi
PAIRS = [(6, 7), (19, 20), (217, 218)]
LABS = list(itertools.product(*PAIRS))
GAMMA_GRAM = 0.02108

# the classified object: A1-A4 as committed through round 97 (commit
# 6402a62), byte-exact -- the census below runs on THIS block; the live
# formulation's A1 carries the round-98 adoption by design:
HISTORICAL_BLOCK = "## 1. The axiom system\n\n**A1 (Arithmetic kernel).** The state space is the descent lattice ℕ (layer index d), weighted\nby Γ_ℝ; the dynamics is the unique Gaussian elastic action with bond compliance α(d)\n(uniqueness: papers' `rem:action-uniqueness`).\n\n**A2 (Local-constant calculus).** Every multiplicative factor attached to a descent is drawn\nfrom the local constants of the adelic structure:\n\n| Constant | Identity | Arithmetic home |\n|---|---|---|\n| χ = 2 | \\|μ(ℝ)\\| | torsion of the real units |\n| Γ(½) = √π | Γ_ℝ critical value | the functional equation's symmetry point |\n| 2π | χ·Γ(½)² | Tate's self-dual period at the real place |\n| ½ | half-argument of Γ_ℝ | the Gaussian, Tate's self-dual test function |\n| mod-8 grading | Brauer–Wall group BW(ℝ) ≅ ℤ/8 | graded Brauer group of the real place (Wall 1964) — the arithmetic avatar of Bott/Clifford periodicity |\n| N_c = 3 = 2^(v₂(12))−1 | Radon–Hurwitz count | a 2-adic invariant (value depends only on v₂) |\n| cos(π/6) | weight–root angle of ℤ[ω] | ring of integers of ℚ(ζ₃) |\n| phases i, ζ₈ | quaternionic frame, Bott | the cyclotomic tower ζ₂, ζ₃, ζ₄, ζ₈ |\n\n**A3 (Assignment rules).** Which constant attaches where: the source-selection flags (P, L, G)\nas ξ-occupancy functors; the increment rule (corrections attach once, at sub-lead); source\nlayers at the analytic features of Γ_ℝ; the per-Bott-period attachment below the phase\ntransition. *This is the load-bearing axiom.* Partial derivation exists (Addendum 12: the\nflags recovered 9/9 from ξ's factorization); the increment and per-period rules are underived.\n\n**A4 (Measurement).** Measurement records the typical value of a Gaussian mode (weight\ne^(±½) per measured mode — lemma S4, anchored by equipartition); projection is along root\nframes (lemma S5).\n\n"


def Om(d):
    return 2 * math.exp((d + 1) / 2 * math.log(PI) - gammaln((d + 1) / 2))


def GR(x):
    return sp.pi ** (-sp.Rational(x, 2)) * sp.gamma(sp.Rational(x, 2))


def main():
    print("=" * 74)
    print("THE GIVEN'S IRREDUCIBILITY CLASSIFICATION (Theorem 1u)")
    print("=" * 74)

    form = open(os.path.join(ROOT, "cascade-riemann-formulation.md"),
                encoding="utf-8").read()
    paper = open(os.path.join(ROOT, "riemann-indistinguishability.md"),
                 encoding="utf-8").read().replace("\n", " ")
    part0 = open(os.path.join(ROOT, "src", "cascade-series-part0.tex"),
                 encoding="utf-8").read().replace("\n", " ")
    part5 = open(os.path.join(ROOT, "src", "cascade-series-part5.tex"),
                 encoding="utf-8").read()

    # ---- U1: the axiom block's labeling-content census
    print()
    print("U1 the axiom block (as committed through round 97) carries")
    print("   zero labeling content -- historical census, round-98 note:")
    i0 = form.find("## 1. The axiom system")
    i1 = form.find("## 2. The theorems")
    ok1 = 0 < i0 < i1
    live_block = form[i0:i1]
    # round 98: the classification's object is the HISTORICAL block; the
    # live A1 carries the adoption (anchored as the net-state):
    block = HISTORICAL_BLOCK
    ok1 &= "re-founded on the Riemann kernel" in live_block
    ok1 &= "re-founded on the Riemann kernel" not in block
    toks = ["sup", "max", "min", "labeling", "labelling", "boundary side",
            "parity", "odd", "mirror", "regular", "coheren", "(7",
            "7, 19", "217", "5, 7"]
    hits = {tok: block.lower().count(tok) for tok in toks
            if block.lower().count(tok)}
    ok1 &= hits == {}
    # round-94 F1: the block DOES contain selection vocabulary -- the A3
    # flags clause -- so the census gates it with per-token adjudication
    # instead of omitting it; round-95 F1/F2 corrected and LOCATION-GATED
    # the per-item statements ("both in that clause's sentence" was false
    # -- the two flag hits sit in two different A3 sentences; and the
    # 'unique' location claim was true but ungated):
    bl = block.lower()
    a1_cl = block[block.find("**A1"):block.find("**A2")]
    a3_cl = block[block.find("**A3"):block.find("**A4")]
    ok1 &= bl.count("selection") == 1 and "source-selection flags" in block
    ok1 &= a3_cl.lower().count("flag") == 2 == bl.count("flag")
    #      both flag hits within A3 (its flags clause and its
    #      partial-derivation sentence), location-gated
    ok1 &= a1_cl.lower().count("unique") == 3 == bl.count("unique")
    ok1 &= "action-uniqueness" in a1_cl
    #      all three unique hits within A1's dynamics sentence,
    #      location-gated (dynamics, not labeling)
    # the block's lone label-like numeral is the Wall year:
    ok1 &= block.count("19") == 1 and "Wall 1964" in block
    # disclosed adjudications, anchored:
    ok1 &= "the functional equation's symmetry point" in block   # A2 home
    ok1 &= "at the analytic features of" in block                # A3
    # round-94 F4: the Notation section's xi functional equation is the
    # committed apparatus's nearest occurrence of the identity the
    # transformed question asks about -- notation, not axiom; anchored:
    form_head = form[:i0]
    ok1 &= "with ξ(s) = ξ(1−s)" in form_head                     # section 0
    ok1 &= "What the lattice does *not*\nfix is the **side**" \
        in open(os.path.join(ROOT, "riemann-indistinguishability.md"),
                encoding="utf-8").read() \
        or "What the lattice does *not* fix is the **side**" in paper
    print(f"   the A1-A4 block ({len(block)} chars) scanned: the 15 listed")
    print(f"   labeling tokens ZERO {hits}; the block's own selection")
    print("   vocabulary gated with adjudication (round-94 F1, location-")
    print("   gated round 95: 'selection' once, in 'source-selection")
    print("   flags'; 'flag' twice, both within A3; 'unique' thrice, all")
    print("   within A1's dynamics sentence -- constants, sources, and")
    print("   dynamics, not labels);")
    print("   the lone '19' is 'Wall 1964' (gated).  Disclosed: A2's home")
    print("   column names the functional equation's SYMMETRY POINT")
    print("   (provenance at the fixed point, not a mirror condition); A3")
    print("   places layers at FEATURES and regions (1k's side-vs-position")
    print("   distinction anchored); section 0's notation commits the xi")
    print("   functional equation -- notation, not axiom (round-94 F4,")
    print("   anchored)   " + ("PASS" if ok1 else "FAIL"))

    # ---- U2: the off-lattice dichotomy
    print()
    print("U2 the given's subject matter is off the axioms' lattice:")
    ok2 = "The state space is the descent lattice" in form
    # round-94 F3: the kernel's argument image is now pinned by
    # ANCHORING the committed T1 definitions (failable), with the
    # positivity arithmetic an exhibit of the anchored offsets (the
    # first draft's constructed lists were gates that could not fail):
    ok2 &= "Ω(d) = 2/Γ_ℝ(d+1)" in form               # T1 definitions
    ok2 &= "N(d) = Γ_ℝ(d+1)/Γ_ℝ(d+2)" in form
    ok2 &= "p(d) = (log Γ_ℝ)′(d+1)" in form
    ok2 &= "α(d) = N(d)²/4π" in form   # round-95 F3: all FOUR anchored
    #      (alpha adds no new Gamma_R argument -- it is N^2/4pi)
    # exhibit: for d in N, d+1 >= 1 and d+2 >= 2 (arithmetic of the
    # anchored offsets); the faces' arguments at the labels:
    face_args = [1 - (d + 1) for d in (7, 19, 217)]  # gamma_oo at the labels
    ok2 &= all(a <= 0 for a in face_args)            # exhibit (declared)
    w7 = sp.simplify(2 / GR(-7))
    ok2 &= w7 == sp.Rational(105, 8) / sp.pi ** 4    # the machinery is real
    print("   A1's state space anchored verbatim ('the descent lattice N');")
    print("   all four kernel T1 definitions anchored (round-94 F3; the")
    print("   alpha anchor round-95 F3 -- their argument image {d+1, d+2}")
    print("   is strictly positive, an exhibit of the anchored offsets);")
    print("   both faces evaluate Gamma_R at")
    print(f"   negative arguments at the labels (1-s = {face_args},")
    print("   exhibit; the d = 7 mirror weight 105/(8 pi^4) gated) -- no")
    print("   axiom asserted any condition there (pre-adoption axioms --")
    print("   the amended A1 now asserts the selector clause exactly")
    print("   there, round-98 F6; the T1-definition anchors run on the")
    print("   live formulation, T1 being unchanged by the adoption)   "
          + ("PASS" if ok2 else "FAIL"))

    # ---- U3: the single entry point (anchor-based, scope declared)
    print()
    print("U3 the labeling's single committed entry point:")
    ok3 = ("A principled derivation of max from the cascade's own axioms"
           in part0.replace("  ", " "))
    ok3 &= "The sup itself is a second given" in paper
    ok3 &= "18\\,\\Omega_{19}\\Omega_{217}/\\pi^3" in part5
    print("   part0's remark ('A principled derivation of max ... remains")
    print("   open'), 1k's 'The sup itself is a second given', and part5's")
    print("   output-consumption formula 18 Omega_19 Omega_217/pi^3 all")
    print("   anchored verbatim -- the labeling enters at the variational")
    print("   definition and is consumed downstream as output (anchor-")
    print("   based; 1t covers the consumption census)   "
          + ("PASS" if ok3 else "FAIL"))

    # ---- U4: the five faces coincide; each extra-axiomatic
    print()
    print("U4 the five committed faces coincide at the sup:")
    vals = {l: (Om(5) / Om(l[0])) ** 2 * Om(l[1]) * Om(l[2]) for l in LABS}
    sup = max(vals, key=vals.get)
    S = {l: 24 * PI ** 2 / ((2 / PI) * math.exp(GAMMA_GRAM) * vals[l])
         for l in LABS}
    smin = min(S, key=S.get)
    odd = tuple(x if x % 2 == 1 else y for x, y in PAIRS)
    zmir = [l for l in LABS if all(sp.zeta(-d) != 0 for d in l)]
    coh = [l for l in LABS if all(sp.simplify(2 / GR(-d)) != 0 for d in l)]
    ok4 = (sup == smin == odd == (7, 19, 217)
           and zmir == coh == [(7, 19, 217)])
    print(f"   argmax I = argmin S = odd rule = {sup}; the zeta-mirror and")
    print("   coherence survivors both uniquely the sup (re-gated).  Types")
    print("   (declared, backed by U1): max/min-S extremal conventions;")
    print("   odd-member lattice-native but axiom-unbacked; zeta-mirror")
    print("   and regularity/coherence off-lattice   "
          + ("PASS" if ok4 else "FAIL"))

    # ---- U5: the classification and the transformed question
    print()
    print("U5 the classification (grading in docstring):")
    ok5 = "or establish that the grammar never needs the odd reading" \
        in paper                                     # the 1s/1t chain stands
    ok5 &= "Mirror coherence is adopted, not derived" in part0
    ok5 &= "That choice has now been made" in part0  # the round-98
    #      adoption recorded at the same locus the openness anchor
    #      occupied (the round-94 F5 anchor superseded by the decision)
    print("   IRREDUCIBLE RELATIVE TO A1-A4 AS COMMITTED: no committed")
    print("   route, zero axiom labeling content (U1), the subject matter")
    print("   off-lattice (U2), every face extra-axiomatic (U4).  A")
    print("   committed-record classification, not an impossibility proof")
    print("   (declared).  The question TRANSFORMS: is the weight")
    print("   function's global identity axiom content?  Stated there,")
    print("   RESOLVED round 98 by the owner's adoption (docstring")
    print("   net-state; the falsifier's antecedent fired by adoption,")
    print("   not derivation)   " + ("PASS" if ok5 else "FAIL"))

    print()
    print("=" * 74)
    print("READING (census + gated; grading in docstring)")
    print("=" * 74)
    print("  The axioms as committed assert nothing about labelings,")
    print("  parities, mirrors, or rankings (U1); their state space is")
    print("  the lattice, and the given constrains the weight function")
    print("  where the lattice never reaches (U2); the labeling enters")
    print("  the chain once, at a definition graded 'adopted' (U3); and")
    print("  every committed face of the given is extra-axiomatic (U4).")
    print("  For the committed record the given is irreducible relative")
    print("  to A1-A4; the open question becomes foundational -- whether")
    print("  the continued weight function is axiom content -- RESOLVED")
    print("  round 98 by the owner's adoption (this file is historical;")
    print("  docstring net-state).  No closure; no number changes.")


if __name__ == "__main__":
    main()
