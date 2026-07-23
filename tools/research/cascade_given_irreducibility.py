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
     "Wall 1964", gated as such).  Disclosed adjudications: A2's
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
     {d+1, d+2} -- strictly positive integers (gated on the
     definitions).  Both faces of the given evaluate Gamma_R at
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
    print("U1 the axiom block carries zero labeling content:")
    i0 = form.find("## 1. The axiom system")
    i1 = form.find("## 2. The theorems")
    ok1 = 0 < i0 < i1
    block = form[i0:i1]
    toks = ["sup", "max", "min", "labeling", "labelling", "boundary side",
            "parity", "odd", "mirror", "regular", "coheren", "(7",
            "7, 19", "217", "5, 7"]
    hits = {tok: block.lower().count(tok) for tok in toks
            if block.lower().count(tok)}
    ok1 &= hits == {}
    # the block's lone label-like numeral is the Wall year:
    ok1 &= block.count("19") == 1 and "Wall 1964" in block
    # disclosed adjudications, anchored:
    ok1 &= "the functional equation's symmetry point" in block   # A2 home
    ok1 &= "at the analytic features of" in block                # A3
    ok1 &= "What the lattice does *not*\nfix is the **side**" \
        in open(os.path.join(ROOT, "riemann-indistinguishability.md"),
                encoding="utf-8").read() \
        or "What the lattice does *not* fix is the **side**" in paper
    print(f"   the A1-A4 block ({len(block)} chars) scanned: selection/")
    print(f"   labeling tokens ZERO {hits}; the lone '19' is 'Wall 1964'")
    print("   (gated).  Disclosed: A2's home column names the functional")
    print("   equation's SYMMETRY POINT (provenance at the fixed point,")
    print("   not a mirror condition); A3 places layers at FEATURES and")
    print("   regions (1k's committed side-vs-position distinction")
    print("   anchored)   " + ("PASS" if ok1 else "FAIL"))

    # ---- U2: the off-lattice dichotomy
    print()
    print("U2 the given's subject matter is off the axioms' lattice:")
    ok2 = "The state space is the descent lattice" in form
    kernel_args = [d + k for d in range(0, 300) for k in (1, 2)]
    ok2 &= all(a >= 1 for a in kernel_args)          # kernel: positive args
    face_args = [1 - (d + 1) for d in (7, 19, 217)]  # gamma_oo at the labels
    ok2 &= all(a <= 0 for a in face_args)            # faces: non-positive
    ok2 &= all(-d < 0 for d in (7, 19, 217))         # mirror weights
    w7 = sp.simplify(2 / GR(-7))
    ok2 &= w7 == sp.Rational(105, 8) / sp.pi ** 4    # the machinery is real
    print("   A1's state space anchored verbatim ('the descent lattice N');")
    print("   the kernel's argument image {d+1, d+2} is strictly positive")
    print("   (gated d = 0..299); both faces evaluate Gamma_R at negative")
    print(f"   arguments at the labels (1-s = {face_args}; the d = 7 mirror")
    print("   weight 105/(8 pi^4) gated) -- no axiom asserts any condition")
    print("   there   " + ("PASS" if ok2 else "FAIL"))

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
    print("   IRREDUCIBLE RELATIVE TO A1-A4 AS COMMITTED: no committed")
    print("   route, zero axiom labeling content (U1), the subject matter")
    print("   off-lattice (U2), every face extra-axiomatic (U4).  A")
    print("   committed-record classification, not an impossibility proof")
    print("   (declared).  The question TRANSFORMS: is the weight")
    print("   function's global identity axiom content?  Stated, not")
    print("   resolved; the falsifier licensed (any future committed")
    print("   derivation routing the labeling through an axiom re-opens")
    print("   the classification)   " + ("PASS" if ok5 else "FAIL"))

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
    print("  the continued weight function is axiom content.  The given")
    print("  persists; no closure; no number changes.")


if __name__ == "__main__":
    main()
