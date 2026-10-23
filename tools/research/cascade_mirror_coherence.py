#!/usr/bin/env python3
"""MIRROR COHERENCE (Theorem 1q, as corrected round 79): an exact
equivalent reformulation of 1p's regularity principle -- the given
recast as non-degeneracy of the invariant under the ground object's
defining symmetry -- with the census, the adjudication convention,
and the equivalence all stated and gated.  Category (a): exact
symbolic arithmetic (sympy); no data, no closures, no RH/GRH, no
semiclassics (Check 7); the hypothesis is nowhere an input (Check 8).

CONTEXT.  Theorem 1p forced the sup from the REGULARITY PRINCIPLE
(labels at regular points of the local functional equation), a new
given.  This file restates that given on the invariant as a whole:

  - The ground object's defining symmetry: xi(s) = xi(1-s) --
    equivalently xi(1/2 + z) is EVEN in z (T1b's subject: 'xi(1/2+z)
    is even, entire of order 1, genus-0 in z^2, no constant term').
    ROUND-79 F1 CORRECTION (the docstring's first version swapped
    the subject): the evenness is xi's, NOT the paired Hadamard
    SUM's -- the sum Sigma 2z/(z^2 - (rho-1/2)^2) carries an
    explicit factor z and is ODD in z, and the full unconditional
    identity (pole terms, Dirichlet side) is not z^2-blind at all.
    What IS true and gated: the ground object xi assigns the SAME
    VALUE to layer d (z = d + 1/2) and its mirror -(d+1)
    (z' = -(d+1/2); same z^2) -- xi itself cannot distinguish them.
    The tower's weights CAN distinguish them; that is exactly what
    coherence probes.
  - The invariant is finite-nonzero on the physical branch (an
    invariant equal to 0 or oo is no invariant; part0's uniqueness
    theorem presupposes it).

THE MIRROR INVARIANT (Q2).  Branch-swap every weight:
Om~(d) = 2/Gamma_R(-d) (the mirror layer's weight; = Om(d) divided
by Tate's gamma-factor at s = d+1, tying to 1p).  Define
I~(l0, l1, l2) = (Om~(5)/Om~(l0))^2 Om~(l1) Om~(l2).  The census
over the eight labelings, HONESTLY CLASSIFIED (round-79 F2
correction -- the first version reported 'oo at all four l0 = 6
labelings', which is false at three of them):
  I~ finite-nonzero  UNIQUELY at (7, 19, 217) -- the sup;
  I~ = 0             at the three l0 = 7 labelings with an even
                     content label;
  I~ = oo            at (6, 19, 217) ONLY (denominator weight zero,
                     both content weights live);
  I~ INDETERMINATE   (0 * oo; no exact value exists) at the three
                     l0 = 6 labelings with an even content label.
ADJUDICATION (stated, not hidden): coherence means the defining
formula EVALUATES, exactly and unconditionally, to a finite nonzero
value.  Zero, infinite, and indeterminate all fail.  Under that
stated convention the sup is the unique survivor.  DISCLOSED
CONVENTION-DEPENDENCE (gated): under a uniform regularization
d -> d + eps the zero orders at (6, 20, 218) cancel and the LIMIT
is finite-nonzero (~ -1.413e123), while (6, 19, 218) and
(6, 20, 217) diverge -- so uniqueness holds for exact values of the
defining formula, NOT for regularized limits.

THE EQUIVALENCE (Q3; round-79 F3 correction).  Gamma_R never
vanishes, so Om~ is never oo: I~ has an exact finite-nonzero value
iff every constituent weight is nonzero iff every label is odd iff
every label is 1p-regular.  MIRROR COHERENCE IS EXTENSIONALLY
EQUIVALENT TO 1p'S PER-LABEL REGULARITY -- an exact, immediate
biconditional, gated as set equalities.  It is an EQUIVALENT
REFORMULATION with independent motivation (non-degeneracy under the
ground object's defining symmetry), NOT a strict narrowing: neither
side is logically smaller, 'derived' holds in both directions, and
the open question -- derive the given from A1-A4 -- is unchanged in
extension.  The first version's 'moves the given up one level /
one global statement replacing per-label applications' framing is
retracted (and its '2^3 applications, one per member of each
straddling pair' count was internally inconsistent -- 8 labelings
vs 6 members; 1p's own gate performed 3 pair-checks).

THE d_V CLAUSE (Q4, deflated per round-79 F7).  Om~ vanishes at
EVERY even d, so 'Om~(5) != 0' is exactly 'd_V is odd' -- 1n's
recorded parity fact re-expressed on the mirror weights, not a new
local discrimination.  Under coherence-as-postulate it is a
consistency requirement the fixed landmark (V's discrete argmax,
not a labeling choice) meets: Om~(5) = -15/(4 pi^3) exact,
Om~(4) = Om~(6) = 0.

SIGN AND VALUE (Q5).  I~_sup < 0: an exact rational over pi^117
(rationality now GATED -- round-79 F6; ~ -1.109e122); the mirror
weights carry Gamma-reflection signs; coherence is non-degeneracy
(!= 0, oo, indeterminate), not positivity.  No number changes; no
closure.
ROUND-98 NET-STATE.  The labeling given this file grades as open/
persisting was resolved by the owner's decision (Theorem 1v,
Addendum 176): A1 is re-founded on Gamma_R as its full global
object ("Gamma_R entire", the owner's phrase -- the function is
meromorphic) with mirror coherence as its selector clause, and the
labeling (7, 19, 217) is now forced by the amended axiom.  This file's grading
describes the pre-adoption state and is kept as record; its gates
are unchanged and remain green.
"""

import itertools
import os
import sys

import sympy as sp

PAIRS = [(6, 7), (19, 20), (217, 218)]
LABS = list(itertools.product(*PAIRS))


def GR(x):
    return sp.pi ** (-sp.Rational(x, 2)) * sp.gamma(sp.Rational(x, 2))


def GRe(x):
    """Gamma_R at a symbolic (shifted) argument."""
    return sp.pi ** (-x / sp.Integer(2)) * sp.gamma(x / sp.Integer(2))


def Om(d):
    return 2 / GR(d + 1)


def Omt(d):
    """The mirror layer's weight 2/Gamma_R(-d)."""
    return 2 / GR(-d)


def xi(s):
    """The completed zeta xi(s) = (1/2)s(s-1)pi^(-s/2)Gamma(s/2)zeta(s)."""
    s = sp.sympify(s)
    return (sp.Rational(1, 2) * s * (s - 1) * sp.pi ** (-s / 2)
            * sp.gamma(s / 2) * sp.zeta(s))


def classify(l0, l1, l2):
    """Exact-value classification of I~ at a labeling (round-79 F2)."""
    den = sp.simplify(Omt(l0))
    nz = [d for d in (l1, l2) if sp.simplify(Omt(d)) == 0]
    if den == 0 and nz:
        return "INDETERMINATE"        # 0 * oo: no exact value exists
    if den == 0:
        return "INF"
    if nz:
        return "ZERO"
    return "finite-nonzero"


def Itilde(l0, l1, l2):
    assert classify(l0, l1, l2) == "finite-nonzero"
    return sp.simplify((Omt(5) / Omt(l0)) ** 2 * Omt(l1) * Omt(l2))


def main():
    print("=" * 74)
    print("MIRROR COHERENCE (Theorem 1q, as corrected round 79)")
    print("=" * 74)

    # ---- Q1: the ground object's mirror pairing (xi's evenness)
    print()
    print("Q1 the ground object cannot distinguish layer from mirror:")
    ok1 = all(sp.Rational(2 * d + 1, 2) ** 2
              == (sp.Rational(1, 2) - (d + 1)) ** 2
              for d in range(0, 31))
    ok1 &= sp.simplify(xi(8) - xi(-7)) == 0        # layer 7 vs mirror -8
    ok1 &= sp.simplify(xi(8) - sp.Rational(4, 225) * sp.pi ** 4) == 0
    ok1 &= sp.simplify(xi(20) - xi(-19)) == 0      # layer 19 vs mirror -20
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "..", "..")
    paper = open(os.path.join(root, "riemann-indistinguishability.md"),
                 encoding="utf-8").read()
    # T1b-unique anchor (round-79 F5: the old substring 'genus-0 in z'
    # lacked the square and was satisfied by 1q's own quote; this one
    # occurs only in T1b's sentence, whose subject is xi(1/2+z)):
    ok1 &= paper.count("genus-0 in z², no constant term") == 1
    print("   z(d)^2 = z(-(d+1))^2 exactly (d = 0..30); xi's evenness gated")
    print("   at exact instances: xi(8) = xi(-7) = 4 pi^4/225,")
    print("   xi(20) = xi(-19) (layer/mirror pairs for labels 7, 19).")
    print("   Round-79 F1 stated: the evenness is xi's (T1b's subject,")
    print("   anchored via the T1b-unique substring, count gated == 1);")
    print("   the paired Hadamard SUM is odd in z and the identity is")
    print("   not z^2-blind   " + ("PASS" if ok1 else "FAIL"))

    # ---- Q2: the honest census + the adjudication + the disclosure
    print()
    print("Q2 the mirror invariant's census (exact-value classification):")
    census = {l: classify(*l) for l in LABS}
    ok_set = [l for l, t in census.items() if t == "finite-nonzero"]
    ok2 = (ok_set == [(7, 19, 217)]
           and census[(6, 19, 217)] == "INF"
           and sorted(l for l, t in census.items()
                      if t == "INDETERMINATE")
           == [(6, 19, 218), (6, 20, 217), (6, 20, 218)]
           and sorted(l for l, t in census.items() if t == "ZERO")
           == [(7, 19, 218), (7, 20, 217), (7, 20, 218)])
    # the disclosed convention-dependence, gated: eps-limits
    e = sp.symbols('e', positive=True)

    def lim(l):
        expr = ((2 / GRe(-5 - e)) / (2 / GRe(-l[0] - e))) ** 2 \
            * (2 / GRe(-l[1] - e)) * (2 / GRe(-l[2] - e))
        return sp.limit(sp.simplify(expr), e, 0, '+')

    l_a = lim((6, 19, 218))
    l_b = lim((6, 20, 217))
    l_c = lim((6, 20, 218))
    ok2 &= (not l_a.is_finite) and (not l_b.is_finite)
    ok2 &= l_c.is_finite and l_c != 0 \
        and abs(float(l_c) / -1.4132310693737173e+123 - 1) < 1e-9
    print("   finite-nonzero UNIQUELY at (7, 19, 217); ZERO at the three")
    print("   l0 = 7 labelings with an even content label; oo at")
    print("   (6, 19, 217) ONLY; INDETERMINATE (0*oo, no exact value) at")
    print("   the other three l0 = 6 labelings -- round-79 F2's corrected")
    print("   census.  Adjudication stated: coherence = the formula")
    print("   EVALUATES to a finite nonzero value.  Disclosed and gated:")
    print("   under d -> d+eps the (6,20,218) LIMIT is finite-nonzero")
    print("   (~ -1.413e123) while the other two diverge -- uniqueness")
    print("   holds for exact values, not regularized limits   "
          + ("PASS" if ok2 else "FAIL"))

    # ---- Q3: the exact equivalence with 1p (round-79 F3)
    print()
    print("Q3 mirror coherence == 1p's regularity (exact biconditional):")
    coh = ok_set
    odd_sel = [tuple(x if x % 2 == 1 else y for x, y in PAIRS)]
    reg = [l for l in LABS if all(sp.simplify(Omt(d)) != 0 for d in l)]
    never_inf = all(sp.simplify(GR(-d)) != 0 for d in range(0, 31))
    ok3 = never_inf and coh == odd_sel == reg == [(7, 19, 217)]
    print("   Gamma_R never vanishes (gated d = 0..30), so Om~ is never oo:")
    print("   coherent = all-odd = 1p-regular = " + str(coh) + " -- an")
    print("   exact, immediate biconditional.  Mirror coherence is an")
    print("   EQUIVALENT REFORMULATION of the regularity principle (with")
    print("   independent motivation), NOT a strict narrowing: the open")
    print("   question is unchanged in extension   "
          + ("PASS" if ok3 else "FAIL"))

    # ---- Q4: the d_V clause (parity, deflated per round-79 F7)
    print()
    print("Q4 the fixed landmark's clause (= 1n's parity fact, restated):")
    w5 = sp.simplify(Omt(5))
    ok4 = w5 == sp.Rational(-15, 4) / sp.pi ** 3 and w5 != 0
    ok4 &= sp.simplify(Omt(4)) == 0 and sp.simplify(Omt(6)) == 0
    ok4 &= all((sp.simplify(Omt(d)) == 0) == (d % 2 == 0)
               for d in range(0, 31))
    print("   Om~(5) = -15/(4 pi^3) != 0 (exact); Om~ vanishes at EVERY")
    print("   even d (gated d = 0..30), so the content is exactly 'd_V is")
    print("   odd' -- 1n's recorded parity fact on the mirror weights, not")
    print("   a new local discrimination.  Under coherence-as-postulate it")
    print("   is a consistency requirement the fixed landmark (V's argmax,")
    print("   not a labeling choice) meets   " + ("PASS" if ok4 else "FAIL"))

    # ---- Q5: the exact value, the sign, rationality, and the 1p tie
    print()
    print("Q5 the coherent value: sign, structure (gated), and the 1p tie:")
    v = Itilde(7, 19, 217)
    ok5 = v != 0 and v != sp.oo and v.is_negative
    ok5 &= sp.simplify(v * sp.pi ** 117).is_rational is True  # round-79 F6
    # (a former "definition sanity" conjunct Omt(7)*GR(-7) == 2 was removed
    # round 80 (c1): tautological by Omt's definition -- a gate that cannot
    # fail; Q5's three printed claims are each gated by the real checks.)
    gamma8 = sp.simplify(GR(-7) / GR(8))              # 1p's gamma at s=8
    ok5 &= sp.simplify(Omt(7) - Om(7) / gamma8) == 0  # Om~ = Om/gamma tie
    print("   I~_sup * pi^117 is an exact rational, GATED (~"
          + f"{float(v):.3e}), NEGATIVE:")
    print("   the mirror weights carry Gamma-reflection signs; coherence")
    print("   is NON-DEGENERACY (!= 0, oo, indeterminate), not positivity.")
    print("   The 1p tie gated: Om~(d) = Om(d)/gamma_oo(d+1) at d = 7   "
          + ("PASS" if ok5 else "FAIL"))

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  The ground object xi assigns the same value to a layer and")
    print("  its mirror; the tower's weights do not.  Requiring the")
    print("  invariant's standing non-degeneracy to hold for the")
    print("  branch-swapped weights -- MIRROR COHERENCE -- selects the sup")
    print("  as the unique labeling where the mirrored formula evaluates")
    print("  to a finite nonzero value (adjudication and regularized-limit")
    print("  caveat stated and gated).  The condition is EXTENSIONALLY")
    print("  EQUIVALENT to 1p's per-label regularity: an equivalent")
    print("  reformulation with independent motivation, not a narrowing.")
    print("  The open question is unchanged: derive the given (either")
    print("  face) from A1-A4.  No number changes; no closure.")
    # round-123 hardening (the A206/A208 standing commission): exit
    # gating added -- this instrument previously exited 0
    # unconditionally, so a printed FAIL could not fail a caller;
    # the exit code now carries the verdicts.  No verdict logic
    # changed.
    n_fail = sum(0 if ok else 1 for ok in (ok1, ok2, ok3, ok4, ok5))
    print()
    print(f"RESULT: {5 - n_fail} pass / {n_fail} fail (5 verdicts)")
    sys.exit(0 if n_fail == 0 else 1)


if __name__ == "__main__":
    main()
