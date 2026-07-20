#!/usr/bin/env python3
"""
U2 AS A FUNCTION (v1, corrected per hostile review rounds 8-11): the
address table computed from identity facts -- with its failures
recorded, not hidden.

THE DEMAND (correct, and the hypothesis's own): if the universe is
zeta-driven, availability/flags/sources/channel-counts cannot be
tabulated facts -- they must be computed from each observable's bare
identity.  This file composes the papers' scattered rules into one
map and tests it binarily against the stored table.

INPUT per observable -- identity facts only (what the observable IS):
  legs      : the particle endpoints (generation layer, quark|lepton|gauge)
  content   : the formula's Phi/p support (summand range), split into
              NOVEL vs inherited by the A13 grading rule
  kind      : coupling | mass-ratio | abs-mass | local-ratio | density
              | overlap
  dim       : carries a scale (dimensionful), or has a Planck-anchored
              constituent

THE A13 GRADING RULE, applied CONSISTENTLY (round-8 fix): "sub-leads
enter raw, corrections attach once per observable, and the flags read
the increment over the maximal closed sub-lead" + "G counts full-
weight window exponentials only" (Addendum 13).  Consequences:
  - b/s        novel=None (window (6,13) arrives inside closed
               sub-lead L(tau/mu))
  - m_tau abs  novel=None (its Phi(5,12) content arrives inside the
               closed sub-leads alpha_s and v).  NOTE (round-10
               Major-4 fix): a round-8 remark here claimed "A52's
               vacuity finding stands as a statement about the
               papers' table."  It does NOT stand -- round 9 (M3)
               showed A52's (T,F,T) dash-fill for m_tau-abs expanded
               closed constituents against the papers' expression-
               tree predicate; corrected A52 grades m_tau-abs
               primary (T,F,F), the precedence is vacuous on uniform
               readings, and the anchoring is variant-conditional
               (see the R7 clause below, which already said so --
               this note lagged it).
  - theta_C    novel=None (its exp(-p(13)/2) is HALF-weight, exactly
               like theta_23's exempted exponential; the prior
               novel=13 encoding was inconsistent with A13 and
               manufactured both v1's "first-run failure" and the
               exhaustion's theta_C kill of the pre-fix G reading)
  - theta_23   novel=None (half-weight window, A13's original case)

THE CLAUSES (all remain stipulations sourced to the papers; the
first-principles companion script proposes groundings at argument
strength only):
  R1 obstruction  = |g2-g1|/8 between leg generations
  R2 colour rank  = 2 if any quark leg, else 0
  R3 projection   = 1 if legs mix quark and lepton, else 0
  R4 flag P       = dim
  R5 flag G       = novel content is a window whose summand range
                    begins strictly below the U(1) layer 14 and
                    reaches the gauge band: lo < 14 and hi >= 12.
                    This is the papers' STRICT-BOUNDARY STIPULATION
                    (part4b:503 "The m_mu/m_e path d=14..21 begins
                    at the U(1) layer and does not receive the
                    shift"; flagged Conditional at part4b 4108(a)).
                    It is NOT a support theorem: the summand set of
                    the mu/e path INCLUDES p(14) (part4b:83), so no
                    faithful interval-support reading exempts it --
                    only the boundary stipulation does (round-8 fix;
                    the earlier "half-open support (a,b]" account
                    double-shifted the summand ranges and is
                    retracted).
  R6 flag L       = kind in {local-ratio, density}
  R7 type/source  = decision order P>L>G -> Absolute 19 | Observer 5
                    | Gauge 14 | Amplitude 7.  Within THIS grading no
                    realized row has two true flags, so the order is
                    unpinned here.  ROUND-9 (M3): A52's dash-fill for
                    m_tau-abs (G=T via expanding the closed
                    constituents alpha_s and v) violated the papers'
                    own expression-tree predicate (part4b
                    rem:sp36-syntactic -- b/s's L(tau/mu) stays a
                    closed symbol, G=F, by exactly that convention).
                    Under the uniform mechanical reading no row is
                    multi-flag at the papers' layer either: the
                    precedence is VACUOUS on primary readings, and
                    the 13-109 sigma anchoring is CONDITIONAL on
                    constituent-expansion variant readings (A52
                    corrected, Addendum 57).
  R8 population   = Geometric if density; Amplitude if overlap;
                    else Descent  -> sign by T7 (+/-/-)
  R9 channel k    = 1 if type in {Absolute, Gauge};
                    3 if type Observer  [SOFT: the papers' three-
                    factor statement, not composed here];
                    2 x (Bott periods touched by FULL content) if
                    Amplitude (papers' channel-count theorem,
                    part4b rem:theta23-channel-count)
  R10 member      = None (Family B radiative) if no flag is true AND
                    population is Descent; else the alpha(d*)/chi^k
                    member

THE THETA_C AVAILABILITY DEFECT -- HISTORY AND RESOLUTION: rounds
8-12 carried this as an open failure (computed (1,2,0) from quark
legs vs the T4-stored/formula (0,0,0); the row was left FAILING so
the defect stayed visible; the round-9 "mass-lead-only domain"
overreach was softened to an open question).  Addendum 61 resolved
it at the IDENTITY-FACT level, not the clause level: the failing
input was the legs encoding, which had recorded the SM-side
generation pairing instead of the states the observable reads (the
papers' Cabibbo proof, part4b:3728, verbatim for theta_C; theta_23
by template-extension inference -- round-13 m5).  With record-legs,
the unchanged clauses compute (0,0,0) on both angle rows and the
availability question closes -- conditional on the record-legs rule
(a new per-row classifier, soft input), on the audit-lemma corpus
reading of m_b/m_tau's projection rank (round-13 M4, see the EXPECT
comment), and subject to the sharpened PMNS falsifier (see the
CASES comment).  Both angle rows and ell_A are now checked as
formula-borne (0,0,0) alongside the T4-stored rows (theta_23 and
ell_A are not T4 exhaustion stages -- the 11 rows are the 9 T4
stages plus these two -- so their key values are formula-borne, not
T4-stored; round-13 M1/n11 replaced the earlier "unchecked" state).

RUN RECORD (corrected): v1's original first run failed on theta_C's
member because theta_C was graded novel=13 against A13's half-weight
exemption; the "window-only sharpening" of the G clause then made the
row pass.  Round 8 showed the grading, not the clause, was at fault:
under the consistent grading the unsharpened clause also passes every
realized row, so the sharpening distinguishes nothing on-domain and
the earlier "data-forced sharpening" claim is withdrawn.  A separate
round-8 finding (F1): the stored theta_23 answer key was WRONG (k=2
against the papers' k=4, part4b thm:theta23-closure "exp(-alpha(7)/
chi^4)" and rem:theta23-channel-count "theta_23 path d=12..20: spans
{P_1,P_2}. k=4"), with legs and full-content bent to match -- the
row now carries the papers' values and passes for the right reason.

WHAT THE COLLAPSE IS NOT (round 8, review F9): counting scalars, the
identity-fact table (76) is LARGER than the stored-output table (50).
The claim "~60 entries -> ~30 facts" is withdrawn.  The residual
claim is structural only: the ten clauses are SHARED across rows
(one rule-set, no per-row exceptions on member fields), and the
discretionary content per row is the A13 grading, the kind
assignment (ell_A's "mass-ratio" vs "local-ratio" is genuinely
ambiguous and load-bearing for R7's anchoring -- disclosed), and
the record-legs classification (record-ratio vs frame-rotation;
added round 13, n10).

DISCLOSURES: assembled knowing the table (fixed-target); soft
inputs: Observer k=3; the A13 grading; the ell_A kind; the
record-legs classification (Addendum 61, round-13 restated).
Uniqueness: see cascade_u2_uniqueness.py (rounds 8-13 state:
member-field uniqueness relative to the declared space; the
availability block has 6 survivors under the record-legs encoding
-- canonical + two extensional duplicates + the cross-generation-
indicator fork (off-domain, probe P1) -- with the R3 projection
pinning conditional on the audit-lemma corpus, round-13 M4).
"""

GAUGE = (12, 14)


def bott_period(d):
    """Papers' Bott-period convention (part4b rem:theta23-channel-count
    'using n=d-1'; implemented identically in the papers' own verifier
    cascade_channel_count_rule.py): P_k = {d : 8k+1 <= d <= 8k+8},
    i.e. (d-1)//8.  P_0 = d 1..8, P_1 = 9..16, P_2 = 17..24.

    ROUND-9 FIX (M1): the prior local PERIODS=[(5,12),(13,20),(21,28)]
    was NOT the papers' convention, and under it no uniform content
    rule reproduced both theta_C's k=2 and theta_23's k=4 -- the rows
    were encoded with opposite conventions (p-support vs path), each
    the one that matched the stored k.  Under the papers' periods a
    UNIFORM encoding (content = p-summand range) reproduces both."""
    return (d - 1) // 8


def periods_touched(content):
    if content is None:
        return 0
    lo, hi = content if isinstance(content, tuple) else (content, content)
    return len({bott_period(d) for d in range(lo, hi + 1)})


def u2(name, legs, novel, full, kind, dim):
    gens = [g for g, k in legs if k in ("quark", "lepton")]
    obstr = abs(gens[0] - gens[1]) // 8 if len(gens) == 2 else 0
    colour = 2 if any(k == "quark" for _, k in legs) else 0
    proj = 1 if {"quark", "lepton"} <= {k for _, k in legs} else 0
    P = dim
    if novel is None or not isinstance(novel, tuple):
        G = False          # no novel content, or a point normalisation
    else:
        lo, hi = novel
        G = lo < hi and lo < GAUGE[1] and hi >= GAUGE[0]
    L = kind in ("local-ratio", "density")
    if P:
        typ, src = "Absolute", 19
    elif L:
        typ, src = "Observer", 5
    elif G:
        typ, src = "Gauge", 14
    else:
        typ, src = "Amplitude", 7
    pop = ("Geometric" if kind == "density" else
           "Amplitude" if kind == "overlap" else "Descent")
    sign = "+" if pop == "Descent" else "-"
    k = (1 if typ in ("Absolute", "Gauge") else
         3 if typ == "Observer" else 2 * periods_touched(full))
    member = None if (not (P or L or G) and pop == "Descent") \
        else (pop, src, k, sign)
    return dict(avail=(obstr, colour, proj), member=member)


# identity facts (legs / novel content / full content / kind / dim)
# gradings per the consistent A13 rule -- see docstring
CASES = [
 ("alpha_s",   [(12, "gauge")],                 (5, 12), (5, 12), "coupling",    False),
 ("tau/mu",    [(5, "lepton"), (13, "lepton")], (6, 13), (6, 13), "mass-ratio",  False),
 ("mu/e",      [(13, "lepton"), (21, "lepton")],(14, 21),(14, 21),"mass-ratio",  False),
 ("b/s",       [(5, "quark"), (13, "quark")],   None,    (6, 13), "overlap",     False),
 ("m_b/m_tau", [(5, "quark"), (5, "lepton")],   None,    None,    "mass-ratio",  False),
 ("m_tau abs", [(5, "lepton")],                 None,    (5, 12), "abs-mass",    True),
 ("ell_A",     [],                              None,    None,    "mass-ratio",  True),
 ("sin2thW",   [(13, "gauge"), (14, "gauge")],  None,    None,    "local-ratio", False),
 ("Omega_m",   [],                              None,    None,    "density",     False),
 # RECORD-LEGS CORRECTION (Addendum 61, restated per round 13 --
 # the rule survives WOUNDED, A62): the mixing angles' legs are the
 # states the observable READS.  Papers status BY ROW (round-13 m5):
 # for theta_C this is VERBATIM -- the Cabibbo proof (part4b:3728):
 # "A mixing-matrix element measures the overlap of two states, ONE
 # FROM EACH GAUGE LAYER"; for theta_23 it is TEMPLATE-EXTENSION
 # INFERENCE (thm:theta23-closure says only "the cascade Cabibbo
 # template extended to a multi-step descent"; the papers nowhere
 # state theta_23's states are gauge-layer states).  The generation
 # coset enters both formulas only at d=13 QUA GAUGE LAYER -- the
 # d=13 dual identity (Gen-2 layer = SU(2) layer) is exactly the
 # disputed point (round-13 m6; the rounds-8-12 encoding read d=13
 # qua generation record).  The old encodings ((13,21)/(5,13)
 # quark) were the SM-side pairing -- what the angle is ABOUT.
 # THE CLASSIFIER IS A NEW PER-ROW INPUT (round-13 attack A): the
 # record-ratio vs frame-rotation split is not determined by any
 # existing field (b/s and theta_C share kind="overlap" yet get
 # opposite leg semantics); it is formula-sourced (grading: uniform
 # expression-tree reading) and counted in the soft-input list.
 # HONEST SCOPE (round 13): with record-legs the angle rows'
 # availability agreement is NEAR-TAUTOLOGICAL (legs read off the
 # formulas whose factor content the output is checked against);
 # the non-trivial content is clause-uniformity across the four
 # record-ratio rows, the theta_C verbatim quote, and the
 # falsifier.  FIXED-TARGET DISCLOSURE: made knowing the target.
 # REGISTERED FALSIFIER (sharpened, round-13 m7): no future
 # angle-type closure (PMNS theta_12/13/23) may carry an
 # AVAILABILITY factor -- 2 sqrt(pi), e^(r/2) colour, or cos(pi/6)
 # projection.  N_c-normalizations are not availability factors
 # under the U2 grammar, BUT the repo's standing PMNS candidates
 # (cascade_pmns_mixing_angle_proposal.py: N_c in all three
 # formulas) are disclosed as adjacent standing evidence, and A14
 # records e-vs-N_c as a scheme question: if a promoted PMNS
 # closure's N_c is shown scheme-equivalent to the colour factor
 # e^(r/2), the rule dies.
 ("theta_C",   [(12, "gauge"), (13, "gauge")],  None,    13,      "overlap",     False),
 # theta_23: content = p-summand range 13..20 (part4b:3921), spans
 # P_1,P_2 under the papers' periods -> k=4; SM-side pairing gen 2-3
 ("theta_23",  [(12, "gauge"), (13, "gauge")],  None,    (13, 20),"overlap",     False),
]

# the answer key: member fields from the papers' closure theorems;
# availability from the T4 store (cascade_T4_uniqueness.py) where it
# exists.  theta_23 / ell_A availability: no T4 store -> unchecked.
EXPECT = {
 "alpha_s":   dict(avail=(0, 0, 0), member=("Descent", 14, 1, "+")),
 "tau/mu":    dict(avail=(1, 0, 0), member=("Descent", 14, 1, "+")),
 "mu/e":      dict(avail=(1, 0, 0), member=None),
 "b/s":       dict(avail=(1, 2, 0), member=("Amplitude", 7, 4, "-")),
 # m_b/m_tau proj=1 CORPUS DISCLOSURE (round-13 M4): the papers'
 # Tier-4a entry is "m_b/m_tau = e" with NO projection factor
 # anywhere in the papers' TeX; the proj=1 witness is the audit's
 # Addendum-19 CANDIDATE LEMMA m_b = m_tau * e * cos(pi/6)
 # (candidate grade, scheme-contingent, PDG convention).  The key
 # row keeps the T4-store/audit corpus value; under a papers-only
 # corpus this row would be (0,2,0) and the R3 projection clause
 # would FAIL here exactly as the old clauses failed on theta_C.
 # The R3 pinning is therefore conditional on the audit-lemma
 # reading; disclosed, not silently chosen.
 "m_b/m_tau": dict(avail=(0, 2, 1), member=None),
 "m_tau abs": dict(avail=(0, 0, 0), member=("Descent", 19, 1, "+")),
 # ell_A avail: formula-borne (the closure carries no availability
 # factors), added round 13 (n11) for consistent treatment
 "ell_A":     dict(avail=(0, 0, 0), member=("Descent", 19, 1, "+")),
 "sin2thW":   dict(avail=(0, 0, 0), member=("Descent", 5, 3, "+")),
 "Omega_m":   dict(avail=(0, 0, 0), member=("Geometric", 5, 3, "-")),
 "theta_C":   dict(avail=(0, 0, 0), member=("Amplitude", 7, 2, "-")),
 # theta_23 avail: formula-borne (thm:theta23-closure carries no
 # 2 sqrt(pi) and no colour factor), not T4-stored
 "theta_23":  dict(avail=(0, 0, 0), member=("Amplitude", 7, 4, "-")),
}


def main():
    print("=" * 74)
    print("U2 AS A FUNCTION (v1, rounds 8-11 corrected): computed vs stored")
    print("=" * 74)
    npass = nfail = 0
    for name, legs, novel, full, kind, dim in CASES:
        got = u2(name, legs, novel, full, kind, dim)
        exp = EXPECT[name]
        msgs = [f"{key}: computed {got[key]} != stored {exp[key]}"
                for key in exp if got[key] != exp[key]]
        status = "PASS" if not msgs else "FAIL"
        npass += not msgs
        nfail += bool(msgs)
        print(f"  {status}  {name:<11} computed avail={got['avail']}"
              f" member={got['member']}")
        for m in msgs:
            print(f"         ** {m}")
    print()
    print("=" * 74)
    print(f"RESULT: {npass}/{npass+nfail} rows against the corrected key")
    print("=" * 74)
    print("  MEMBER fields: one shared rule-set, no per-row exceptions,")
    print("  uniform content encoding under the papers' period convention")
    print("  (round-9 M1).")
    print("  AVAILABILITY: the rounds-8-12 theta_C defect is RESOLVED at")
    print("  the identity-fact level (Addendum 61): the angles' legs are")
    print("  the gauge-layer states they read (papers' Cabibbo proof,")
    print("  'one from each gauge layer'), not the SM-side generation")
    print("  pairing mislabeled as legs in rounds 8-12.  Unchanged")
    print("  clauses now compute (0,0,0) on both angle rows.  Round-13")
    print("  restated (WOUNDED, A62): verbatim for theta_C only; the")
    print("  classifier is a new per-row soft input; the angle rows'")
    print("  agreement is near-tautological; sharpened falsifier: no")
    print("  future PMNS-angle closure may carry an AVAILABILITY factor")
    print("  (2 sqrt(pi), e^(r/2), cos(pi/6)); the repo's N_c-bearing")
    print("  PMNS candidates are disclosed adjacent evidence (A14")
    print("  e-vs-N_c scheme note).")
    print("  The withdrawn round-8 claims ('11/11 on all seven fields',")
    print("  '~60 entries -> ~30 facts', 'the sharpening was data-forced')")
    print("  stay withdrawn -- see the run record and Addenda 56-61.")


if __name__ == "__main__":
    main()
