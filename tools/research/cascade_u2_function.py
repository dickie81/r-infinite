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
papers' Cabibbo proof, part4b:3727: "the overlap of two states, one
from each gauge layer").  With record-legs, the unchanged clauses
compute (0,0,0) on both angle rows and the availability question
closes -- conditional on the record-legs rule, which is disclosed
fixed-target and carries the registered PMNS falsifier (see the
CASES comment).  theta_23 and ell_A have no T4-stored availability
(neither is a T4 exhaustion stage -- the 11 rows are the 9 T4
stages plus these two), so their availability is unchecked.

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
discretionary content per row is the A13 grading plus the kind
assignment (ell_A's "mass-ratio" vs "local-ratio" is genuinely
ambiguous and load-bearing for R7's anchoring -- disclosed).

DISCLOSURES: assembled knowing the table (fixed-target); two soft
inputs (Observer k=3; the A13 grading); the kind field for ell_A.
Uniqueness: see cascade_u2_uniqueness.py (round-8 corrected state:
member-field uniqueness relative to the declared space; the
availability block has NO surviving variant set over the corrected
key -- the theta_C defect is open).
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
 # RECORD-LEGS CORRECTION (Addendum 61, resolving the theta_C
 # availability defect): the mixing angles' legs are the states the
 # observable READS, and the papers state these verbatim -- the
 # Cabibbo proof (part4b:3727): "A mixing-matrix element measures
 # the overlap of two states, ONE FROM EACH GAUGE LAYER"; theta_23
 # extends "the cascade Cabibbo template" through the same window.
 # The gauge-layer states are d=12,13; the generation layers never
 # enter either formula.  The rounds-8-12 encodings ((13,21) and
 # (5,13) quark) were the SM-side generation pairing -- what the
 # angle is ABOUT, not what it reads; that mislabel was the entire
 # source of the availability defect (computed (1,2,0) from label-
 # legs vs the T4-stored/formula (0,0,0)).  Identity-level rule,
 # uniform across rows: record-ratios read generation records
 # (tau/mu, mu/e, b/s, m_b/m_tau -- avail factors attach);
 # frame-rotations read gauge-layer states (theta_C, theta_23 --
 # no generation path, no factors).  Grading named per the pattern
 # rule: the uniform expression-tree reading of the canonical
 # formulas.  FIXED-TARGET DISCLOSURE: this reclassification was
 # made knowing the target; its defences are the papers' verbatim
 # proof language and a REGISTERED DISCRIMINATING PREDICTION -- any
 # future angle closure (PMNS theta_12/13/23) carrying a 2 sqrt(pi)
 # Bott factor or a colour factor falsifies the record-legs rule.
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
 "m_b/m_tau": dict(avail=(0, 2, 1), member=None),
 "m_tau abs": dict(avail=(0, 0, 0), member=("Descent", 19, 1, "+")),
 "ell_A":     dict(member=("Descent", 19, 1, "+")),
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
    print("  clauses now compute (0,0,0) on both angle rows.  Disclosed")
    print("  fixed-target; registered falsifier: any future PMNS-angle")
    print("  closure carrying a 2 sqrt(pi) or colour factor kills the")
    print("  record-legs rule.")
    print("  The withdrawn round-8 claims ('11/11 on all seven fields',")
    print("  '~60 entries -> ~30 facts', 'the sharpening was data-forced')")
    print("  stay withdrawn -- see the run record and Addenda 56-61.")


if __name__ == "__main__":
    main()
