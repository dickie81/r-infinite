#!/usr/bin/env python3
"""
U2 FIRST-PRINCIPLES RECONSTRUCTION (round-8 corrected: proposed
groundings at ARGUMENT strength -- the earlier theorem claims are
retracted).

WHAT THIS FILE NOW CLAIMS (and no more): the v1 clause structure can
be ANNOTATED with proposed reasons drawn from the T1-T9 foundation.
The reasons are arguments and identifications, not theorems.  The
round-8 hostile review (findings F2, F6, F7, F10, F11, F12; Addendum
56) defeated the stronger claims this file previously made:

  RETRACTED - "the point-vs-window gauge reading is a theorem of the
    T5 increment rule via half-open support (a,b]".  The summand set
    of the mu/e path INCLUDES p(14) (part4b:83, "d=14..21 ...
    exclusive of the lower endpoint" -- i.e. summands 14..21), so no
    faithful support reading exempts it; the prior "support"
    computation double-shifted the summand ranges, and the prior
    increment-rule verifier uses the OPPOSITE span convention
    (cascade_increment_rule.py: a <= dstar < b).  The G clause is
    the papers' strict-boundary STIPULATION (part4b:503, Conditional
    per 4108(a)), full stop.
  RETRACTED - "one record, one frame (T9)".  No such statement
    exists in T9 (quenched-record theorem) or anywhere in the repo;
    the phrase was an invented gloss.  The nesting below is a
    freestanding argument.
  RETRACTED - "Observer 3 = |T6 marked set|, a theorem".  T6 forces
    only the SUBCRITICAL marked set {5,13} (size 2), given the coset
    marking as instantiation; {5,13,21} is address-book data
    (Definition 6.1).  Observer k=3 = the number of generation-coset
    members is an instantiation-count identification; k=3 stays a
    soft input.
  RETRACTED - "19 and 5 are foundation objects" (vs 14 and 7
    inherited).  All four source values pass through the same
    feature->integer-layer selection convention counted in the
    paper's residue; and "5 = observer twist" was wrong -- the
    observer is twist 4 (Definition 6.1); 5 is the volume-maximum
    host layer d_V=5 (part4b:83).
  RETRACTED - "no precedence order, no null clause, no k-table in
    the code".  The code below is an ordered if/elif chain with an
    else-None and inline constants -- syntactically exactly a
    precedence order, a null clause, and a k-table.  What the
    annotations add is proposed REASONS, not removal.

WHAT SURVIVES, honestly labeled:
  ARGUMENT  - frame nesting: unit anchor before frame questions
    (a dimensionful number is meaningless unanchored), observer
    frame before mediation, bilinear innermost.  REVERSIBLE: "a
    record is produced at the end of a mediated path, so the gauge
    frame resolves first" argues unit > gauge > observer (= PGL,
    also an exhaustion survivor).  The nesting PROPOSES PLG; it does
    not select it.
  ARGUMENT  - contact counting: k = 1 (one anchor) / 3 (one per
    generation-coset member -- instantiation count, NOT "three
    spatial dimensions" (Check 8) and NOT a T6 theorem) / 1 (one
    band) / 2 x periods (two legs of a bilinear form).
  ARGUMENT  - member existence: no resolved frame -> no
    chi-attachment -> Family-B null.
  IDENTIFICATION - obstruction |dg|/8 read as winding of the
    order-8 Weil-index clock (the order is T6's; "each cycle = one
    rank unit" is asserted, and the data cannot distinguish this
    from periods-spanned-minus-1 on any coset row).
  IDENTIFICATION - colour rank 2 read as [Q(zeta_3):Q]; equally
    readable as the su(3) Cartan rank (Addendum 14) -- a choice
    among coincident 2s.  "Fixed once per record" is an assumption
    (the m_b/m_tau row is what forces the ANY-quark reading; see
    the uniqueness exhaustion's R2 kills).

KNOWN FAILURE (shared with v1, review F5): the availability clauses
overpredict on theta_C -- computed (1,2,0), stored/formula (0,0,0).
Reported below, not patched.

FORK POSITIONS (downgraded from "adjudication" to "proposal"): on
the exhaustion's probe forks this reconstruction takes the canonical
branch everywhere, but at argument strength only -- P3/P4/P7 by the
reversible nesting argument (P7, the P&G corner, added in round 10),
P1 by the winding identification, P2 by the strict-boundary
stipulation itself (not independent arithmetic), P5 by the no-frame
argument, P6 by the point-vs-window reading (round 9).  A future row
disagreeing would refute the PROPOSAL, not a theorem.
"""

import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cascade_u2_function import CASES, EXPECT, GAUGE, periods_touched
from cascade_u2_uniqueness import PROBES

CLOCK = 8              # order of the Weil index gamma = zeta_8 (T6)
COLOUR_RANK = 2        # [Q(zeta_3):Q] -- or su(3) Cartan rank (A14)
GENERATION_COSET = (5, 13, 21)   # address-book instantiation data
BAND = (12, 13, 14)    # gauge twists (Radon-Hurwitz)
SOURCES = dict(Absolute=19, Observer=5, Gauge=14, Amplitude=7)
# all four source values pass through the feature->layer selection
# convention (paper residue); none is re-derived here


def gauge_mediated(novel):
    """The papers' strict-boundary stipulation (part4b:503, 4108(a)):
    a window whose summand range begins strictly below the U(1)
    layer 14 and reaches the gauge band.  A stipulation, not a
    support theorem (see docstring RETRACTED items)."""
    if not isinstance(novel, tuple) or novel[0] >= novel[1]:
        return False
    lo, hi = novel
    return lo < GAUGE[1] and hi >= GAUGE[0]


def u2_fp(row):
    name, legs, novel, full, kind, dim = row
    gens = [g for g, k in legs if k in ("quark", "lepton")]

    # availability: winding identification / colour rank / duality
    obstr = abs(gens[0] - gens[1]) // CLOCK if len(gens) == 2 else 0
    colour = COLOUR_RANK if any(k == "quark" for _, k in legs) else 0
    proj = 1 if {"quark", "lepton"} <= {k for _, k in legs} else 0

    pop = ("Geometric" if kind == "density" else
           "Amplitude" if kind == "overlap" else "Descent")
    sign = "+" if pop == "Descent" else "-"

    # the annotated decision chain (syntactically: precedence order,
    # null clause, k-table -- see docstring; the annotations propose
    # reasons, they do not remove the stipulations)
    if dim:                                   # unit anchor outermost
        frame = ("Absolute", SOURCES["Absolute"], 1)
    elif kind in ("local-ratio", "density"):  # observer frame
        frame = ("Observer", SOURCES["Observer"], len(GENERATION_COSET))
    elif gauge_mediated(novel):               # gauge frame
        frame = ("Gauge", SOURCES["Gauge"], 1)
    elif kind == "overlap":                   # bilinear frame
        frame = ("Amplitude", SOURCES["Amplitude"],
                 2 * periods_touched(full))
    else:                                     # no frame -> Family B
        frame = None
    member = None if frame is None else (pop, frame[1], frame[2], sign)
    return dict(avail=(obstr, colour, proj), member=member)


def main():
    print("=" * 74)
    print("U2 FIRST-PRINCIPLES RECONSTRUCTION (round-8: argument strength)")
    print("=" * 74)
    print()
    mp = mf = 0
    avail_fails = []
    for row in CASES:
        got = u2_fp(row)
        exp = EXPECT[row[0]]
        mem_ok = got["member"] == exp["member"]
        mp += mem_ok
        mf += not mem_ok
        line = f"  {'PASS' if mem_ok else 'FAIL'}  {row[0]:<11}" \
               f" member={got['member']}"
        if "avail" in exp and got["avail"] != exp["avail"]:
            avail_fails.append((row[0], got["avail"], exp["avail"]))
            line += "   [avail DEFECT]"
        print(line)
    print()
    print(f"  MEMBER fields: {mp}/{mp + mf} under the corrected key")
    for name, g, e in avail_fails:
        print(f"  AVAIL defect (open, review F5): {name} computed {g}"
              f" vs stored {e}")
    print()
    print("PROPOSED FORK POSITIONS (argument strength, not adjudication):")
    for probe in PROBES:
        got = u2_fp(probe)
        print(f"  {probe[0]}:")
        print(f"    proposal -> member={got['member']}")
    print()
    print("  Grounds per fork: P1 winding identification; P2 the strict-")
    print("  boundary stipulation's plain reading; P3/P4/P7 the REVERSIBLE")
    print("  nesting argument (PGL is argued equally well by path-before-")
    print("  read; P7 is the P&G case added in round 10); P5 the no-frame")
    print("  argument; P6 the point-vs-window reading (round 9).  None is")
    print("  a theorem.")
    print()
    print("=" * 74)
    print("STATUS LEDGER (round-8 corrected)")
    print("=" * 74)
    print("  ARGUMENT      : frame nesting (reversible); contact counts;")
    print("                  member-existence-from-frames.")
    print("  IDENTIFICATION: winding |dg|/8; colour rank 2 (field degree")
    print("                  vs Cartan rank -- coincident 2s); Observer")
    print("                  k=3 = generation-coset count (instantiation).")
    print("  STIPULATION   : the G clause (papers' strict boundary,")
    print("                  Conditional per part4b 4108(a)); the four")
    print("                  source values 19/5/14/7 (feature->layer")
    print("                  convention); kind fields ride on D1; A13")
    print("                  grading is an input.")
    print("  OPEN DEFECT   : availability on theta_C (and the whole")
    print("                  avail-block no-survivor state, see the")
    print("                  uniqueness script).")
    print("  RETRACTED     : half-open support 'theorem'; 'T9 one-record-")
    print("                  one-frame'; 'Observer 3 = |T6 marked set|';")
    print("                  '19/5 foundation objects'; 'no precedence/")
    print("                  null/k-table in the code'; 'adjudicates all")
    print("                  five forks'.")


if __name__ == "__main__":
    main()
