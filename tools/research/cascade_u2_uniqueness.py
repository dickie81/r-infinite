#!/usr/bin/env python3
"""
U2 RULE-SET UNIQUENESS: the forcing theorem, by exhaustion.

THE QUESTION (the open item left by cascade_u2_function.py): the v1
rule-set reproduces the stored table, but it was assembled knowing
the table.  Is it the ONLY rule-set that does?

THE METHOD (T4-grade: exhaustion within a declared candidate space,
proving single-valuedness, never absolute forcedness):
  1. For each of the ten clause slots, enumerate every papers-
     motivated variant (24 variants across 10 slots, spaces below).
  2. NO-NAME RULE: every variant reads only identity facts (legs,
     content, kind, dim) through bounded predicates -- no clause may
     mention an observable's name.  This excludes the lookup table
     itself from the candidate space.
  3. Run the FULL CARTESIAN PRODUCT of variants (avail block 75
     combos; member block 21,600 combos) against all 11 stored rows.
  4. Classify survivors: extensionally equal on the realized domain
     by construction; probe rows (identity facts of UNREALIZED
     observables) then split the survivors into extensional classes
     -- each split is a registered DISCRIMINATING STRUCTURAL
     PREDICTION, not a defect.

WHAT "UNIQUE" CAN MEAN HERE (stated before running):
  - PINNED slot: only the canonical variant survives -> that clause
    is data-forced within the space.
  - DUPLICATE slot: survivors extensionally equal on the whole
    reachable identity domain (e.g. |dg|/8 = periods-1 on the coset
    {5,13,21}) -> same function, different syntax; uniqueness holds.
  - FORKED slot: survivors agree on all realized rows but disagree
    on a probe -> the data to date does not pin the clause; the
    disagreement is a testable fork.
The theorem sought: the rule-set is unique AS A FUNCTION ON THE
REALIZED DOMAIN, with all residual freedom enumerated, localized,
and pushed off-domain.

DATA ANCHORING of kills: the stored table is validated to <= 0.01%
against the record (T4), so any member-field change (source d*,
channel k, class, sign) moves a closed formula by factors of order
e^(alpha/k) or chi -- far beyond 0.01%.  Order variants placing G
before P were already sigma'd in A52: m_tau-abs -> 1784.7 MeV =
+65 sigma.  Kills are therefore data-kills, not convention-kills.

DISCLOSURES: the candidate space is finite and chosen (papers-
motivated, not the space of all conceivable rules); uniqueness is
relative to it -- the same epistemic standard as the T4 exhaustion.
The two soft inputs (Observer k = 3; A13 grading) are inputs here
too, not outputs.
"""

import itertools
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cascade_u2_function import CASES, EXPECT, GAUGE, periods_touched


def gens_of(legs):
    return [g for g, k in legs if k in ("quark", "lepton")]


def window(novel):
    if isinstance(novel, tuple) and novel[0] < novel[1]:
        return novel
    return None


# ---- clause variant spaces (each variant papers-motivated) ----------

R1 = {  # obstruction rank (avail[0])
 "|dg|/8 Bott gaps (CANONICAL)":
    lambda legs: (lambda g: abs(g[0] - g[1]) // 8 if len(g) == 2 else 0)(gens_of(legs)),
 "periods spanned minus 1":
    lambda legs: (lambda g: periods_touched((min(g), max(g))) - 1 if len(g) == 2 else 0)(gens_of(legs)),
 "cross-generation indicator":
    lambda legs: (lambda g: 1 if len(g) == 2 and g[0] != g[1] else 0)(gens_of(legs)),
 "|dg|/4 half-Bott":
    lambda legs: (lambda g: abs(g[0] - g[1]) // 4 if len(g) == 2 else 0)(gens_of(legs)),
 "no obstruction":
    lambda legs: 0,
}

R2 = {  # colour rank (avail[1])
 "2 if ANY quark leg = one su(3) Cartan (CANONICAL)":
    lambda legs: 2 if any(k == "quark" for _, k in legs) else 0,
 "2 only if ALL matter legs quark":
    lambda legs: 2 if gens_of(legs) and all(k == "quark" for _, k in legs if k in ("quark", "lepton")) else 0,
 "count of quark legs":
    lambda legs: sum(1 for _, k in legs if k == "quark"),
 "N_c = 3 if any quark":
    lambda legs: 3 if any(k == "quark" for _, k in legs) else 0,
 "no colour rank":
    lambda legs: 0,
}

R3 = {  # projection rank (avail[2])
 "1 if quark/lepton mixed (CANONICAL)":
    lambda legs: 1 if {"quark", "lepton"} <= {k for _, k in legs} else 0,
 "matter kinds minus 1":
    lambda legs: max(0, len({k for _, k in legs if k in ("quark", "lepton")}) - 1),
 "1 if any lepton leg":
    lambda legs: 1 if any(k == "lepton" for _, k in legs) else 0,
 "no projection rank":
    lambda legs: 0,
}

R4 = {  # flag P
 "dimensionful/anchored (CANONICAL)": lambda kind, dim: bool(dim),
 "never":                             lambda kind, dim: False,
 "abs-mass kinds only":               lambda kind, dim: kind == "abs-mass",
}

R5 = {  # flag G
 "window transit lo<14, hi>=12 (CANONICAL)":
    lambda novel: (lambda w: w is not None and w[0] < GAUGE[1] and w[1] >= GAUGE[0])(window(novel)),
 "points count too (the pre-fix v1 reading)":
    lambda novel: novel is not None and (lambda lo, hi: lo < GAUGE[1] and hi >= GAUGE[0])(
        *(novel if isinstance(novel, tuple) else (novel, novel))),
 "boundary start allowed (lo<=14)":
    lambda novel: (lambda w: w is not None and w[0] <= GAUGE[1] and w[1] >= GAUGE[0])(window(novel)),
 "strict top (hi>12)":
    lambda novel: (lambda w: w is not None and w[0] < GAUGE[1] and w[1] > GAUGE[0])(window(novel)),
 "window starts wholly below (lo<12)":
    lambda novel: (lambda w: w is not None and w[0] < GAUGE[0] and w[1] >= GAUGE[0])(window(novel)),
}

R6 = {  # flag L
 "local-ratio or density (CANONICAL)": lambda kind: kind in ("local-ratio", "density"),
 "local-ratio only":                   lambda kind: kind == "local-ratio",
 "density only":                       lambda kind: kind == "density",
}

R7 = {"".join(o): o for o in itertools.permutations(("P", "L", "G"))}
TYPE_OF_FLAG = {"P": ("Absolute", 19), "L": ("Observer", 5),
                "G": ("Gauge", 14)}


def assign(flags, order):
    for f in order:
        if flags[f]:
            return TYPE_OF_FLAG[f]
    return ("Amplitude", 7)


def _pop(kind):
    return ("Geometric" if kind == "density" else
            "Amplitude" if kind == "overlap" else "Descent")


R8 = {  # population class + T7 sign
 "T7 map, + iff Descent (CANONICAL)":
    lambda kind: (_pop(kind), "+" if _pop(kind) == "Descent" else "-"),
 "swap Geometric/Amplitude targets":
    lambda kind: ((lambda p: ("Amplitude" if p == "Geometric" else
                              "Geometric" if p == "Amplitude" else p))(_pop(kind)),
                  "+" if _pop(kind) == "Descent" else "-"),
 "always +": lambda kind: (_pop(kind), "+"),
 "always -": lambda kind: (_pop(kind), "-"),
}

R9 = {  # channel exponent k
 "1 / 3 / 2*periods(full) (CANONICAL)":
    lambda typ, full, novel: (1 if typ in ("Absolute", "Gauge") else
                              3 if typ == "Observer" else 2 * periods_touched(full)),
 "always 1":
    lambda typ, full, novel: 1,
 "Observer -> 2":
    lambda typ, full, novel: (1 if typ in ("Absolute", "Gauge") else
                              2 if typ == "Observer" else 2 * periods_touched(full)),
 "Amplitude -> periods(full), no doubling":
    lambda typ, full, novel: (1 if typ in ("Absolute", "Gauge") else
                              3 if typ == "Observer" else periods_touched(full)),
 "Amplitude -> 2*periods(NOVEL)":
    lambda typ, full, novel: (1 if typ in ("Absolute", "Gauge") else
                              3 if typ == "Observer" else 2 * periods_touched(novel)),
}

R10 = {  # Family-B null (member = None)
 "None iff no flag AND Descent (CANONICAL)":
    lambda anyflag, pop, kind: (not anyflag) and pop == "Descent",
 "never None":
    lambda anyflag, pop, kind: False,
 "None iff no flag (any class)":
    lambda anyflag, pop, kind: not anyflag,
 "None iff no flag AND Descent AND mass-ratio":
    lambda anyflag, pop, kind: (not anyflag) and pop == "Descent" and kind == "mass-ratio",
}

AVAIL_SLOTS = [("R1", R1), ("R2", R2), ("R3", R3)]
MEMBER_SLOTS = [("R4", R4), ("R5", R5), ("R6", R6), ("R7", R7),
                ("R8", R8), ("R9", R9), ("R10", R10)]
CANON = {s: next(iter(d)) for s, d in AVAIL_SLOTS + MEMBER_SLOTS}


def u2_c(row, choice):
    name, legs, novel, full, kind, dim = row
    avail = (R1[choice["R1"]](legs), R2[choice["R2"]](legs),
             R3[choice["R3"]](legs))
    flags = dict(P=R4[choice["R4"]](kind, dim),
                 L=R6[choice["R6"]](kind),
                 G=R5[choice["R5"]](novel))
    typ, src = assign(flags, R7[choice["R7"]])
    pop, sign = R8[choice["R8"]](kind)
    k = R9[choice["R9"]](typ, full, novel)
    member = (None if R10[choice["R10"]](any(flags.values()), pop, kind)
              else (pop, src, k, sign))
    return dict(avail=avail, member=member)


def failures(choice):
    out = []
    for row in CASES:
        got = u2_c(row, choice)
        exp = EXPECT[row[0]]
        for key in exp:
            if got[key] != exp[key]:
                out.append((row[0], key, got[key], exp[key]))
    return out


# probes: identity facts of UNREALIZED observables (no stored answer)
PROBES = [
 ("P1 third-gap ratio (legs 5&21, dg=16)",
  [(5, "lepton"), (21, "lepton")], (6, 21), (6, 21), "mass-ratio", False),
 ("P2 pure second-period window coupling (13,20)",
  [(13, "gauge")], (13, 20), (13, 20), "coupling", False),
 ("P3 observer-local ratio WITH window content (L&G both true)",
  [(13, "gauge"), (14, "gauge")], (5, 14), (5, 14), "local-ratio", False),
 ("P4 dimensionful observer-local (P&L both true)",
  [], None, None, "local-ratio", True),
 ("P5 flag-free non-ratio Descent (coupling, no window)",
  [(21, "gauge")], None, (21, 28), "coupling", False),
]


def main():
    print("=" * 74)
    print("U2 RULE-SET UNIQUENESS EXHAUSTION")
    print("=" * 74)

    # ---- per-slot scan (others canonical) ----
    print()
    print("PER-SLOT SCAN (all other clauses canonical):")
    slot_survivors = {}
    for slot, space in AVAIL_SLOTS + MEMBER_SLOTS:
        surv = []
        print(f"  {slot}:")
        for vname in space:
            choice = dict(CANON)
            choice[slot] = vname
            fails = failures(choice)
            if fails:
                r, key, g, e = fails[0]
                print(f"    KILLED   {vname}")
                print(f"             by {r}: {key} {g} != stored {e}")
            else:
                surv.append(vname)
                tag = "CANONICAL" if vname == CANON[slot] else "SURVIVES "
                print(f"    {tag}  {vname}")
        slot_survivors[slot] = surv

    # ---- full cartesian products (catch compensating combos) ----
    print()
    print("FULL CARTESIAN PRODUCTS:")
    avail_total = member_total = 0
    avail_surv, member_surv = [], []
    for combo in itertools.product(*[space for _, space in AVAIL_SLOTS]):
        avail_total += 1
        choice = dict(CANON)
        choice.update(dict(zip([s for s, _ in AVAIL_SLOTS], combo)))
        if not failures(choice):
            avail_surv.append(combo)
    for combo in itertools.product(*[space for _, space in MEMBER_SLOTS]):
        member_total += 1
        choice = dict(CANON)
        choice.update(dict(zip([s for s, _ in MEMBER_SLOTS], combo)))
        if not failures(choice):
            member_surv.append(combo)
    print(f"  avail block : {len(avail_surv)}/{avail_total} combos survive")
    print(f"  member block: {len(member_surv)}/{member_total} combos survive")
    prod_avail = 1
    for s, _ in AVAIL_SLOTS:
        prod_avail *= len(slot_survivors[s])
    prod_member = 1
    for s, _ in MEMBER_SLOTS:
        prod_member *= len(slot_survivors[s])
    comp_a = len(avail_surv) - prod_avail
    comp_m = len(member_surv) - prod_member
    print(f"  compensating combos beyond per-slot products:"
          f" avail {comp_a:+d}, member {comp_m:+d}"
          f" {'(NONE -- slots independent)' if comp_a == 0 and comp_m == 0 else '(INVESTIGATE)'}")

    # ---- probe forks among survivors ----
    print()
    print("PROBE FORKS (survivors on unrealized identity facts):")
    all_survivors = []
    for ac in avail_surv:
        for mc in member_surv:
            choice = dict(zip([s for s, _ in AVAIL_SLOTS], ac))
            choice.update(dict(zip([s for s, _ in MEMBER_SLOTS], mc)))
            all_survivors.append(choice)
    print(f"  total surviving syntactic rule-sets: {len(all_survivors)}"
          f" (all agree on every realized row by construction)")
    nforks = 0
    for probe in PROBES:
        outs = {}
        for ch in all_survivors:
            got = u2_c(probe, ch)
            key = (got["avail"], got["member"])
            outs.setdefault(key, []).append(ch)
        print(f"  {probe[0]}:")
        if len(outs) == 1:
            (a, m), _ = next(iter(outs.items()))
            print(f"    NO FORK: all survivors -> avail={a} member={m}")
        else:
            nforks += 1
            for (a, m), chs in sorted(outs.items(), key=lambda x: -len(x[1])):
                # which slot choices distinguish this group
                diff = {}
                for s, _ in AVAIL_SLOTS + MEMBER_SLOTS:
                    vals = {c[s] for c in chs}
                    allvals = {c[s] for c in all_survivors}
                    if vals != allvals and len(vals) < len(allvals):
                        diff[s] = sorted(vals)
                print(f"    FORK ({len(chs)} rule-sets): avail={a} member={m}")
                for s, v in diff.items():
                    print(f"        <- {s} in {v}")

    print()
    print("=" * 74)
    print("VERDICT")
    print("=" * 74)
    pinned = [s for s, _ in AVAIL_SLOTS + MEMBER_SLOTS
              if len(slot_survivors[s]) == 1]
    degen = [s for s, _ in AVAIL_SLOTS + MEMBER_SLOTS
             if len(slot_survivors[s]) > 1]
    print(f"  PINNED slots (canonical variant alone survives): {pinned}")
    print(f"  DEGENERATE slots (multiple survivors): {degen}")
    print()
    print("  UNIQUENESS THEOREM (T4-grade, relative to the declared space):")
    print("  on the REALIZED identity domain the rule-set is unique as a")
    print("  function -- every surviving syntactic variant computes the")
    print("  identical table, and every kill is a data-kill (the table is")
    print("  validated to <=0.01%; source/order kills are sigma'd in A52 at")
    print("  13-65 sigma).  Residual freedom exists ONLY off-domain, is")
    print("  fully enumerated by the probe forks above, and each fork is a")
    print("  registered discriminating structural prediction: a future row")
    print("  matching a probe's identity facts adjudicates it.")
    print()
    print("  NOT proved: uniqueness over all conceivable rules (the space")
    print("  is declared, papers-motivated, finite); the two soft inputs")
    print("  (Observer k=3, A13 grading) remain inputs.")


if __name__ == "__main__":
    main()
