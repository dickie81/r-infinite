#!/usr/bin/env python3
"""
U2 RULE-SET UNIQUENESS EXHAUSTION (rounds 8-14 corrected).

THE QUESTION: the v1 rule-set reproduces the stored member table, but
was assembled knowing it.  Is it the only rule-set that does, within
a declared candidate space?  (T4-grade: single-valuedness relative to
the space, never absolute forcedness.)

ROUND-8 CORRECTIONS carried by this version (hostile review, findings
F1-F5, F8; see Addendum 56):
  - The answer key is corrected (theta_23 k=4 per part4b
    thm:theta23-closure; T4-stored availability added, under which
    the availability clauses FAILED on theta_C through rounds 8-12
    -- computed (1,2,0) vs stored (0,0,0), zero avail-block
    survivors.  RESOLVED by Addendum 61's record-legs correction
    (round-13 restated, A62): the angles' legs are the gauge-layer
    states they read (papers' Cabibbo proof, VERBATIM for theta_C;
    template-extension inference for theta_23), not the SM-side
    generation pairing; with record-legs the unchanged clauses
    cover every row and the avail block has SIX survivors --
    canonical + two extensional duplicates + the cross-generation
    indicator, a GENUINE off-domain fork discriminated by P1
    (round-13 M3 corrected the "two duplicates" miscount).
    Disclosed fixed-target; sharpened PMNS falsifier and the M4
    corpus conditionality -- see cascade_u2_function.py.)
  - The A13 grading is applied consistently (theta_C and m_tau-abs
    novel=None).  Consequences: the pre-fix "points count too" G
    variant is no longer killed (its old kill was manufactured by
    the inconsistent theta_C grading), and NO realized row has two
    true flags within this grading -- so ALL SIX precedence orders
    survive.  The precedence is unpinned by this exhaustion; round 9
    (M3) further showed A52's dash-fill was inconsistent with the
    papers' expression-tree predicate, so the precedence is vacuous
    on uniform primary readings at BOTH layers, with the 13-109 sigma
    anchoring conditional on the four variant readings (round 10
    added the ell_A-kind L-variant at +109 sigma).
  - The variant count is 44 (not "24" as previously misstated).
  - KILL CLASSIFICATION (F3): "every kill is a data-kill" is
    withdrawn.  Each member-field kill is now sigma'd: the variant's
    member value exp(+-alpha(src)/chi^k) is compared to the stored
    one and divided by the row's experimental fractional precision
    (or leading-match quality where the record is a leading-order
    match).  Classes: LABEL (identical value, kill by record label
    only), RECORD (< 2 sigma -- experiment cannot distinguish;
    killed only by table fidelity), DATA (>= 2 sigma).  Slot
    "pinning strength" = the strongest class among its kills.
  - WITHHELD AXIS DISCLOSED (F8): the source map (Absolute->19,
    Observer->5, Gauge->14, Amplitude->7) and the population-class
    names are held FIXED throughout -- the space never varies the
    four source values, so "pinned" claims are relative to a space
    that pre-fixes that freedom.

ROUND-9 CORRECTIONS (see Addendum 57):
  - M1: periods_touched now uses the papers' Bott convention
    ((d-1)//8, via cascade_u2_function) and theta_23's content is
    the uniform p-summand range (13,20); the R9 pinning is no
    longer relative to a bent input field.
  - M2: probe P6 added -- the original five probes could not
    separate the canonical G reading from "points count too" in the
    corrected survivor set; the round-8 completeness claim was for
    the old 72-survivor space only.

ROUND-10 CORRECTION (Major 1): P1-P6 was STILL incomplete for the
36-survivor set -- the R7 pairs {PGL,GPL} and {LPG,LGP} were
indistinguishable on all six probes (none carried P&G).  P7 added;
with it every pair of member survivors is either separated by a
probe or extensionally identical on reachable inputs (the R5
canonical-vs-lo<12 and R10 pairs fork on P2/P5/P6).  Completeness
claims refer to P1-P7 on the current survivors, this run.
  - Kill-strength honesty (round-9 m5; mislabeled under the round-10
    header until round 11, m3): the DISTINCTIVE content of the sign
    slot (the +/- structure beyond the label) and of the doubling
    (2x) in the channel rule are pinned only at RECORD strength
    (1.0 sigma and 1.4 sigma respectively); the multi-sigma kills
    on those slots hit other variants.  R6's second kill is 2.3
    sigma and R5's "strict top" exactly 2.0 sigma -- on the DATA
    boundary this classification itself defines.

NO-NAME RULE: every variant reads only identity facts through
bounded predicates -- no clause may mention an observable's name.

DISCLOSURES: the candidate space is finite and chosen; the soft
inputs (Observer k=3, A13 grading, the ell_A kind, and the
record-legs classification -- Addendum 61, round-13 restated) are
inputs here too; the m_b/m_tau projection rank rides on the
audit-lemma corpus (round-13 M4).
"""

import itertools
import math
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
 "2 if ANY quark leg (CANONICAL)":
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
 "window, strict boundary lo<14, hi>=12 (CANONICAL)":
    lambda novel: (lambda w: w is not None and w[0] < GAUGE[1] and w[1] >= GAUGE[0])(window(novel)),
 "points count too":
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
N_VARIANTS = sum(len(d) for _, d in AVAIL_SLOTS + MEMBER_SLOTS)


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


def failures(choice, fields=("avail", "member")):
    out = []
    for row in CASES:
        got = u2_c(row, choice)
        exp = EXPECT[row[0]]
        for key in exp:
            if key in fields and got[key] != exp[key]:
                out.append((row[0], key, got[key], exp[key]))
    return out


# ---- kill classification (round 8, F3) ------------------------------
# fractional comparison scales: experimental sigma, or the paper-
# stated leading-match quality where the record is a leading match
PRECISION = {
 "alpha_s": 0.0085, "tau/mu": 6.5e-5, "mu/e": 0.0013, "b/s": 0.0087,
 "m_b/m_tau": 0.01, "m_tau abs": 6.8e-5, "ell_A": 3.0e-4,
 "sin2thW": 1.7e-4, "Omega_m": 0.023, "theta_C": 0.0031,
 "theta_23": 0.025,
}


def member_value(m):
    """Closure factor exp(sign * alpha(src) / chi^k), chi = 2."""
    if m is None:
        return 1.0
    _, src, k, sign = m
    r = math.gamma((src + 1) / 2) / math.gamma((src + 2) / 2)
    a = r * r / 4.0
    return math.exp((1 if sign == "+" else -1) * a / 2 ** k)


def classify_kill(fail):
    row, key, got, exp = fail
    if key != "member":
        return "FORMULA", None   # availability: order-unity formula factors
    vg, ve = member_value(got), member_value(exp)
    if abs(vg - ve) < 1e-12:
        return "LABEL", 0.0
    sig = abs(vg / ve - 1) / PRECISION[row]
    return ("DATA" if sig >= 2 else "RECORD"), sig


# probes: identity facts of UNREALIZED observables (no stored answer)
PROBES = [
 ("P1 third-gap ratio (legs 5&21, dg=16)",
  [(5, "lepton"), (21, "lepton")], (6, 21), (6, 21), "mass-ratio", False),
 # (round-10 m-B: label corrected -- under the papers' periods
 # (13,20) spans P1 and P2, it is not "pure second-period")
 ("P2 window coupling (13,20), spans P1+P2",
  [(13, "gauge")], (13, 20), (13, 20), "coupling", False),
 ("P3 observer-local ratio WITH window content (L&G both true)",
  [(13, "gauge"), (14, "gauge")], (5, 14), (5, 14), "local-ratio", False),
 ("P4 dimensionful observer-local (P&L both true)",
  [], None, None, "local-ratio", True),
 ("P5 flag-free non-ratio Descent (coupling, no window; full spans P2+P3)",
  [(21, "gauge")], None, (21, 28), "coupling", False),
 # round-9 M2: the corrected survivor set contains "points count too",
 # which the original five probes provably could not separate from the
 # canonical G reading (no probe carried point content).  P6 fixes that.
 ("P6 point normalisation IN the gauge band (novel = point 13)",
  [(13, "gauge")], 13, 13, "coupling", False),
 # round-10 Major 1: P1-P6 still did not separate the R7 pairs
 # {PGL,GPL} and {LPG,LGP} -- no probe carried P AND G together
 # (P3 is L&G, P4 is P&L).  P7 closes the enumeration: with
 # P3+P4+P7 all six orderings have distinct probe signatures.
 # ROUND-11 F1 CORRECTION: round 10 justified P7's reachability by
 # citing the papers' m_W-absolute as "dimensionful with gauge-
 # window content" -- but under the arc's own uniform grading
 # m_W-absolute is (T,F,F): its window content sits inside the
 # closed constituents m_Z/v (part4b:1728 short-circuits at P),
 # exactly the m_tau-abs configuration.  The witness held only
 # under the demoted constituent-expansion reading -- the grading-
 # inconsistency class, third occurrence, owned in Addendum 59.
 # Honest status: P7 is a well-formed hypothetical identity-fact
 # corner; the nearest uniform-reading P&G configuration is the
 # VEV v itself (its canonical formula carries e^(Phi(5,12))
 # TOP-LEVEL and it is dimensionful -- part4b thm:vev at 3325-3328,
 # v = M_Pl,red x a_GUT x exp(Phi(12->4)) x exp(-pi/alpha(5));
 # window attribution at part4b:83), but v is an
 # anchor with no addressed member row, so the P&G class has no
 # realized addressed instance.
 ("P7 dimensionful WITH gauge-window content (P&G both true)",
  [], (5, 12), (5, 12), "abs-mass", True),
]


def main():
    print("=" * 74)
    print("U2 RULE-SET UNIQUENESS EXHAUSTION (rounds 8-14 corrected)")
    print("=" * 74)
    print(f"  variant space: {N_VARIANTS} variants across 10 slots;"
          f" source map {{19,5,14,7}} and class names HELD FIXED")
    print()
    print("PER-SLOT SCAN (others canonical; member slots checked on member")
    print("fields, avail slots on the corrected avail key):")
    slot_survivors = {}
    for slot, space in AVAIL_SLOTS + MEMBER_SLOTS:
        fields = ("avail",) if slot in ("R1", "R2", "R3") else ("member",)
        surv = []
        print(f"  {slot}:")
        for vname in space:
            choice = dict(CANON)
            choice[slot] = vname
            fails = failures(choice, fields)
            if fails:
                cls, sig = classify_kill(fails[0])
                r, key, g, e = fails[0]
                tag = (f"{cls}" + (f" {sig:.1f} sigma" if sig is not None
                                   else ""))
                print(f"    KILLED [{tag:<16}] {vname}")
                print(f"             by {r}: {key} {g} != stored {e}")
            else:
                surv.append(vname)
                tag = "CANONICAL" if vname == CANON[slot] else "SURVIVES "
                print(f"    {tag}  {vname}")
        slot_survivors[slot] = surv

    print()
    print("FULL CARTESIAN PRODUCTS:")
    avail_surv, member_surv = [], []
    at = mt = 0
    for combo in itertools.product(*[space for _, space in AVAIL_SLOTS]):
        at += 1
        choice = dict(CANON)
        choice.update(dict(zip([s for s, _ in AVAIL_SLOTS], combo)))
        if not failures(choice, ("avail",)):
            avail_surv.append(combo)
    for combo in itertools.product(*[space for _, space in MEMBER_SLOTS]):
        mt += 1
        choice = dict(CANON)
        choice.update(dict(zip([s for s, _ in MEMBER_SLOTS], combo)))
        if not failures(choice, ("member",)):
            member_surv.append(combo)
    print(f"  avail block : {len(avail_surv)}/{at} combos survive the"
          f" corrected key")
    print(f"  member block: {len(member_surv)}/{mt} combos survive")
    pm = 1
    for s, _ in MEMBER_SLOTS:
        pm *= len(slot_survivors[s])
    print(f"  member compensating combos beyond per-slot product:"
          f" {len(member_surv) - pm:+d}")

    print()
    print("PROBE FORKS (member survivors, avail slots canonical):")
    all_surv = []
    for mc in member_surv:
        choice = dict(CANON)
        choice.update(dict(zip([s for s, _ in MEMBER_SLOTS], mc)))
        all_surv.append(choice)
    for probe in PROBES:
        outs = {}
        for ch in all_surv:
            got = u2_c(probe, ch)
            outs.setdefault(got["member"], []).append(ch)
        print(f"  {probe[0]}:")
        if len(outs) == 1:
            print(f"    NO FORK: all -> member={next(iter(outs))}")
        else:
            for m, chs in sorted(outs.items(),
                                 key=lambda x: -len(x[1])):
                diff = {}
                for s, _ in MEMBER_SLOTS:
                    vals = {c[s] for c in chs}
                    allv = {c[s] for c in all_surv}
                    if vals != allv:
                        diff[s] = sorted(vals)
                print(f"    FORK ({len(chs)}): member={m}")
                for s, v in diff.items():
                    print(f"        <- {s} in {v}")

    print()
    print("AVAIL PROBE FORKS (avail survivors, member slots canonical;")
    print("added round 13, M3 -- the avail freedom was previously")
    print("unexercised by the probe section):")
    any_avail_fork = False
    for probe in PROBES:
        outs = {}
        for ac in avail_surv:
            choice = dict(CANON)
            choice.update(dict(zip([s for s, _ in AVAIL_SLOTS], ac)))
            got = u2_c(probe, choice)
            outs.setdefault(got["avail"], []).append(
                dict(zip([s for s, _ in AVAIL_SLOTS], ac)))
        if len(outs) > 1:
            any_avail_fork = True
            print(f"  {probe[0]}:")
            allv = {s: {dict(zip([s2 for s2, _ in AVAIL_SLOTS], ac))[s]
                        for ac in avail_surv} for s, _ in AVAIL_SLOTS}
            for a, chs in sorted(outs.items(), key=lambda x: -len(x[1])):
                diff = {s: sorted({c[s] for c in chs})
                        for s, _ in AVAIL_SLOTS
                        if {c[s] for c in chs} != allv[s]}
                print(f"    FORK ({len(chs)}): avail={a}")
                for s, v in diff.items():
                    print(f"        <- {s} in {v}")
    if not any_avail_fork:
        print("  no avail fork on any probe")

    print()
    print("=" * 74)
    print("VERDICT (rounds 10-14 corrected state)")
    print("=" * 74)
    pinned = [s for s in slot_survivors if len(slot_survivors[s]) == 1]
    print(f"  member-field survivors: {len(member_surv)}; per-slot"
          f" survivor counts:"
          f" {[f'{s}:{len(slot_survivors[s])}' for s, _ in MEMBER_SLOTS]}")
    print(f"  slots with canonical alone surviving: {pinned}")
    print()
    print("  AVAILABILITY (Addendum 61, round-13 restated): under the")
    print("  record-legs encoding the canonical clauses cover every row;")
    print("  survivors = canonical + two extensional duplicates (R1")
    print("  periods-minus-1; R3 kinds-minus-1) + the cross-generation")
    print("  indicator, a GENUINE fork discriminated off-domain by P1")
    print("  (avail forks above).  R2 pinned uniquely by m_b/m_tau; the")
    print("  R3 projection pinning is CONDITIONAL on the audit-lemma")
    print("  corpus for m_b/m_tau's proj=1 (round-13 M4: the papers'")
    print("  Tier-4a 'm_b/m_tau = e' carries no projection factor).")
    print("  Conditional on the record-legs rule (new per-row classifier,")
    print("  soft input; fixed-target; sharpened PMNS falsifier).  The")
    print("  rounds-8-12 zero-survivor state was the label-legs mislabel.")
    print("  MEMBER FIELDS: uniqueness holds only up to (i) the G-flag")
    print("  reading (3 survivors -- the old theta_C kill of 'points")
    print("  count too' was an artifact of the inconsistent grading),")
    print("  (ii) the precedence order (all 6 survive: no realized row is")
    print("  multi-flag under the consistent A13 grading; round 9: also")
    print("  vacuous on the papers' uniform expression-tree reading --")
    print("  anchoring only under A52's variant gradings, 13-109 sigma), and")
    print("  (iii) the Family-B kind restriction (2 survivors).")
    print("  KILL STRENGTHS: mixed -- see per-kill classes above (LABEL =")
    print("  record-label only; RECORD < 2 sigma; DATA >= 2 sigma).  The")
    print("  blanket claim 'every kill is a data-kill' is WITHDRAWN.")
    print("  All survivor freedom remains off-domain (probe forks above).")


if __name__ == "__main__":
    main()
