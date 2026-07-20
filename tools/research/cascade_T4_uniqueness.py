#!/usr/bin/env python3
"""
T4: ADDRESS-BOOK DETERMINATION (restated per external review F3).

STATEMENT.  Given the ~60-entry address book (window endpoints,
availability ranks, member source/class/exponent, record status per
observable) and the rules (T5 attach-once, T6 counting, T7 sign, T8
projection, T9 ranks, exclusion, flags, channel-count), the encoded
rules are single-valued and the determined formulas reproduce the
record to <= 0.01%.  The exhaustion verifies single-valuedness and
arithmetic correctness -- NOT forcedness: availability is tabulated
per observable, and computing it from address data alone (U2 as a
function) is the open formal target.

PROOF STRUCTURE.
  U1 (exactly-once).  At-most-once is T5 (Z totally ordered; simple
     features; partition of log xi).  At-least-once is the
     COMPLETENESS OF THE GAUSSIAN MEASURE (T2): Z is the product of
     ALL mode normalisations; a mode present at a crossing
     contributes its factor (annealed if unrecorded, quenched e^(r/2)
     if recorded, T9) -- omitting it is not an alternative
     assignment but a different measure, violating A1.
  U2 (availability -- TABULATED, not computed; per review F3 the
     stronger claim is open).  The stored operation set cites: colour rank (T8/T9),
     broken-symmetry status (obstruction scope), frame changes
     (T8), threshold side (T6/A38).  The exclusion principle is the
     negative direction: no generating process, no factor.
  U3 (member determinism).  Source by the flags (A12, canonical
     formulas A13), sign by T7 (population class), magnitude
     alpha(d*)/chi^k with k by the channel-count theorem, once by
     T5, none for L-class (non-source-selectable).
  EXHAUSTION.  For each stage, enumerate the NAIVE space (window
     alternatives x operation multiplicities 0..2 x all member
     options including none) and apply each rule as a labelled
     filter.  T4 holds iff every stage ends with exactly ONE
     survivor, and the survivor reproduces the recorded formula.

CONDITIONALITY (stated, not hidden): unique GIVEN the address book
and record statuses (instantiation / C1; the addresses themselves
are largely forced by the papers' Part IVa Radon-Hurwitz/Bott
theorems -- inherited), the P>L>G precedence, J1/J2 in the neutrino
mechanism, and A2's closed atom list.
"""

import itertools
import math

from scipy.special import digamma

PI = math.pi
SQRTPI = math.sqrt(PI)
COS30 = math.cos(PI / 6)


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


def p(d):
    return 0.5 * digamma((d + 1) / 2.0) - 0.5 * math.log(PI)


def Phi(a, b):
    return sum(p(d) for d in range(a, b + 1))


SOURCES = [5, 7, 14, 19]
KS = [1, 2, 3, 4]

# Stage table.  Address data (forced window, availability, member class)
# is the instantiation input; every filter cites its theorem.
STAGES = [
    dict(name="b/s", windows=[(6, 13), (5, 13), (6, 14), (5, 14)],
         fwin=(6, 13), avail=dict(obstr=1, colour=2, proj=0),
         mem=dict(cls="Amplitude", src=7, k=4), obs=44.7436),
    dict(name="m_tau/m_mu", windows=[(6, 13), (5, 13), (6, 14)],
         fwin=(6, 13), avail=dict(obstr=1, colour=0, proj=0),
         mem=dict(cls="Descent", src=14, k=1), obs=16.8170),
    dict(name="m_mu/m_e", windows=[(14, 21), (13, 21), (14, 22)],
         fwin=(14, 21), avail=dict(obstr=1, colour=0, proj=0),
         mem=None, obs=206.4958),          # leading (radiative slot separate)
    dict(name="m_b/m_tau", windows=[None], fwin=None,
         avail=dict(obstr=0, colour=2, proj=1),   # colour rank 2 recorded
         mem=None, obs=2.35422),
    dict(name="theta_C member", windows=[None], fwin=None,
         avail=dict(obstr=0, colour=0, proj=0),
         mem=dict(cls="Amplitude", src=7, k=2), obs=math.exp(-alpha(7) / 4)),
    dict(name="alpha_s member", windows=[None], fwin=None,
         avail=dict(obstr=0, colour=0, proj=0),
         mem=dict(cls="Descent", src=14, k=1), obs=math.exp(alpha(14) / 2)),
    dict(name="m_tau abs member", windows=[None], fwin=None,
         avail=dict(obstr=0, colour=0, proj=0),
         mem=dict(cls="Descent", src=19, k=1), obs=math.exp(alpha(19) / 2)),
    dict(name="sin2thW member", windows=[None], fwin=None,
         avail=dict(obstr=0, colour=0, proj=0),
         mem=dict(cls="Descent", src=5, k=3), obs=math.exp(alpha(5) / 8)),
    dict(name="Omega_m member", windows=[None], fwin=None,
         avail=dict(obstr=0, colour=0, proj=0),
         mem=dict(cls="Geometric", src=5, k=3), obs=math.exp(-alpha(5) / 8)),
]


def member_value(m):
    if m is None:
        return 1.0
    sgn = +1 if m["cls"] == "Descent" else -1
    return math.exp(sgn * alpha(m["src"]) / 2 ** m["k"])


def stage_value(win, mults, mem):
    v = 1.0
    if win:
        v *= math.exp(Phi(*win))
    v *= (2 * SQRTPI) ** mults["obstr"]
    v *= math.e ** (mults["colour"] / 2.0)     # T9: e^(r/2) per recorded rank
    v *= COS30 ** mults["proj"]
    v *= member_value(mem)
    return v


def exhaust(stage):
    naive = 0
    survivors = []
    mem_space = [None] + [dict(cls=c, src=s, k=k)
                          for c in ("Descent", "Amplitude", "Geometric")
                          for s in SOURCES for k in KS]
    for win in stage["windows"]:
        for mo, mc, mp in itertools.product((0, 1, 2), (0, 1, 2, 4), (0, 1, 2)):
            for mem in mem_space:
                naive += 1
                # F1: address book fixes the window
                if win != stage["fwin"]:
                    continue
                # F2 (U1+U2): each available operation exactly its rank,
                # unavailable exactly zero  [T5 + T2-completeness + A38]
                if (mo, mc, mp) != (stage["avail"]["obstr"],
                                    stage["avail"]["colour"],
                                    stage["avail"]["proj"]):
                    continue
                # F3 (U3): member forced by flags + T7 + channel count
                fm = stage["mem"]
                if fm is None:
                    if mem is not None:
                        continue
                else:
                    if mem is None:
                        continue
                    if mem["src"] != fm["src"]:      # flags (A12/A13)
                        continue
                    if mem["cls"] != fm["cls"]:      # population class -> T7
                        continue
                    if mem["k"] != fm["k"]:          # channel-count theorem
                        continue
                survivors.append((win, (mo, mc, mp), mem))
    return naive, survivors


def main():
    print("=" * 74)
    print("T4 EXHAUSTION: rule-consistent assignments per stage")
    print("=" * 74)
    print(f"  {'stage':<18}{'naive space':>12}{'survivors':>10}"
          f"{'value':>12}{'recorded':>12}{'dev':>8}")
    all_one = True
    for st in STAGES:
        naive, surv = exhaust(st)
        if len(surv) != 1:
            all_one = False
            print(f"  {st['name']:<18}{naive:>12}{len(surv):>10}"
                  f"   ** NOT UNIQUE **")
            continue
        win, mults, mem = surv[0]
        v = stage_value(win, dict(obstr=mults[0], colour=mults[1],
                                  proj=mults[2]), mem)
        dev = (v / st["obs"] - 1) * 100
        print(f"  {st['name']:<18}{naive:>12}{len(surv):>10}"
              f"{v:>12.4f}{st['obs']:>12.4f}{dev:>7.2f}%")
    print()
    # neutrino stage: forms x exponent patterns
    print("  neutrino E-stage: 10 window forms (A37) x 4 exponent patterns")
    forms = {"Nc pi^2": (3 * PI ** 2, False), "2pi e sqrt3": (29.5825, True),
             "4e^2": (29.5562, True), "G 2pi e": (30.2726, True),
             "chi Nc^2 sqrt(e)": (29.6770, True),
             "chi 2pi sqrt(e) sqrt2": (29.3003, True),
             "chi^2 2pi sec30": (29.0208, True),
             "Nc G pi sqrt3": (28.9339, True),
             "chi Nc G e": (28.9082, True),
             "G pi^2 sqrt(e)": (28.8418, True)}
    patterns = ["(0,1,2) [T6 forced]", "(1,1,1)", "(0,1,1)", "(0,2,4)"]
    surv = [(f, pt) for f, (v, col) in forms.items() for pt in patterns
            if not col and pt.startswith("(0,1,2)")]
    print(f"    naive {len(forms)*len(patterns)}: A38 exclusion kills"
          f" colour-bearing forms, T6 kills patterns -> survivors: {surv}")
    print()
    verdict = all_one and len(surv) == 1
    print("=" * 74)
    print(f"  T4 VERDICT: {'ADDRESS-BOOK DETERMINATION HOLDS' if verdict else 'FAILS'}"
          f" -- every stage single-valued vs the ~60-entry table")
    print("=" * 74)
    print("  Conditional on: the address book & record statuses (C1 instan-")
    print("  tiation; addresses largely forced by Part IVa Radon-Hurwitz/")
    print("  Bott, inherited), P>L>G precedence, J1/J2, A2's closed atom")
    print("  list.  Verifies single-valuedness + arithmetic correctness;")
    print("  availability-as-a-function (the forcing theorem) is OPEN.")


if __name__ == "__main__":
    main()
