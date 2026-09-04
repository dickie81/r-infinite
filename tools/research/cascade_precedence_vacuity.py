#!/usr/bin/env python3
"""
THE P > L > G VACUITY CHECK (fix-map item 2).

QUESTION: does the precedence order ever fire?  If no observable has
more than one true flag, the order is vacuous and residue item six
can be DELETED.  If it fires, compute what every alternative order
would predict and whether data excludes it -- if all alternatives are
data-excluded, the precedence is ANCHORED (data-selected, same class
as the unit convention), not free.

METHOD (binary, answer not pre-known): evaluate the FULL flag triple
(P, L, G) for each of the nine closed observables from its canonical
formula -- the papers' table (part4b:1630-1647, read directly) short-
circuits (dashes) after the first true flag, so the dashes must be
filled in.  Then run all 6 possible precedence orderings and record
every assignment change, with its closure recomputed and sigma'd.

FLAG EVALUATIONS (each justified from the canonical formula; every
reading-dependent case is tested both ways -- round 10: there are
now FOUR variant readings, m_tau abs G, ell_A G, ell_A L (the kind
ambiguity), and sin2thW G):
  alpha_s     (F,F,T)  window Phi(5,12) meets gauge window
  m_tau/m_mu  (F,F,T)  window Phi(6,13) meets gauge window
  m_tau abs   (T,F,F)  P: dimensional/Planck (papers).  G: ROUND-9
                       CORRECTION (M3, Addendum 57) -- the papers'
                       G-predicate is mechanical over the formula's
                       EXPRESSION TREE (part4b rem:sp36-syntactic),
                       under which alpha_s and v are closed symbols,
                       exactly as b/s's L(tau/mu) is (that is what
                       keeps b/s at F below).  This script's original
                       dash-fill expanded the constituents (alpha_s =
                       a_GUT e^(Phi(5,12)), v likewise) and got G=T --
                       an inconsistent grading, the same defect class
                       as review F4.  The constituent-expansion
                       reading is retained as a tested VARIANT.
  ell_A       (T,F,?)  P: r_d Planck-anchored (papers).  G: the
                       cosmological formula is built from geometric
                       pi-forms; no gauge-window exponential found ->
                       G = F primary, T tested as variant.
  sin2thW     (F,T,?)  L: observer-local ratio (papers).  G: the
                       closure's canonical formula tan thW =
                       (N(14)/sqrt pi)/N(13) is POINT values (G = F);
                       but part4b:83 also gives the couplings as Phi
                       values over d=5..13/5..14 (G = T under that
                       reading).  BOTH tested.
  Omega_m     (F,T,F)  1/pi geometric; no window.
  theta_C     (F,F,F)  static normalisations inside arccos (papers).
  b/s         (F,F,F)  papers' canonical reading (A13).
  theta_23    (F,F,F)  papers' canonical reading (A13).

SOURCE MAP: Absolute->19, Gauge->14, Observer->5, Amplitude->7
(Amplitude = no flag true, order-independent).
"""

import itertools
import math

from scipy.special import digamma

PI = math.pi


def R(d):
    return math.gamma((d + 1) / 2.0) / math.gamma((d + 2) / 2.0)


def alpha(d):
    return R(d) ** 2 / 4.0


TYPE_OF_FLAG = {"P": ("Absolute", 19), "L": ("Observer", 5),
                "G": ("Gauge", 14)}


def assign(flags, order):
    for f in order:
        if flags[f]:
            return TYPE_OF_FLAG[f]
    return ("Amplitude", 7)


OBS = [
    ("alpha_s",    dict(P=0, L=0, G=1), None),
    ("m_tau/m_mu", dict(P=0, L=0, G=1), None),
    ("m_tau abs",  dict(P=1, L=0, G=0), dict(P=1, L=0, G=1)),
    # round-10 m-E: ell_A's SECOND reading-dependent axis added -- the
    # disclosed kind ambiguity (mass-ratio vs local-ratio) is an
    # L-flag variant (T,T,F), not a G variant; tested as variant here
    # via a second OBS row (the scan handles each reading separately)
    ("ell_A",      dict(P=1, L=0, G=0), dict(P=1, L=0, G=1)),
    ("ell_A (L-variant: kind local-ratio)",
                   dict(P=1, L=0, G=0), dict(P=1, L=1, G=0)),
    ("sin2thW",    dict(P=0, L=1, G=0), dict(P=0, L=1, G=1)),
    ("Omega_m",    dict(P=0, L=1, G=0), None),
    ("theta_C",    dict(P=0, L=0, G=0), None),
    ("b/s",        dict(P=0, L=0, G=0), None),
    ("theta_23",   dict(P=0, L=0, G=0), None),
]

CANON = ("P", "L", "G")
ORDERS = list(itertools.permutations(("P", "L", "G")))


def sigma_consequences(name, dstar):
    """Closure under the alternative source, sigma'd vs data."""
    if name == "m_tau abs":
        lead = 1754.20
        pred = lead * math.exp(alpha(dstar) / 2)
        return pred, (pred - 1776.86) / 0.12, "MeV vs 1776.86(12)"
    if name == "sin2thW":
        lead = 0.22860
        k = {5: 8, 14: 2, 19: 2, 7: 4}[dstar]
        pred = lead * math.exp(alpha(dstar) / k)
        return pred, (pred - 0.23122) / 0.00004, "vs 0.23122(4)"
    if name.startswith("ell_A"):
        lead = 301.44 / math.exp(alpha(19) / 2)
        pred = lead * math.exp(alpha(dstar) / 2)
        return pred, (pred - 301.6) / 0.09, "vs 301.6(9)"
    return None, None, ""


def main():
    print("=" * 74)
    print("P > L > G VACUITY CHECK")
    print("=" * 74)
    multi = [(n, f) for n, f, _ in OBS if sum(f.values()) >= 2]
    print(f"  observables with >= 2 true flags (primary readings):"
          f" {[n for n, _ in multi] or 'NONE'}")
    if not multi:
        print("  => VACUOUS: precedence deletable.")
    else:
        print("  => NOT VACUOUS: the order is load-bearing where flagged.")
    print()
    print("  full ordering scan (primary readings + tested variants):")
    fired = []
    for name, flags, variant in OBS:
        for tag, fl in [("primary", flags)] + ([("variant", variant)]
                                               if variant else []):
            canon_t, canon_d = assign(fl, CANON)
            alts = {}
            for o in ORDERS:
                t, d = assign(fl, o)
                if d != canon_d:
                    alts[d] = alts.get(d, []) + ["".join(o)]
            if alts:
                fired.append((name, tag, canon_d, alts, fl))
    if not fired:
        print("    no observable's assignment changes under any of the")
        print("    six orderings -> precedence VACUOUS, item deletable.")
        return
    for name, tag, canon_d, alts, fl in fired:
        print(f"    {name} [{tag}] flags {fl}: canonical d* = {canon_d};"
              f" alternatives:")
        for d, orders in alts.items():
            pred, sig, unit = sigma_consequences(name, d)
            s = (f" -> closure {pred:.5g} {unit}: {sig:+.0f} sigma"
                 if pred else "")
            print(f"      d* = {d} under {orders}{s}")
    print()
    print("=" * 74)
    print("VERDICT")
    print("=" * 74)
    print("  ROUND-9 CORRECTED VERDICT: on the UNIFORM primary readings")
    print("  (the papers' expression-tree predicate, applied the same way")
    print("  to every row) NO observable is multi-flag -- the precedence")
    print("  is VACUOUS on primary readings and the order never fires.")
    print("  Under the tested VARIANT readings (constituent expansion for")
    print("  m_tau abs; window content for ell_A; coupling-running for")
    print("  sin2thW; ell_A kind, round 10) the order fires and every")
    print("  assignment-changing ordering is excluded at 13-109 sigma.")
    print("  So the anchoring is")
    print("  CONDITIONAL: 'data-anchored' holds only if the variant")
    print("  grading is adopted; on the uniform grading the residue item")
    print("  is deletable as vacuous.  A52's original 'NOT VACUOUS'")
    print("  verdict rested on an inconsistent dash-fill (see docstring)")
    print("  and is superseded (Addendum 57).")


if __name__ == "__main__":
    main()
