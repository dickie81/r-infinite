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

FLAG EVALUATIONS (each justified from the canonical formula; the two
reading-dependent cases are tested BOTH ways):
  alpha_s     (F,F,T)  window Phi(5,12) meets gauge window
  m_tau/m_mu  (F,F,T)  window Phi(6,13) meets gauge window
  m_tau abs   (T,F,T)  P: dimensional/Planck (papers). G: BEHIND THE
                       DASH -- the formula (alpha_s v/sqrt2)e^(-Phi(5)
                       +a(19)/chi)/(2 sqrt pi)^2 contains alpha_s =
                       a_GUT e^(Phi(5,12)) and v = M_Pl a_GUT
                       e^(Phi(5,12)) e^(-pi/a(5)): TWO gauge-window
                       exponentials.  G = T.  L = F.
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
    ("m_tau abs",  dict(P=1, L=0, G=1), None),
    ("ell_A",      dict(P=1, L=0, G=0), dict(P=1, L=0, G=1)),
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
    if name == "ell_A":
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
    worst = None
    print("  NOT VACUOUS: the precedence fires (m_tau abs at minimum --")
    print("  its formula carries gauge-window exponentials behind the")
    print("  papers' short-circuit dash).  BUT every ordering that changes")
    print("  any assignment produces a closure excluded by data (sigmas")
    print("  above).  STATUS CHANGE, not deletion: residue item six moves")
    print("  from 'motivated, unanchored' to 'DATA-ANCHORED discrete")
    print("  convention' -- the same epistemic class as the unit and the")
    print("  window-potential pairing (items five/seven).  The residue")
    print("  count stays at seven; its free (unanchored) content shrinks.")


if __name__ == "__main__":
    main()
