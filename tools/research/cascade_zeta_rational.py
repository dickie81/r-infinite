#!/usr/bin/env python3
"""THE ARITHMETIC-PRIMARY FORM (Theorem 1o): 1n's parity
equivalent re-expressed on zeta itself -- the sup's twist points
are the Euler-rational points, and the inf's twist points mirror
exactly onto the trivial zeros.  ROUND-75 CORRECTIONS APPLIED (F1
MAJOR, F2): see the CONTEXT and (iii) blocks below.  Category
(a): exact symbolic
arithmetic (sympy Bernoulli/zeta) plus the Gamma-side argmax
recomputation; no data, no closures, no RH/GRH, no semiclassics
(Check 7); the hypothesis is nowhere an input (Check 8).

CONTEXT.  Theorem 1n characterized the variational sup three
ways (parity, Euler-null spheres, minimal horizon budget), each
an equivalence with the forcing open.  1n's obstruction
equivalent is avatar-side (chi of spheres) -- deprecated as a
register by the paper's Theorem-1 Remark, 'The paper never uses
the avatar; the arithmetic is primary' -- while its parity
equivalent is already arithmetic (integer parity of tower
labels), stated on the layer index.  (Round-75 F2 struck this
file's first claim that BOTH 1n equivalents were avatar-side,
and the 'canonical register' assertion: the Remark deprecates
the avatar in derivations, it does not rank characterization
registers.)  This file expresses the dichotomy on zeta's
special-value structure -- the paper's primary object:

  (i)  Under Definition 2.1 (twist s = d+1), the sup labels'
       twist points are s = 8, 20, 218, and the four
       distinguished layers' twists are {6, 8, 20, 218} -- ALL
       EVEN, where Euler's theorem gives zeta(s) = rational *
       pi^s (zeta(6) = pi^6/945, zeta(8) = pi^8/9450; gated
       exactly at all four via Bernoulli numbers).  The inf
       labels' twists 7, 21, 219 are odd: no closed form
       (zeta at odd integers is arithmetically opaque).
  (ii) THE MIRROR DICHOTOMY: under the functional equation
       s -> 1-s, the sup twists mirror to NONZERO RATIONALS --
       zeta(-5) = -1/252, zeta(-7) = 1/240, zeta(-19) =
       174611/6600, zeta(-217) != 0 (exact) -- while the inf
       twists mirror EXACTLY onto the trivial zeros:
       zeta(-6) = zeta(-20) = zeta(-218) = 0.  Among the eight
       labelings the sup is the UNIQUE one all of whose twist
       points avoid the trivial-zero mirror set.
  (iii) THE LEDGER CROSS-LINK: zeta(6) = pi^6/945 IS the frozen
       ledger's m_tau fork constant -- the row
       'pi^6/945-vs-alpha(14)/2' reads, in the tower's own
       dictionary, 'zeta at the volume-max layer's twist point
       vs the compliance at the U(1) layer'.  Round-75 F1
       (MAJOR) struck this file's first 'novel registration'
       claim ('no repo surface previously identified pi^6/945
       as zeta(6)'): the identification is the fork's FOUNDING
       FACT -- cascade_adelic_compensator.py tests ln zeta(6)
       at s = d+1, d = 5, against the papers' alpha(14)/2 (the
       'adelic survivor') and lists pi^6/945 as zeta(6) in its
       compensator menu; the Check-4 grep had missed tools/.
       What is new here is only the tie to the twist-parity
       structure: the fork constant is zeta at d_V's twist
       point, a member of the sup's Euler-rational twist set
       {6, 8, 20, 218}.  No closure, no data; Belle II
       adjudicates the fork exactly as before.

GRADING (honest, per Check 8; the campaign grammar).  Still an
equivalence: WHY the labels avoid the trivial-zero mirror set is
the residual selection content, so the forcing stays OPEN and
Theorem 1k's second given persists.  What changes is the
characterization's placement: the dichotomy now lives on zeta's
special-value structure (odd d <-> even s, a Definition-2.1
biconditional -- declared; the parity form was already
arithmetic, the zeta-form its classical decoration), with the
avatar-side chi reading demoted to shadow status.  No number
changes; no closure.
"""

import itertools
import math

import sympy as sp
from scipy.special import gammaln

PI = math.pi
PAIRS = [(6, 7), (19, 20), (217, 218)]
LABS = list(itertools.product(*PAIRS))
DISTINGUISHED = (5, 7, 19, 217)


def Om(d):
    return 2 * math.exp((d + 1) / 2 * math.log(PI) - gammaln((d + 1) / 2))


def I(l0, l1, l2):
    return (Om(5) / Om(l0)) ** 2 * Om(l1) * Om(l2)


def main():
    print("=" * 74)
    print("THE ARITHMETIC-PRIMARY FORM (Theorem 1o)")
    print("=" * 74)

    vals = {l: I(*l) for l in LABS}
    sup = max(vals, key=vals.get)
    inf = min(vals, key=vals.get)
    sup_tw = tuple(d + 1 for d in sup)
    inf_tw = tuple(d + 1 for d in inf)
    dist_tw = tuple(d + 1 for d in DISTINGUISHED)

    # ---- Z1: the twist parities (argmax recomputed; Def-2.1 map)
    print()
    print("Z1 twist points under Definition 2.1 (s = d+1):")
    ok1 = sup == (7, 19, 217) and inf == (6, 20, 218)
    ok1 &= sup_tw == (8, 20, 218) and all(s % 2 == 0 for s in sup_tw)
    ok1 &= inf_tw == (7, 21, 219) and all(s % 2 == 1 for s in inf_tw)
    ok1 &= dist_tw == (6, 8, 20, 218) and all(s % 2 == 0 for s in dist_tw)
    print(f"   sup {sup} -> twists {sup_tw} (all even); inf {inf} ->")
    print(f"   twists {inf_tw} (all odd); the four distinguished layers'")
    print(f"   twists {dist_tw} all even (odd d <-> even s: the Def-2.1")
    print(f"   biconditional -- declared)   {'PASS' if ok1 else 'FAIL'}")

    # ---- Z2: Euler rationality at the even twist points (exact)
    print()
    print("Z2 Euler rationality zeta(s)/pi^s in Q at the even twists:")
    ok2 = all(sp.simplify(sp.zeta(s) / sp.pi ** s).is_rational
              for s in dist_tw)
    ok2 &= sp.simplify(sp.zeta(6) - sp.pi ** 6 / 945) == 0
    ok2 &= sp.simplify(sp.zeta(8) - sp.pi ** 8 / 9450) == 0
    print(f"   zeta(6) = pi^6/945, zeta(8) = pi^8/9450; zeta(20), zeta(218)")
    print(f"   rational x pi^s (Bernoulli, exact) -- the sup's twist points")
    print(f"   are zeta's Euler-closed-form points; the inf's (7, 21, 219)")
    print(f"   are odd: no closed form is known   {'PASS' if ok2 else 'FAIL'}")

    # ---- Z3: the mirror dichotomy (exact trivial-zero avoidance)
    print()
    print("Z3 the functional-equation mirror s -> 1-s:")
    sup_mirror = [sp.zeta(1 - s) for s in sup_tw]
    inf_mirror = [sp.zeta(1 - s) for s in inf_tw]
    ok3 = all(m != 0 and sp.simplify(m).is_rational for m in sup_mirror)
    ok3 &= all(m == 0 for m in inf_mirror)
    ok3 &= sup_mirror[0] == sp.Rational(1, 240)          # zeta(-7)
    ok3 &= sup_mirror[1] == sp.Rational(174611, 6600)    # zeta(-19)
    ok3 &= sp.zeta(-5) == sp.Rational(-1, 252)           # d_V's mirror
    print(f"   sup twists mirror to NONZERO rationals: zeta(-7) = 1/240,")
    print(f"   zeta(-19) = 174611/6600, zeta(-217) != 0 (and d_V's")
    print(f"   zeta(-5) = -1/252); inf twists mirror EXACTLY onto the")
    print(f"   trivial zeros: zeta(-6) = zeta(-20) = zeta(-218) = 0   "
          f"{'PASS' if ok3 else 'FAIL'}")

    # ---- Z4: uniqueness among the eight labelings
    print()
    print("Z4 uniqueness: the sup alone avoids the trivial-zero mirrors:")
    avoiders = [l for l in LABS
                if all(sp.zeta(1 - (d + 1)) != 0 for d in l)]
    counts = {l: sum(1 for d in l if sp.zeta(1 - (d + 1)) == 0)
              for l in LABS}
    ok4 = avoiders == [sup] and counts[inf] == 3
    print(f"   avoiders among the 8: {avoiders} (exactly the sup); the inf")
    print(f"   carries 3 trivial-zero mirrors; every non-sup labeling")
    print(f"   carries at least one   {'PASS' if ok4 else 'FAIL'}")

    # ---- Z5: the ledger cross-link (round-75 F1/F4 rebuilt: the
    # identification pre-exists -- the fork's founding fact, see the
    # docstring; the old sole conjunct was a byte-duplicate of Z2's
    # zeta(6) conjunct (5 + 1 evaluates before sympy sees it).  The
    # genuine gate now: the frozen ledger row present verbatim in the
    # paper, plus the Z2 re-exhibit, declared as such)
    print()
    print("Z5 the ledger cross-link (identification pre-existing, round-75")
    print("   F1; new content: the tie to the twist-parity structure):")
    import os
    root = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        "..", "..")
    paper = open(os.path.join(root, "riemann-indistinguishability.md"),
                 encoding="utf-8").read()
    ok5 = "\u03c0\u2076/945-vs-\u03b1(14)/2 fork" in paper
    ok5 &= sp.simplify(sp.zeta(6) - sp.pi ** 6 / 945) == 0  # Z2 re-exhibit
    print(f"   the frozen ledger row 'pi^6/945-vs-alpha(14)/2 fork' present")
    print(f"   verbatim in the paper; zeta(d_V + 1) = pi^6/945 (Z2")
    print(f"   re-exhibit, declared).  The fork constant -- identified as")
    print(f"   zeta(6) by the adelic compensator (its 'survivor') -- sits")
    print(f"   at d_V's twist point in the sup's Euler-rational twist set")
    print(f"   {{6, 8, 20, 218}}.  No closure; Belle II adjudicates as")
    print(f"   before   {'PASS' if ok5 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  1n's parity dichotomy has an exact arithmetic form on the")
    print("  paper's primary object: the sup's twist points are zeta's")
    print("  Euler-rational points, whose functional-equation mirrors are")
    print("  nonzero rationals; the inf's twist points mirror exactly")
    print("  onto the trivial zeros, and the sup is the unique labeling")
    print("  avoiding that degenerate mirror set.  The dichotomy now")
    print("  lives on zeta's special-value structure, the chi reading its")
    print("  avatar-side shadow (round-75 F2: no register ranking claimed).")
    print("  Still an equivalence -- why the labels")
    print("  avoid the trivial-zero mirrors is the residual content; the")
    print("  forcing stays open; 1k's second given persists.  The m_tau")
    print("  ledger constant pi^6/945 is zeta(6) -- the fork's founding")
    print("  fact (adelic compensator), here tied to d_V's twist point in")
    print("  the Euler-rational twist set.  No number changes; no closure.")


if __name__ == "__main__":
    main()
