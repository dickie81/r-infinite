#!/usr/bin/env python3
"""THE TORSION-EXCEPTIONAL SELECTION (Theorem 1j, round-57
adjudication MODIFY applied): the kernel's two-field CLASS anatomy,
and the chi_-3 pairing RE-MOTIVATED given the pairing-act.
Category (a): classical unit-group theory + the committed 1h/1i
machinery; no data, no closures, no RH/GRH, no semiclassics
(Check 7); the hypothesis is nowhere an input to the arithmetic
(Check 8 -- see GRADING below for exactly where C1 enters).

CONTEXT.  Round-15 M3: the odd bridge (1c) holds verbatim for
every odd real primitive chi, so pairing the odd feature with
chi_-3 by CONDUCTOR-MINIMALITY was graded a convention -- the
third member of the selection-convention residue class.  This
file attacks that member.

THE CLASSICAL CENSUS (J1).  Among imaginary quadratic fields the
unit-group torsion is |mu| in {2, 4, 6}: |mu| = 6 uniquely at
disc -3 (Q(zeta_3), the ring Z[omega] with its six units) and
|mu| = 4 uniquely at disc -4 (Q(zeta_4) = Q(i)); every other
field has |mu| = 2.  Gated by direct unit count over all
fundamental discriminants |d| <= 10^4; the universal closes
classically (round-57 F8): a root of unity solves a^2 - d b^2 = 4
(or x^2 + |d/4| y^2 = 1), and b != 0 (y != 0) forces |d| <= 4, so
no disc beyond the scan can carry extra torsion (Dirichlet; units
of imaginary quadratic fields).

THE KERNEL'S TWO FIELDS -- AT CLASS LEVEL (J2, J3 -- the 1h
anatomy re-read).  The clock-invisibility criterion of Theorem
1h is ker(., -1)_2 = ker(., -4)_2 -- i.e. THE DISC CHARACTER OF
THE mu_4 FIELD, localized at the clock prime (gated on all
eight classes); and the invisible UNIT direction is {1,
cls(-3)} -- THE mu_6 FIELD'S DISCRIMINANT CLASS, whose local
extension Q_2(sqrt(-3)) = Q_2(zeta_3) is the unramified
quadratic (gated).  The mu_4 field itself is 2-ramified
(cls(-4) = 7, clock-VISIBLE).  Round-58 precision: the anatomy
is CLASS-level, not field-determining -- (., -3)_2 = (., -11)_2
identically (every d = 5 mod 8 gives the same local character),
so the dyadic kernel alone does not pin the mu_6 field; what
privileges disc -3 among its class representatives is the
torsion census (J1) together with the T11 pairing-act.  With
that stated: the kernel's anatomy is built from the two
torsion-exceptional fields' DISC CLASSES -- invisibility = the
mu_4 disc character's kernel; the invisible unit direction =
the mu_6 disc class -- and 1h's structure is their joint
localization at class level.

THE PAIRING RE-MOTIVATED, GIVEN THE PAIRING-ACT (J4, J5, J6).
Round-57 F1 (MAJOR, verdict MODIFY) struck this file's first
framing -- "re-founded", "reduces to a consequence", the J6
print's denial that any order principle was in play while the
gate literally computes a maximum -- because routing colour
through torsion imports the PAIRING-ACT: that the odd feature
is paired with an imaginary quadratic unit structure at all,
which Theorem 11 / Def 6.1 do not entail (chi_-4, the mu_4
partner, is the live alternative).  Gloss note (round 59): the
paper folds T11's colour identification into the act itself
("pairing with the colour field's character"), under which
chi_-4 is excluded by the act; this file states the weaker act
and lets the T11-anchored maximum exclude chi_-4 -- the total
conditional content is identical (colour = mu_6 is C1-charged
in GRADING on either cut).  The adjudicated state:
GIVEN the pairing-act, torsion-maximality -- |mu| = 6, the
extremal structural property Theorem 11 ALREADY load-bears (the
su(3) roots ARE the units mu_6 of Z[omega]; the cos(pi/6)
projection exists among imaginary quadratic rings iff disc =
-3) -- selects Q(zeta_3) uniquely among all imaginary quadratic
fields (J6), hence chi_-3 uniquely among all odd real primitive
characters, and conductor-minimality is then ENTAILED (|disc| =
3 is a fortiori the minimal conductor, J4), not an independent
principle.  The mu_6 field's 2-localization lands on the
invisible unit direction at class level (J3), and its epsilon
support is the two-place pair {3, inf} with the quarter-turn
values (J5, citing 1i's gated decomposition).

GRADING (honest, per Check 8; round-57 adjudication RESOLVED).
The arithmetic is theorem-grade throughout: the torsion census
with its classical closure, the two-field class anatomy, the
uniqueness of the mu_6 maximum, minimality-entailed-given-the-
pairing-act.  What remains C1-conditional is what was already
C1-conditional before this file: that COLOUR is the mu_6
structure (Theorem 11's identification -- the dictionary's
entry, not re-derived here).  Adjudicated verdict (round 57,
MODIFY): the chi_-3 member of the selection-convention class is
RE-MOTIVATED, not reduced -- the pairing-act persists as the
member's conventional content, and given it, minimality is
entailed.  The class keeps three members; the seven-item
residue COUNT is unchanged.  No number changes; no closure; the
grammar-reading question stays open (this narrows it again: the
colour entry's dyadic shadow IS the invisible unit coordinate
at class level -- the 1e(iv) identification relocated, not a
new forcing).
"""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cascade_local_family import hilbert, same_class

D2 = [1, 3, 5, 7, 2, 6, 10, 14]
H = [1, 5, 2, 10]


def cls(x):
    return next(c for c in D2 if same_class(x, c))


def squarefree(n):
    i = 2
    while i * i <= n:
        if n % (i * i) == 0:
            return False
        i += 1
    return True


def fundamental_discs(bound):
    """Fundamental discriminants d < 0 with |d| <= bound."""
    out = []
    for d in range(-3, -bound - 1, -1):
        if d % 4 == 1 and squarefree(-d):
            out.append(d)
        elif d % 4 == 0:
            m = d // 4
            if squarefree(-m) and (-m) % 4 in (1, 2):
                out.append(d)
    return out


def torsion(d):
    """|mu| of the imaginary quadratic field of fundamental disc d,
    by direct unit enumeration (norm-1 elements of the maximal
    order; the enumeration windows cover every root of unity)."""
    count = 0
    if d % 4 == 1:                       # (a + b sqrt(d))/2, a = b mod 2
        for a in range(-4, 5):
            for b in range(-4, 5):
                if (a - b) % 2 == 0 and a * a - d * b * b == 4:
                    count += 1
    else:                                # d = 4m: elements x + y*sqrt(m)
        m = -d // 4
        for x in range(-2, 3):
            for y in range(-2, 3):
                if x * x + m * y * y == 1:
                    count += 1
    return count


def main():
    print("=" * 74)
    print("THE TORSION-EXCEPTIONAL SELECTION (Theorem 1j)")
    print("=" * 74)

    fund = fundamental_discs(10000)

    # ---- J1: the torsion census
    print()
    print("J1 torsion census over all fundamental discs |d| <= 10^4:")
    w6 = [d for d in fund if torsion(d) == 6]
    w4 = [d for d in fund if torsion(d) == 4]
    bad = [d for d in fund if torsion(d) not in (2, 4, 6)]
    ok1 = w6 == [-3] and w4 == [-4] and not bad
    print(f"   {len(fund)} discs: |mu| = 6 exactly at {w6}, |mu| = 4"
          f" exactly at {w4}, all others |mu| = 2   "
          f"{'PASS' if ok1 else 'FAIL'}")

    # ---- J2: invisibility = the mu_4 field's disc character, localized
    print()
    # round-57 F4: the identity conjunct cannot fail (-4 and -1 share a
    # square class; the closed formula reads the valuation mod 2), and
    # the ker conjunct re-gates 1h L8a -- a consistency exhibit of the
    # identification, declared per the L7b standard
    print("J2 the 1h invisibility criterion is the mu_4 field's disc")
    print("   character at the clock prime (exhibit; see comment):")
    ok2 = all(hilbert(c, -4, 2) == hilbert(c, -1, 2) for c in D2)
    ok2 &= sorted(H) == sorted(c for c in D2 if hilbert(c, -4, 2) == 1)
    print(f"   (., -4)_2 == (., -1)_2 on all 8 classes, and"
          f" ker(., -4)_2 = H   {'PASS' if ok2 else 'FAIL'}")

    # ---- J3: the invisible unit direction is the mu_6 field's disc
    print()
    print("J3 the invisible unit direction is the mu_6 field's disc:")
    Hu = sorted(u for u in (1, 3, 5, 7) if hilbert(u, -1, 2) == 1)
    ok3 = Hu == sorted({1, cls(-3)})
    ok3 &= (-3) % 8 == 5                      # unramified type: Q_2(zeta_3)
    ok3 &= cls(-4) not in H                   # the mu_4 field is 2-ramified
    print(f"   H cap units = {Hu} = {{1, cls(-3)}}; -3 = 5 mod 8"
          f" (Q_2(zeta_3), unramified); cls(-4) = {cls(-4)} not in H   "
          f"{'PASS' if ok3 else 'FAIL'}")

    # ---- J4: conductor-minimality as a consequence
    print()
    # round-57 F4: entailed by J1 (if the census holds, min |d| = 3
    # follows) -- a consistency exhibit, declared; round-57 F1/F3: the
    # consequence is CONDITIONAL on the pairing-act
    print("J4 minimality entailed within the pairing (exhibit, from J1):")
    ok4 = abs(w6[0]) == min(abs(d) for d in fund) if len(w6) == 1 else False
    print(f"   |disc(mu_6 field)| = {abs(w6[0])} = the minimal conductor"
          f" over all scanned odd real primitive chi_d   "
          f"{'PASS' if ok4 else 'FAIL'}")

    # ---- J5: the epsilon tie (1i's decomposition, re-exhibited)
    print()
    print("J5 the mu_6 character's two-place epsilon support (1i):")
    import cmath, math
    e3 = sum((1 if u % 3 == 1 else -1) * cmath.exp(2j * cmath.pi * u / 3)
             for u in (1, 2)) / math.sqrt(3)
    ok5 = abs(e3 - 1j) < 1e-9        # (round-57 F6: the former second
    #  conjunct was algebraically identical; eps_inf = -i is the classical
    #  constant, not computed here -- this line is 1i's re-exhibit)
    print(f"   eps_3(chi_-3) = +i; with the classical eps_inf(sgn) = -i"
          f" the product is +1 -- support {{3, inf}} (1i re-exhibit)   "
          f"{'PASS' if ok5 else 'FAIL'}")

    # ---- J6: the matching is unique GIVEN the pairing-act (round-57
    # F1: the first version printed "no order principle" while literally
    # computing a maximum -- struck; the selection is conditional on the
    # pairing-act, which T11 does not entail.  Round-57 F4: this gate is
    # entailed by J1 (a consistency exhibit, the L7b class), declared)
    print()
    print("J6 the T11 mu_6 requirement matches a unique field (exhibit,")
    print("   entailed by J1; selection conditional on the pairing-act):")
    mx = max(torsion(d) for d in fund)
    argmax = [d for d in fund if torsion(d) == mx]
    ok6 = mx == 6 and argmax == [-3]
    print(f"   max |mu| = {mx} uniquely at d = {argmax} => given the"
          f" pairing-act, chi_-3 follows   {'PASS' if ok6 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  The kernel's anatomy is the joint localization, at class")
    print("  level, of the only two torsion-exceptional imaginary")
    print("  quadratics: invisibility is the mu_4 field's disc character,")
    print("  the invisible unit direction is the mu_6 field's disc class.")
    print("  Given the pairing-act, torsion-maximality -- the property")
    print("  Theorem 11 already load-bears -- selects the mu_6 field")
    print("  uniquely, and conductor-minimality is entailed, not an")
    print("  independent principle.  Adjudicated (round 57, MODIFY): the")
    print("  chi_-3 member is re-motivated, not reduced -- the pairing-")
    print("  act persists as the conventional content.  Residue count")
    print("  unchanged; no closure; grammar-reading question stays open.")


if __name__ == "__main__":
    main()
