#!/usr/bin/env python3
"""THE PAIRING-ACT'S ANATOMY (Theorem 1r): the act decomposed, and
the live alternative excluded thrice on committed anchors.
Category (a): integer/character arithmetic, Hilbert symbols, a
reduced-form class-number count, and one classical L-value; no
data, no closures, no RH/GRH, no semiclassics (Check 7); the
hypothesis is nowhere an input (Check 8).

CONTEXT.  The round-57 adjudication left the selection class's
third member conditional on the PAIRING-ACT -- pairing the odd
feature (p_sgn = 0 at s = 6.2569, an object with no derived
address) with the colour field's character -- and recorded chi_-4
as "a live alternative partner that only the order or the
pairing-act excludes."  Theorem 1j is stable (round 59) in that
adjudicated form.  This file attacks the act directly: decompose
it, and test the live alternative against committed-anchored
act-forms (the ordering between them and the colour gloss is
stated in GRADING -- round-81 F2).

  P1 THE TARGET SPACE IS THE CENSUS SPACE.  The odd bridge's
     partner family -- every odd real primitive chi (1c) -- is
     classically the Kronecker characters chi_d of negative
     fundamental discriminants (real primitive <=> fundamental-
     disc Kronecker: classical, cited; parity = sign of d).
     Census side gated: all 3043 discs to 10^4 give
     chi_d(-1) = -1.  Re-gated small-conductor facts (committed
     at 1c): q = 2 admits no primitive character; q = 3 exactly
     one, odd.
  P2 THE DYADIC ROUTE (act-form W1).  1j's committed description
     of the outcome -- "the selected field's dyadic shadow is the
     invisible unit direction" -- promoted to an act-form: the
     partner's disc class lies NONTRIVIALLY in H cap units =
     {1, cls(-3)}.  W1 names no field, no mu_6, no T11.  Under W1
     the candidate slice is cls(-3)'s class (d = 5 mod 8; 1014 of
     3043; equivalently chi_d(2) = -1, the clock prime inert --
     1e(iv)'s colour-at-2 fact, gated as the slice's iff on odd
     discs); the class-level caveat is honored (-11 in the slice;
     no field pinned -- gated |slice| > 1); and chi_-4 IS EXCLUDED
     BY 1h'S KERNEL ALONE (cls(-4) = 7 not in H; chi_-8 too,
     cls = 14).
  P3 THE CONDUCTOR ROUTE (act-form W2).  1d's committed adelic
     fact -- the finite potential carried jointly by p = 2 and
     p = 3 -- gives the act-form: the partner's conductor is a
     carrying prime.  Conductor 2 admits no primitive character;
     conductor 3 exactly one, odd (P1): W2 pins chi_-3 OUTRIGHT
     in the whole family ({d : |d| in {2,3}} = {-3}, gated), and
     chi_-4 is excluded again (4 not a carrying prime).
  P4 THE BRIDGE'S CONSTANT ALREADY CARRIES mu_6.  The committed
     1c constant L(1, chi_-3) = pi/(3 sqrt 3) is Dirichlet's
     class-number formula 2 pi h/(w sqrt|d|) at (h, w, |d|) =
     (1, 6, 3): h(-3) = 1 gated by reduced-form count, w = 6 the
     census's unit count, the identity symbolic, the numeric
     L(1) re-gated by period-3 block summation; mu_4 cross-check
     L(1, chi_-4) = 2 pi/(4*2) = pi/4 (Leibniz) gated.  The
     torsion count 6 that T11's mu_6 requirement matches is
     ALREADY THE DENOMINATOR of the odd bridge's own committed
     constant.
  P5 THE TRIPLE EXCLUSION AND THE ROLES.  chi_-4 fails all three
     routes jointly (cls not in H; conductor not carrying;
     |mu| = 4 != 6 -- each gated).  The role asymmetry re-gated:
     the invisibility criterion IS (., -4)_2 = (., -1)_2 with
     kernel H (the candidate partner is the *instrument* of the
     committed filter), while cls(-3) is the invisible *datum*
     inside it.  (The identity (., -4)_2 = (., -1)_2 is
     class-level -- -4 = -1 times a square -- an exhibit, not an
     independent gate; the kernel computation is the gate.)

GRADING (honest; the round-57 typing applied in advance; the
round-81 F2/F3 corrections applied).  THE ACT PERSISTS.  None of
W1, W2, or the colour gloss (the act's standing form: pair with
the colour field's character, 1j) is entailed by the axioms;
each is a matching principle of the round-57 type (why the
invisible direction; why a carrying conductor; why mu_6), and
pairing-at-all -- the odd feature's missing address (Definition
6.1) -- is untouched.  THE ORDERING, STATED (round-81 F2: the
first draft said "act-forms strictly weaker than the colour
gloss", false for two of the three under predicate implication):
W1 is strictly weaker EXTENSIONALLY (pass set 1014 discs,
properly containing the gloss's {-3}); W2 and the census route
are extensionally EQUIVALENT to the gloss's output (each pins
{-3}) and weaker only in WHAT THEY NAME -- no field, no mu_6, no
T11 presupposed.  What changes is the live alternative's status:
chi_-4 fails three DISTINCT committed anchors (round-81 F3:
"independent" unqualified was wrong -- W2's exclusion is generic,
excluding every alternative partner whatsoever; the kernel and
census exclusions are the chi_-4-specific evidence, and the
kernel route is not mere 2-ramification: -56 (cls 2) and -24
(cls 10) are 2-ramified discs the kernel admits, together
covering both ramified kernel classes -- gated in P5; the sweep's
first exhibit "-28 (cls 1)" was false, round-82 F1: -28 is not a
fundamental disc and cls 1 is the trivial class, not
ramification), so the
round-57 recital's "only the order or the pairing-act excludes"
is superseded in exactly this sense.  No universal over
act-forms is claimed.  Three members and the seven-item residue
count stand; no number changes; no closure.
"""

import math
import os
import random
import sys

import sympy as sp
from sympy.functions.combinatorial.numbers import jacobi_symbol

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cascade_torsion_selection import H, cls, fundamental_discs, torsion

BOUND = 10 ** 4


def kronecker(d, n):
    """Kronecker symbol (d/n) for n >= 1."""
    if n == 0:
        return 0
    r = 1
    nn = n
    while nn % 2 == 0:
        nn //= 2
        if d % 2 == 0:
            return 0
        r *= 1 if d % 8 in (1, 7) else -1
    if nn > 1:
        num, den, j = d % nn, nn, 1
        while num != 0:
            while num % 2 == 0:
                num //= 2
                if den % 8 in (3, 5):
                    j = -j
            num, den = den, num          # reciprocity on the pre-swap
            if num % 4 == 3 and den % 4 == 3:   # pair (old den, old num)
                j = -j
            num %= den
        if den != 1:
            return 0
        r *= j
    return r


def chi_minus_one(d):
    """chi_d(-1) via the completed Kronecker symbol: chi_d(n) for
    n = |d| - 1 = -1 mod |d| (n coprime to d for fundamental d)."""
    return kronecker(d, abs(d) - 1)


def hilbert2(a, b):
    """Hilbert symbol (a, b)_2 for nonzero rationals (integers)."""
    def dec(x):
        v = 0
        while x % 2 == 0:
            v += 1
            x //= 2
        return v, x % 8

    va, ua = dec(a)
    vb, ub = dec(b)
    eps = ((ua - 1) // 2) * ((ub - 1) // 2)
    om = va * ((ub * ub - 1) // 8) + vb * ((ua * ua - 1) // 8)
    return (-1) ** ((eps + om) % 2)


def class_number(d):
    """h(d) for fundamental d < 0 by counting reduced forms
    (a, b, c), b^2 - 4ac = d, -a < b <= a <= c, b >= 0 if a == c."""
    h = 0
    a = 1
    while a * a <= -d // 3 + 1:
        for b in range(-a + 1, a + 1):
            num = b * b - d
            if num % (4 * a) == 0:
                c = num // (4 * a)
                if c >= a and not (a == c and b < 0):
                    h += 1
        a += 1
    return h


def main():
    print("=" * 74)
    print("THE PAIRING-ACT'S ANATOMY (Theorem 1r)")
    print("=" * 74)

    discs = fundamental_discs(BOUND)

    # ---- P1: the target space is the census space
    print()
    print("P1 the partner family = the census space:")
    ok1 = len(discs) == 3043
    ok1 &= all(chi_minus_one(d) == -1 for d in discs)
    # q = 2: the only character mod 2 is principal (imprimitive)
    ok1 &= [n for n in range(2) if math.gcd(n, 2) == 1] == [1]
    # q = 3: exactly one nontrivial character, quadratic, odd
    chars3 = [kronecker(-3, n) if math.gcd(n, 3) == 1 else 0
              for n in range(3)]
    ok1 &= chars3 == [0, 1, -1] and kronecker(-3, 2) == -1
    # the library cross-check, landed as a committed conjunct (round-81
    # F1: a session run is drafting until it lands in code); seeded:
    rng = random.Random(57)
    ok1 &= all(kronecker(a, n) == int(jacobi_symbol(a, n))
               for a, n in (((rng.randint(-500, 500) or 1),
                             rng.randrange(1, 400, 2))
                            for _ in range(500)))
    print("   every odd real primitive chi is a Kronecker chi_d, d < 0")
    print("   fundamental (classical, cited); census side gated: all")
    print(f"   {len(discs)} discs to 10^4 give chi_d(-1) = -1.  Re-gated:")
    print("   q = 2 has no primitive character (its unique character is")
    print("   principal); q = 3 has exactly one, odd (chi_-3(2) = -1).")
    print("   Symbol routine cross-checked in-code against the library")
    print("   Jacobi on 500 seeded cases (round-81 F1: landed as a gate).")
    print("   The act selects in the space the torsion census reads   "
          + ("PASS" if ok1 else "FAIL"))

    # ---- P2: the dyadic route (act-form W1)
    print()
    print("P2 act-form W1 (dyadic shadow = the invisible unit direction):")
    Hu = [h for h in H if h in (1, 3, 5, 7)]
    ok2 = Hu == [1, 5] and cls(-3) == 5
    slice5 = [d for d in discs if cls(d) == 5]
    ok2 &= -3 in slice5 and -11 in slice5 and len(slice5) == 1014
    ok2 &= len(slice5) > 1                      # no field pinned: honesty
    ok2 &= cls(-4) == 7 and 7 not in H          # chi_-4 excluded by 1h
    ok2 &= cls(-8) == 14 and 14 not in H        # chi_-8 too
    odd_discs = [d for d in discs if d % 2 != 0]
    ok2 &= all((kronecker(d, 2) == -1) == (cls(d) == 5) for d in odd_discs)
    print(f"   slice = cls(-3)'s class: {len(slice5)} of {len(discs)} discs")
    print("   (d = 5 mod 8; iff chi_d(2) = -1, the clock prime inert --")
    print("   1e(iv), gated on all odd discs); -11 in the slice and")
    print("   |slice| > 1 gated (class-level: NO field pinned -- round-57")
    print("   F2 honored).  chi_-4 excluded by the kernel alone:")
    print("   cls(-4) = 7 not in H (chi_-8: cls 14 not in H)   "
          + ("PASS" if ok2 else "FAIL"))

    # ---- P3: the conductor route (act-form W2)
    print()
    print("P3 act-form W2 (conductor among the carrying primes {2, 3}):")
    carrying = [d for d in discs if abs(d) in (2, 3)]
    ok3 = carrying == [-3]
    ok3 &= -4 not in carrying    # computed, not a literal (round-81 F7)
    print("   {d in census : |d| in {2, 3}} = [-3] (gated; no fundamental")
    print("   disc has |d| = 2, matching q = 2's empty primitive family):")
    print("   W2 pins chi_-3 outright in the whole family; chi_-4 excluded")
    print("   again (conductor 4 not a carrying prime)   "
          + ("PASS" if ok3 else "FAIL"))

    # ---- P4: the bridge's committed constant carries w = 6
    print()
    print("P4 L(1, chi_-3) = pi/(3 sqrt 3) is Dirichlet at (h, w) = (1, 6):")
    ok4 = class_number(-3) == 1 and torsion(-3) == 6
    ok4 &= sp.simplify(2 * sp.pi * 1 / (6 * sp.sqrt(3))
                       - sp.pi / (3 * sp.sqrt(3))) == 0
    # period-3 block summation: sum_k [1/(3k+1) - 1/(3k+2)] -> L(1)
    L = sum(1 / (3 * k + 1) - 1 / (3 * k + 2) for k in range(2 * 10 ** 6))
    ok4 &= abs(L - math.pi / (3 * math.sqrt(3))) < 1e-7
    # mu_4 cross-check: h(-4) = 1, w = 4, L(1, chi_-4) = pi/4 (Leibniz)
    ok4 &= class_number(-4) == 1 and torsion(-4) == 4
    L4 = sum(1 / (4 * k + 1) - 1 / (4 * k + 3) for k in range(2 * 10 ** 6))
    ok4 &= abs(L4 - math.pi / 4) < 1e-7
    # sanity on the counter: a nontrivial class number
    ok4 &= class_number(-23) == 3
    print("   h(-3) = 1 (reduced-form count; h(-23) = 3 sanity), w = 6 (the")
    print("   census's unit count): 2 pi h/(w sqrt 3) = pi/(3 sqrt 3)")
    print("   symbolically; L(1) re-gated numerically (period-3 blocks,")
    print("   < 1e-7); mu_4 cross-check L(1, chi_-4) = pi/4 gated.  The")
    print("   torsion count 6 that T11's mu_6 requirement matches is the")
    print("   denominator of the bridge's own committed constant   "
          + ("PASS" if ok4 else "FAIL"))

    # ---- P5: the triple exclusion, and the roles
    print()
    print("P5 the live alternative fails all three routes; the roles:")
    ok5 = (cls(-4) not in H            # W1
           and -4 not in carrying      # W2 (computed; generic exclusion)
           and torsion(-4) == 4)       # the mu_6 route: 4 != 6
    # round-82 F1 exhibit, gated: the kernel route is not mere
    # 2-ramification -- two 2-ramified (even) census discs it admits,
    # covering both ramified kernel classes {2, 10}:
    ok5 &= (-56 in discs and cls(-56) == 2
            and -24 in discs and cls(-24) == 10)
    kernel = [a for a in (1, 3, 5, 7, 2, 6, 10, 14) if hilbert2(a, -1) == 1]
    ok5 &= sorted(kernel) == sorted(H)
    ok5 &= all(hilbert2(a, -4) == hilbert2(a, -1)
               for a in (1, 3, 5, 7, 2, 6, 10, 14))   # exhibit: -4 = -1*sq
    print("   chi_-4: cls not in H (W1); conductor 4 not carrying (W2);")
    print("   |mu| = 4 != 6 (census) -- the round-57 'only the order or the")
    print("   pairing-act excludes' is superseded (three DISTINCT anchors;")
    print("   W2's exclusion generic -- the ordering in the docstring, F2/F3).")
    print("   Roles re-gated: ker(., -1)_2 =")
    print("   H exactly (the candidate partner's character is the committed")
    print("   filter's *instrument*; cls(-3) the invisible *datum* -- the")
    print("   (., -4)_2 = (., -1)_2 identity declared an exhibit, -4 being")
    print("   -1 times a square)   " + ("PASS" if ok5 else "FAIL"))

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  The pairing-act selects in exactly the census's space.  Under")
    print("  three committed-anchored act-forms -- W1 strictly weaker")
    print("  extensionally; W2 and the census equivalent to the gloss's")
    print("  output, weaker only in what they name (round-81 F2) -- the")
    print("  live alternative chi_-4 is excluded each time, and the routes")
    print("  consistently point at chi_-3 (W1 its class; W2 and the census")
    print("  the field).  The bridge's own committed")
    print("  constant pi/(3 sqrt 3) carries w = 6 by Dirichlet: the mu_6")
    print("  datum sits on both sides of the pairing.  THE ACT PERSISTS --")
    print("  no act-form is entailed, pairing-at-all is untouched, and no")
    print("  universal over act-forms is claimed.  Three members and the")
    print("  seven-item count stand.  No number changes; no closure.")
    # round-123 hardening (the A206/A208 standing commission): exit
    # gating added -- this instrument previously exited 0
    # unconditionally, so a printed FAIL could not fail a caller;
    # the exit code now carries the verdicts.  No verdict logic
    # changed.
    n_fail = sum(0 if ok else 1 for ok in (ok1, ok2, ok3, ok4, ok5))
    print()
    print(f"RESULT: {5 - n_fail} pass / {n_fail} fail (5 verdicts)")
    sys.exit(0 if n_fail == 0 else 1)


if __name__ == "__main__":
    main()
