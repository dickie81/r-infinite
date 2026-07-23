#!/usr/bin/env python3
"""THE REGULARITY FORCING, CONDITIONAL ON ONE PRINCIPLE
(Theorem 1p): the trivial-zero-avoidance equivalent in local
form -- the inf labels' twists are the POLES of Tate's
archimedean gamma-factor, and a single named non-degeneracy
principle forces the sup outright.  Category (a): exact symbolic
arithmetic (sympy) plus the Gamma-side argmax recomputation; no
data, no closures, no RH/GRH, no semiclassics (Check 7); the
hypothesis is nowhere an input (Check 8).

CONTEXT.  Theorems 1n/1o characterized the variational sup four
ways (minimal horizon budget; odd/Euler-null member;
zeta-Euler-rational twists; trivial-zero-mirror avoidance), each
an equivalence with the forcing open.  This file translates the
last into the LOCAL language of the tower's own Tate structure
(T2: the Gaussian as the self-dual vector at the real place,
Tate's gcd condition) and states the sharpest available result:

  (i)  THE GAMMA-FACTOR DICHOTOMY (exact).  Tate's archimedean
       gamma-factor -- the local functional equation's transfer
       coefficient, gamma_oo(s) = Gamma_R(1-s)/Gamma_R(s) for
       the trivial character with epsilon_oo = 1 -- has, on the
       tower, POLES exactly at the odd twists and finite nonzero
       values (closed forms: gamma(2) = -2 pi^2, gamma(6) =
       -4 pi^6/15, gamma(8) = 8 pi^8/315) exactly at the even
       twists.  Equivalently: the tower's own weight, continued
       through the functional equation to the mirror layer
       (s -> 1-s maps layer d to layer -(d+1)), is
       2/Gamma_R(-d) -- ZERO iff d is even.  The inf labels
       (6, 20, 218) sit at gamma-poles / measure-zero mirrors;
       the sup labels (7, 19, 217) at regular points / live
       mirrors.
  (ii) THE CONDITIONAL FORCING.  Adopt ONE principle -- the
       REGULARITY PRINCIPLE: the invariant's integer labels are
       regular points of the tower's local functional equation
       (equivalently: gamma_oo finite there; equivalently: the
       mirror weight nonzero).  Then at each straddling pair
       exactly one member qualifies, and the labeling is FORCED
       to (7, 19, 217) = the variational sup, with zero residual
       freedom; the variational definition, the parity rule,
       minimal horizon budget, zeta-rationality, and
       trivial-zero avoidance all follow as corollaries.  This
       is the first single-principle forcing of the sup.
  (iii) THE PRECISION BONUS.  The local form is strictly cleaner
       than 1o's global trivial-zero form: at s = 1 (layer
       d = 0) the gamma-factor has a pole and the mirror weight
       vanishes, yet zeta(1-1) = zeta(0) = -1/2 != 0 -- the
       global form has an exceptional point (where zeta's POLE,
       not a trivial zero, sits opposite), while the local form
       is uniform on ALL d >= 0.  On the label range d >= 1 the
       two coincide (gated biconditional).

GRADING (honest, per Check 8; the campaign grammar -- the
round-57/60 lessons applied in advance).  The forcing is
CONDITIONAL: the regularity principle is a NEW given, not
derived from A1-A4/T1-T2.  What makes it the sharpest form yet
of 1k's second given: it is a single, named, arithmetic
non-degeneracy condition on committed machinery -- the same
selection TYPE the framework already uses (T2's gcd condition:
'no extraneous zeros in Z(f,s)/Gamma_R(s)'; Theorem 7's 'every
feature has order one because variances are positive'; 1k's
no-tie margins) -- replacing 'take the max' and entailing all
four prior equivalents.  The open question NARROWS to: derive
the regularity principle from the cascade's axioms.  It is not
claimed derived; part0's remark keeps its open status.  No
number changes; no closure.
"""

import itertools
import math

import sympy as sp
from scipy.special import gammaln

PI = math.pi
PAIRS = [(6, 7), (19, 20), (217, 218)]
LABS = list(itertools.product(*PAIRS))


def GR(x):
    """Gamma_R at an exact rational point (sympy)."""
    return sp.pi ** (-sp.Rational(x, 2)) * sp.gamma(sp.Rational(x, 2))


def gamma_factor(s):
    return GR(1 - s) / GR(s)


def is_pole(expr):
    return expr == sp.zoo or expr.has(sp.zoo)


def Om(d):
    return 2 * math.exp((d + 1) / 2 * math.log(PI) - gammaln((d + 1) / 2))


def I(l0, l1, l2):
    return (Om(5) / Om(l0)) ** 2 * Om(l1) * Om(l2)


def main():
    print("=" * 74)
    print("THE REGULARITY FORCING, CONDITIONAL ON ONE PRINCIPLE (Theorem 1p)")
    print("=" * 74)

    vals = {l: I(*l) for l in LABS}
    sup = max(vals, key=vals.get)
    inf = min(vals, key=vals.get)

    # ---- R1: the gamma-factor dichotomy on the tower (exact)
    print()
    print("R1 Tate's archimedean gamma-factor Gamma_R(1-s)/Gamma_R(s):")
    ok1 = all(is_pole(gamma_factor(s)) == (s % 2 == 1)
              for s in list(range(2, 31)) + [217, 218, 219])
    ok1 &= sp.simplify(gamma_factor(2) + 2 * sp.pi ** 2) == 0
    ok1 &= sp.simplify(gamma_factor(8) - 8 * sp.pi ** 8 / 315) == 0
    print(f"   poles exactly at odd s, finite nonzero at even s (gated on")
    print(f"   s = 2..30 and 217..219; closed forms gamma(2) = -2 pi^2,")
    print(f"   gamma(8) = 8 pi^8/315 gated exactly) -- the local functional")
    print(f"   equation is singular at the inf twists (7, 21, 219), regular")
    print(f"   at the sup twists (8, 20, 218)   {'PASS' if ok1 else 'FAIL'}")

    # ---- R2: the mirror-weight formulation (exact; d = 0 included)
    print()
    print("R2 the mirror weight 2/Gamma_R(-d) (layer d's functional-")
    print("   equation image is layer -(d+1)):")
    ok2 = all((sp.simplify(2 / GR(-d)) == 0) == (d % 2 == 0)
              for d in list(range(0, 31)) + [217, 218])
    w7 = sp.simplify(2 / GR(-7))
    ok2 &= w7 == sp.Rational(105, 8) / sp.pi ** 4
    print(f"   zero iff d even (gated d = 0..30, 217, 218; d = 7's live")
    print(f"   mirror weight = 105/(8 pi^4) gated exactly); the s = d+1")
    print(f"   biconditional with R1 -- declared   {'PASS' if ok2 else 'FAIL'}")

    # ---- R3: the per-crossing forcing under the regularity principle
    print()
    print("R3 the conditional forcing: exactly one regular member per pair:")
    regular = tuple(d for pair in PAIRS
                    for d in pair if not is_pole(gamma_factor(d + 1)))
    counts = [sum(1 for d in pair if not is_pole(gamma_factor(d + 1)))
              for pair in PAIRS]
    ok3 = counts == [1, 1, 1] and regular == (7, 19, 217) == sup
    print(f"   regular members per pair: {counts}; the regular labeling =")
    print(f"   {regular} = the variational argmax (recomputed) -- GIVEN the")
    print(f"   regularity principle, the labeling is forced with zero")
    print(f"   residual freedom; the agreement with the sup is the gated")
    print(f"   content (it could have failed at any crossing)   "
          f"{'PASS' if ok3 else 'FAIL'}")

    # ---- R4: the corollary chain (all five selectors coincide)
    print()
    print("R4 the corollary chain on the eight labelings:")
    odd_sel = tuple(x if x % 2 == 1 else y for x, y in PAIRS)
    S = {l: 24 * PI ** 2 / ((2 / PI) * math.exp(0.02108) * vals[l])
         for l in LABS}
    smin = min(S, key=S.get)
    tz_avoiders = [l for l in LABS
                   if all(sp.zeta(1 - (d + 1)) != 0 for d in l)]
    ok4 = regular == odd_sel == sup == smin
    ok4 &= tz_avoiders == [sup]
    print(f"   regular = odd-member = argmax I = argmin S = the unique")
    print(f"   trivial-zero avoider = {sup}: under the regularity")
    print(f"   principle, the variational definition and all four 1n/1o")
    print(f"   equivalents follow as corollaries   {'PASS' if ok4 else 'FAIL'}")

    # ---- R5: the precision bonus (the s = 1 exceptional point)
    print()
    print("R5 the local form is uniform where the global form breaks:")
    ok5 = is_pole(gamma_factor(1)) and sp.simplify(2 / GR(0)) == 0
    ok5 &= sp.zeta(0) == sp.Rational(-1, 2)      # NOT a trivial zero
    ok5 &= all((sp.zeta(1 - (d + 1)) == 0) == (d % 2 == 0)
               for d in range(1, 31))            # global form OK for d >= 1
    print(f"   at s = 1 (layer d = 0): gamma pole and mirror weight 0, yet")
    print(f"   zeta(0) = -1/2 != 0 (zeta's POLE sits opposite, not a")
    print(f"   trivial zero) -- 1o's global form has an exceptional point;")
    print(f"   the local form is uniform on all d >= 0; on the label range")
    print(f"   d >= 1 the two coincide (gated)   {'PASS' if ok5 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; grading in docstring)")
    print("=" * 74)
    print("  The inf labels' twist points are the poles of Tate's")
    print("  archimedean gamma-factor: the tower's own local functional")
    print("  equation is singular there, and the mirror layer carries")
    print("  zero weight.  ONE named principle -- integer labels at")
    print("  regular points of the local functional equation, the same")
    print("  non-degeneracy type as T2's gcd condition and Theorem 7's")
    print("  order-one requirement -- forces the labeling to (7, 19, 217)")
    print("  outright, with the variational definition and all four 1n/1o")
    print("  equivalents as corollaries.  The principle is a NEW given,")
    print("  not derived from the axioms: the open question narrows to")
    print("  deriving it.  1k's second given now has its sharpest form.")
    print("  No number changes; no closure.")


if __name__ == "__main__":
    main()
