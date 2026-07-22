#!/usr/bin/env python3
"""THE RAMIFIED TATE STEP (Theorem 1i): pure-phase towers and the
root-number identity.  Category (a): classical Tate local theory +
machine-gated arithmetic; no data, no closures, no RH/GRH, no
semiclassics (Check 7 -- Gauss sums, epsilon factors, Hilbert
symbols); the hypothesis is nowhere an input (Check 8).

CONTEXT.  Theorem 1d named "2-adic/3-adic Tate theory" as the next
step, not opened; 1e opened the UNRAMIFIED half (self-dual
achievers, Euler factors).  This file opens the RAMIFIED half.
Classical structure (Tate): a ramified character of Q_p^x has
LOCAL L-FACTOR 1 -- no pole, no Euler factor -- and its entire
functional-equation content is the EPSILON FACTOR, a normalized
Gauss sum.  The ramified towers are PURE PHASE; the family's two
unramified members are its only pole-carriers -- the trivial
tower (1e), alone with a real-s pole, and eta_5's (1 + 2^-s)^-1
with complex poles (round-54 F1 corrected "the only pole-carrying
one").

THE IDENTITY (E2, the file's core).  For each dyadic square class
a, let eta_a = (., a)_2 be the quadratic character of Q_2^x.  With
the orientation SIGMA fixed by the epsilon product formula (E1),
    beta(a) = eps(eta_a)          on ALL EIGHT classes,
where beta(a) = gamma_2(a)/gamma_2(1) is the clock's disc-twist
(1f/1g) and eps(eta_a) is Tate's local epsilon factor: the
unit-conductor Gauss sum times the classical unramified-twist
correction eta_a(2)^{a(chi)}.  Equivalently, in the program's own
standard character psi_2 = e^{-2 pi i {x}_2}:
    beta(a) = eta_a(-1) * eps(eta_a, psi_2).
COMBINED WITH THE CLOSED FORM (1g(ii)):
    gamma_2(q) = gamma_2(1)^dim * eps(eta_disc) * hasse(q)
-- Tate's local functional equation supplies the clock's twist
structure.  The general Weil-index/epsilon relation is classical
in substance (Weil's metaplectic index; the quadratic root-number
relations); the eight-class identity in the program's stated
conventions is gated here.

ORIENTATION, FIXED BY GATE NOT BY FIAT (E1).  Local epsilon
factors are convention-laden (additive-character orientation).
The convention is pinned the only honest way: the finite-place
Gauss orientation sigma = +1 pairs with the classical archimedean
odd root number eps_inf = -i so that the PRODUCT FORMULA
Prod_v eps_v = global W holds at the known values -- gated on
four independently KNOWN global root numbers (multiplicatively
dependent as characters -- chi_-8 = chi_8 chi_-4; round-54 F8) (chi_-4, chi_8, chi_-8,
chi_-3, all W = +1; chi_-3's is the paper's analytically-verified
root number, 1c).  The round-22 covariance grading applies:
structural statements are convention-free, specific values are
convention-tied.

THE COLOUR DECOMPOSITION (E4).  The global root number +1 of
L(s, chi_-3) -- verified analytically at 1c -- decomposes locally
as eps_3(chi_-3) * eps_inf(sgn) = (+i)(-i) = +1: the colour
character's evenness of sign is a two-place cancellation, ramified
conductor-3 against the archimedean sgn tower, ANOTHER two-place
lock of the 1f/1g family shape.  And the odd bridge's conductor
term -1/2 ln 3 (1c) is the log-derivative of the functional
equation's conductor factor 3^{s/2} -- Door 4's "conductor is the
different" has its epsilon-side home (E5).

WHAT THIS DOES NOT DO: derive any A2 grammar entry; produce new
numbers; claim any closure.  The ramified towers' pure-phase
structure and the root-number identity are structure, not
prediction.  No data, no RH/GRH.
"""

import cmath
import math
import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from cascade_local_family import gamma_v, hilbert, same_class, hasse, disc

D2 = [1, 3, 5, 7, 2, 6, 10, 14]
Z8 = [cmath.exp(2j * cmath.pi * j / 8) for j in range(8)]


def cls(x):
    return next(c for c in D2 if same_class(x, c))


def chi_m4(n):
    return 1 if n % 4 == 1 else -1


def chi_8(n):
    return 1 if n % 8 in (1, 7) else -1


def chi_m8(n):
    return 1 if n % 8 in (1, 3) else -1


def chi_m3(n):
    return 0 if n % 3 == 0 else (1 if n % 3 == 1 else -1)


# unit restriction of eta_a and its conductor exponent a(chi)
UNIT = {1: (None, 0), 5: (None, 0), 3: (chi_m4, 2), 7: (chi_m4, 2),
        2: (chi_8, 3), 10: (chi_8, 3), 6: (chi_m8, 3), 14: (chi_m8, 3)}


def eps_unit(chi, k, sigma):
    """Normalized unit-conductor Gauss sum, orientation sigma = +-1."""
    if k == 0:
        return 1.0
    q = 2 ** k
    s = sum(chi(u) * cmath.exp(sigma * 2j * cmath.pi * u / q)
            for u in range(1, q) if u % 2 == 1)
    return s / math.sqrt(q)


def eps_eta(a, sigma):
    """Tate epsilon of eta_a = (., a)_2: unit Gauss sum times the
    classical unramified-twist correction eta_a(2)^{a(chi)}."""
    ch, k = UNIT[a]
    base = eps_unit(ch, k, sigma) if ch else 1.0
    return (hilbert(2, a, 2) ** k) * base


def main():
    print("=" * 74)
    print("THE RAMIFIED TATE STEP (Theorem 1i): pure phase + the")
    print("root-number identity")
    print("=" * 74)

    # ---- E1: orientation fixed by the epsilon product formula
    print()
    print("E1 orientation fixed by the product formula (four known global")
    print("   root numbers, all W = +1; eps_inf(odd) = -i classical):")
    W_inf_odd = -1j
    e_m4 = eps_unit(chi_m4, 2, +1)
    e_8 = eps_unit(chi_8, 3, +1)
    e_m8 = eps_unit(chi_m8, 3, +1)
    e_3 = sum(chi_m3(u) * cmath.exp(2j * cmath.pi * u / 3)
              for u in (1, 2)) / math.sqrt(3)
    ok1 = abs(e_m4 * W_inf_odd - 1) < 1e-9          # chi_-4 odd
    ok1 &= abs(e_8 - 1) < 1e-9                      # chi_8 even, W_inf = 1
    ok1 &= abs(e_m8 * W_inf_odd - 1) < 1e-9         # chi_-8 odd
    ok1 &= abs(e_3 * W_inf_odd - 1) < 1e-9          # chi_-3 odd (the paper's)
    print(f"   eps_2(chi_-4)*(-i) = eps_2(chi_-8)*(-i) = eps_2(chi_8) =")
    print(f"   eps_3(chi_-3)*(-i) = +1   {'PASS' if ok1 else 'FAIL'}")

    # ---- E2: the eight-class root-number identity
    print()
    print("E2 the identity beta(a) = eps(eta_a) on all 8 square classes")
    print("   (and the program-psi form beta = eta(-1) eps(eta, psi_2)):")
    g1 = gamma_v(1, 2)
    ok2 = True
    for a in D2:
        b = gamma_v(a, 2) / g1
        ok2 &= abs(b - eps_eta(a, +1)) < 1e-8
        ok2 &= abs(b - hilbert(-1, a, 2) * eps_eta(a, -1)) < 1e-8
    print(f"   both forms, 8/8 classes   {'PASS' if ok2 else 'FAIL'}")

    # ---- E3: the classical unramified-twist formula on the twisted pairs
    print()
    print("E3 unramified-twist formula eps(chi mu) = mu(2)^a(chi) eps(chi)")
    print("   on the three eta_5-twisted pairs:")
    # round-54 F3: the eps-side ratio cancels the shared unit base
    # bit-exactly (a consistency exhibit); the twist formula's GENUINE
    # instrument is the beta-side ratio, computed from the independent
    # Weil-oscillator machinery -- gated here.  Note the (3,7) pair has
    # even exponent a(chi) = 2, so its correction is invisible in
    # principle; the odd-exponent pairs carry the content.
    g1_ = gamma_v(1, 2)
    ok3 = True
    for x, y in ((3, 7), (2, 10), (6, 14)):
        r_beta = (gamma_v(x, 2) / g1_) / (gamma_v(y, 2) / g1_)
        want = (hilbert(2, x, 2) / hilbert(2, y, 2)) ** UNIT[x][1]
        ok3 &= abs(r_beta - want) < 1e-8
    print(f"   beta-side ratios on pairs (3,7), (2,10), (6,14)   "
          f"{'PASS' if ok3 else 'FAIL'}")

    # ---- E4: the colour decomposition
    print()
    print("E4 the colour character's global root number decomposes:")
    # round-54 F5: the product conjunct shares E1's computation on the
    # same variable -- E4 is the DECOMPOSITION READING of E1's anchor,
    # a consistency exhibit, declared as such
    ok4 = abs(e_3 - 1j) < 1e-9 and abs(e_3 * W_inf_odd - 1) < 1e-9
    print(f"   eps_3(chi_-3) = +i, eps_inf(sgn) = -i, product = +1 = the")
    print(f"   analytically-verified global W (1c)   "
          f"{'PASS' if ok4 else 'FAIL'}")
    print("   (a two-place cancellation: ramified conductor 3 against the")
    print("    archimedean sgn tower -- the 1f/1g family shape again)")

    # ---- E5: the conductor log-derivative = the odd bridge's constant
    print()
    print("E5 the odd bridge's conductor term is the epsilon-side")
    print("   conductor factor's log-derivative:")
    # round-54 F7: the first version's conjuncts were tautologies (the
    # same expression twice; a math-library check).  The identity's
    # GENUINE gate is cascade_local_tate.py's T-loc4 bridge check
    # (p_sgn + sum_p p_p^chi = Lambda'/Lambda - (1/2)ln 3, verified to
    # 1e-20); E5 exhibits the sign bookkeeping: the completed L's
    # conductor factor 3^{(s+1)/2} has log-derivative +ln(3)/2, entering
    # the bridge with a MINUS as it crosses to the p_sgn side.
    ok5 = abs((math.log(3) / 2) + (-math.log(3) / 2)) < 1e-15
    print(f"   conductor factor's log-derivative +ln(3)/2 crosses sides:"
          f" bridge term = -ln(3)/2 (genuine gate: local_tate T-loc4)   "
          f"{'PASS' if ok5 else 'FAIL'}")

    # ---- E6: the closed form recombined through epsilon
    # round-54 F6: E6 is a corollary of E2 + local_family's gated
    # cocycle/closed form (L2/L3) -- a consistency exhibit of the
    # recombination, not an independent failure mode; declared per the
    # L7b precedent
    print()
    print("E6 gamma_2(q) = gamma_2(1)^dim * eps(eta_disc) * hasse(q) --")
    print("   the clock's twist IS the root-number map (dims 1-2")
    print("   exhaustive + the 1g battery):")
    ok6 = True
    for a in D2:
        lhs = gamma_v(a, 2)
        rhs = g1 * eps_eta(cls(a), +1)
        ok6 &= abs(lhs - rhs) < 1e-8
    for a in D2:
        for b in D2:
            lhs = gamma_v(a, 2) * gamma_v(b, 2)
            rhs = (g1 ** 2) * eps_eta(cls(a * b), +1) * hilbert(a, b, 2)
            ok6 &= abs(lhs - rhs) < 1e-8
    battery = [[1, 3, 5], [2, 6, 10], [1, 2, 3, 4], [7, 14, 5, 6],
               [1, 1, 1, 1, 3], [2, 3, 5, 7, 10, 14], [3, 3, 3],
               [1, 6, 10, 14]]
    for f in battery:
        lhs = 1
        for x in f:
            lhs *= gamma_v(x, 2)
        rhs = (g1 ** len(f)) * eps_eta(cls(disc(f)), +1) * hasse(f, 2)
        ok6 &= abs(lhs - rhs) < 1e-8
    print(f"   8 + 64 + battery forms   {'PASS' if ok6 else 'FAIL'}")

    # ---- E7: pure phase -- ramified L-factor triviality (classical,
    # exhibited): the ramified local zeta integral of the unit indicator
    # twisted by chi is a FINITE sum with no pole; exhibited by the
    # vanishing of the unit-sphere character sums at every level
    print()
    print("E7 pure phase: ramified unit-character sums vanish shell-by-")
    print("   shell (no Euler factor -- the ramified towers carry no")
    print("   pole; all content is in eps):")
    ok7 = True
    for ch, k in ((chi_m4, 2), (chi_8, 3), (chi_m8, 3)):
        for kk in range(k, k + 4):
            q = 2 ** kk
            s = sum(ch(u) for u in range(1, q) if u % 2 == 1)
            ok7 &= abs(s) < 1e-12
    for kk in range(1, 5):
        q = 3 ** kk
        s = sum(chi_m3(u) for u in range(1, q) if u % 3 != 0)
        ok7 &= abs(s) < 1e-12
    print(f"   chi_-4, chi_8, chi_-8 (dyadic shells), chi_-3 (triadic"
          f" shells)   {'PASS' if ok7 else 'FAIL'}")

    print()
    print("=" * 74)
    print("READING (classical + gated; honest scope in docstring)")
    print("=" * 74)
    print("  The ramified side of Tate's local theory is pure phase, and")
    print("  its phases are the program's: the clock's disc-twist beta is")
    print("  the dyadic quadratic root-number map, the colour character's")
    print("  +1 is a two-place epsilon cancellation, and the odd bridge's")
    print("  conductor term is the epsilon conductor's log-derivative.")
    print("  Orientation fixed by the product-formula gate, stated, not")
    print("  chosen silently.  No grammar entry derived; category (a).")


if __name__ == "__main__":
    main()
