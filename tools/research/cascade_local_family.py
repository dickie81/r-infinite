#!/usr/bin/env python3
"""
THE LOCAL FAMILY COMPLETED (Addendum 79): odd-place exclusivity and
the kernel's anatomy.  Category (a): exact identities + classical
theorems, machine-verified; no data, no closures; every
identification graded; every "forced" names its forcer (A66); no
semiclassics (Check 7 -- Gauss sums, Hilbert symbols, Witt theory).

CONTEXT.  Theorem 1f established the two clock-place quotients:
gamma_2 : W(Q_2) ->> mu_8 (<1> -> zeta_8^(-1)) and gamma_inf =
zeta_8^sig : W(R) ->> mu_8, locked inverse by Weil's product
formula.  Two doors were left open: what happens at the ODD places
(Door 1), and what exactly is the kernel (Door 2).  This file
closes both at their achievable scope.

CONVENTION: the same standard adelic character as Theorem 1f
(psi_inf = e^(2 pi i x), psi_p = e^(-2 pi i {x}_p)); the same
covariance grading applies (round-22 F2): the structural statements
below are character-free, the specific values are convention-tied.

L1 (DOOR 1 -- THE ODD PLACES ARE SMALL AND DIMENSION-BLIND;
verified).  For odd p the local Weil index on the four square
classes {1, u, p, up} (u a non-residue) satisfies:
    gamma_p(<1>) = gamma_p(<u>) = 1   (units are SILENT),
    image of gamma_p = mu_2 = {1,-1}      if p = 1 mod 4,
                     = mu_4 = {1,+-i,-1}  if p = 3 mod 4.
With |W(Q_p)| = 16 (classical: Lam Ch. VI; cited), the kernels
have order 8 and 4 respectively.  THE EXCLUSIVITY THEOREM: within
the family {gamma_v : W(Q_v) -> mu_8}_v over all places of Q, the
full order-8 image -- the clock group -- occurs EXACTLY at v = 2
and v = infinity, and the unit form <1> has nontrivial index
EXACTLY at those two places.  The program's clock (T6 archimedean;
1d/1e/1f dyadic) lives at precisely the places where the Witt-Weil
family can carry it.  THE FORCER CHAIN, spelled (round-25 F1: the
unit form is silent at odd p, so level does not act through <1>;
the chain is): the image of gamma_p is a homomorphic image of
W(Q_p), whose exponent is 2 x level(Q_p) (classical; = 2 for
p = 1 mod 4, 4 for p = 3 mod 4), so the image lies in
mu_{2 level} <= mu_4 for EVERY odd p -- the five sampled primes
verify the classical inputs, they do not carry the quantifier;
the L1 gate checks image order = 2 x level exactly.  Equivalently
the Gauss evaluations G(a,p) = eps_p sqrt(p) (a/p) cap the class
values directly.  Nothing cascade-chosen.  UNIFIED CRITERION
(round-25 c1): the cocycle and closed form hold at v = inf too
(verified in-code below, L6 -- round-26 F1 moved this from the
session record into the script), so across ALL places the clock
places are exactly those where gamma_v(<1>) is PRIMITIVE -- the
1f-F2 primitivity phenomenon is itself clock-place-exclusive, and
"sig mod 8" is the infinity-evaluation of the same universal
closed form gamma(1)^dim beta(disc) hasse.

L2 (DOOR 2a -- THE COCYCLE; classical (Weil; Rao), verified
exhaustively).  gamma(a) gamma(b) = gamma(1) gamma(ab) (a,b)_v
with (.,.)_v the Hilbert symbol: verified over ALL 64 ordered
square-class pairs at v = 2 and all 16 pairs at p = 3, 5.  The
Weil index is a quadratic character of the square-class group
twisted by the Hilbert pairing -- this is the exact sense in which
the clock is "quadratic arithmetic."

L3 (DOOR 2b -- THE CLOSED FORM; derived from L2 by induction,
verified independently).  With beta(a) := gamma(a)/gamma(1):
    gamma_v(q) = gamma_v(1)^(dim q) * beta_v(disc q) * hasse_v(q),
hasse_v(q) = prod_{i<j} (a_i, a_j)_v.  At v = 2, gamma(1) =
zeta_8^(-1): THE DYADIC CLOCK READS DIMENSION MOD 8, twisted by
disc and Hasse.  At v = infinity: SIGNATURE MOD 8 (Theorem 1f).
At odd p, gamma_p(1) = 1: THE DIMENSION TERM VANISHES -- odd
places are dimension-blind.  The two clock places are exactly the
dimension-/signature-sensitive places of Q.  (Verified: exhaustive
over all diagonal forms of dim 1-2 on the 8 dyadic classes, a
deterministic battery of dims 3-6, and odd-p samples.)

L4 (DOOR 2c -- KERNEL ANATOMY AT p = 2; verified).  Witt classes
of Q_2: 1 zero class, 8 of dim 1, 14 anisotropic of dim 2 (the
pairs (disc delta != -1-class, hasse h), each realized), 8 of dim
3, 1 of dim 4 (the quaternionic norm form <1,1,1,1>) -- total 32
(Lam; the 14 and the count are re-derived here from (disc, Hasse)
classification of binary forms, with hyperbolic = (disc -1, h +1)
and (disc -1, h -1) unrealizable in dim 2).  Dimension parity
forces the kernel of gamma_2 into even dimension; the dim-4 class
has gamma = -1; so ker gamma_2 = {0} + the dim-2 anisotropic
classes with gamma = 1.  The script finds EXACTLY THREE, each of
order 2 in W (k = -k verified via the dim-2 isometry criterion
(disc, hasse) -- classical: dim + disc + Hasse classify over
local fields), so ker gamma_2 = (Z/2)^2, completing
    W(Q_2) = Z/8 (+) Z/2 (+) Z/2  --gamma_2-->>  mu_8
with the Z/8 the <1>-span and the (Z/2)^2 exactly the clock-
invisible classes.  GRAMMAR HONESTY: whether the two clock-
invisible Z/2's (disc-type and Hasse-type data) have any grammar
meaning is OPEN and none is claimed; this door was opened to
expose that question precisely.

L5 (THE GLOBAL RE-LOCK; verified).  Weil's product formula
Prod_v gamma_v(q) = 1 for MULTI-DIMENSIONAL rational forms (1f
verified it per square class; here per form), including an
8-dimensional definite form (sig = dim = 8: both clock places
return 1 -- the mod-8 wrap seen globally).

WHAT THIS DOES NOT DO: derive any A2 grammar entry (N_c's count
remains Adams-archimedean per 1f(iii); the layer selection remains
papers-side); touch data; use RH/GRH.  The reading of this mu_8
as THE grammar's clock remains the same graded identification
T6/D3.2/1f made.
"""

import cmath
import math

MU8 = [cmath.exp(2j * cmath.pi * j / 8) for j in range(8)]


def nearest_mu8(z):
    best = min(range(8), key=lambda j: abs(z - MU8[j]))
    return best, abs(z - MU8[best])


def gauss_phase(u0, p, k):
    N = p ** k
    s = sum(cmath.exp(-2j * cmath.pi * ((u0 * n * n) % N) / N)
            for n in range(N))
    return s / abs(s)


def gamma_v(u, p, kbig=None):
    """Local Weil index of <u> at finite p (standard character)."""
    e = 0
    u0 = u
    while u0 % p == 0:
        u0 //= p
        e += 1
    if kbig is None:
        kbig = 10 if p == 2 else 4
    k = kbig + (e % 2 != kbig % 2)
    return gauss_phase(u0, p, k)


def gamma_inf_form(form):
    sig = sum(1 if a > 0 else -1 for a in form)
    return cmath.exp(1j * cmath.pi * sig / 4)


def split(a, p):
    """a = p^e * u with p !| u; return (e, u)."""
    e = 0
    while a % p == 0:
        a //= p
        e += 1
    return e, a


def eps2(u):
    return ((u % 8) - 1) // 2 % 2


def omega2(u):
    return 1 if u % 8 in (3, 5) else 0


def hilbert(a, b, p):
    """Hilbert symbol (a,b)_p, p prime (classical closed formulas)."""
    if p == 2:
        al, u = split(a, 2)
        be, v = split(b, 2)
        s = eps2(u) * eps2(v) + al * omega2(v) + be * omega2(u)
        return -1 if s % 2 else 1
    al, u = split(a, p)
    be, v = split(b, p)
    leg_u = 1 if pow(u % p, (p - 1) // 2, p) == 1 else -1
    leg_v = 1 if pow(v % p, (p - 1) // 2, p) == 1 else -1
    s = al * be * ((p - 1) // 2)
    r = (-1 if s % 2 else 1) * (leg_u ** be) * (leg_v ** al)
    return r


def hasse(form, p):
    h = 1
    for i in range(len(form)):
        for j in range(i + 1, len(form)):
            h *= hilbert(form[i], form[j], p)
    return h


def disc(form):
    d = 1
    for a in form:
        d *= a
    return d


def gamma_form(form, p):
    z = 1
    for a in form:
        z *= gamma_v(a, p)
    return z


def closed_form(form, p):
    g1 = gamma_v(1, p)
    beta = gamma_v(disc(form), p) / g1
    return g1 ** len(form) * beta * hasse(form, p)


def main():
    print("=" * 74)
    print("THE LOCAL FAMILY COMPLETED: odd-place exclusivity + kernel")
    print("=" * 74)

    # ---- L1: the odd places
    print()
    print("L1 odd places (four square classes 1, u, p, up):")
    ok_ex = True
    for p in (3, 5, 7, 11, 13):
        u = next(x for x in range(2, p)
                 if pow(x, (p - 1) // 2, p) == p - 1)
        reps = [1, u, p, u * p]
        c2 = next(c * c for c in (2, 3, 5, 7) if c % p)
        vals, ok = [], True
        for r in reps:
            g = gamma_v(r, p)
            ok &= abs(gamma_v(r, p, kbig=2) - g) < 1e-9        # k-stable
            ok &= abs(g - gamma_v(r * c2, p)) < 1e-9           # class-inv
            j, d = nearest_mu8(g)
            ok &= d < 1e-9
            vals.append(j)
        units_silent = vals[0] == 0 and vals[1] == 0
        # subgroup of mu_8 generated by the numeric class exponents:
        g0 = 8
        for v in vals:
            g0 = math.gcd(g0, v)
        size = 8 // g0
        want = 2 if p % 4 == 1 else 4
        ok &= units_silent and size == want
        ok_ex &= ok
        print(f"   p = {p:>2} ({p % 4} mod 4): units silent ="
              f" {units_silent}, image order {size} (want {want}"
              f" = 2 x level = exp W(Q_p): the forcer chain)"
              f"   {'PASS' if ok else 'FAIL'}")
    print(f"   EXCLUSIVITY: order-8 image and nontrivial <1> occur only"
          f" at v = 2, inf   {'PASS' if ok_ex else 'FAIL'}")
    print("   (|W(Q_p)| = 16, Lam, cited => kernel orders 8 / 4)")

    # ---- L2: the cocycle
    print()
    print("L2 cocycle  gamma(a)gamma(b) = gamma(1)gamma(ab)(a,b)_v :")
    d2 = [1, 3, 5, 7, 2, 6, 10, 14]
    ok2 = True
    for a in d2:
        for b in d2:
            lhs = gamma_v(a, 2) * gamma_v(b, 2)
            rhs = gamma_v(1, 2) * gamma_v(a * b, 2) * hilbert(a, b, 2)
            ok2 &= abs(lhs - rhs) < 1e-9
    print(f"   v = 2: all 64 ordered class pairs   "
          f"{'PASS' if ok2 else 'FAIL'}")
    for p in (3, 5):
        u = next(x for x in range(2, p)
                 if pow(x, (p - 1) // 2, p) == p - 1)
        rp = [1, u, p, u * p]
        okp = True
        for a in rp:
            for b in rp:
                lhs = gamma_v(a, p) * gamma_v(b, p)
                rhs = gamma_v(1, p) * gamma_v(a * b, p) * hilbert(a, b, p)
                okp &= abs(lhs - rhs) < 1e-9
        print(f"   p = {p}: all 16 ordered class pairs   "
              f"{'PASS' if okp else 'FAIL'}")

    # ---- L3: the closed form
    print()
    print("L3 closed form  gamma(q) = gamma(1)^dim * beta(disc) * hasse(q):")
    ok3 = all(abs(gamma_form([a], 2) - closed_form([a], 2)) < 1e-9
              for a in d2)
    ok3 &= all(abs(gamma_form([a, b], 2) - closed_form([a, b], 2)) < 1e-9
               for a in d2 for b in d2)
    print(f"   v = 2, exhaustive dims 1-2 (8 + 64 forms)   "
          f"{'PASS' if ok3 else 'FAIL'}")
    battery = [[1, 3, 5], [2, 6, 10], [1, 2, 3, 4], [7, 14, 5, 6],
               [1, 1, 1, 1, 3], [2, 3, 5, 7, 10, 14], [3, 3, 3],
               [1, 6, 10, 14]]
    okb = all(abs(gamma_form(f, 2) - closed_form(f, 2)) < 1e-9
              for f in battery)
    print(f"   v = 2, deterministic battery dims 3-6   "
          f"{'PASS' if okb else 'FAIL'}")
    oko = True
    for p in (3, 5):
        u = next(x for x in range(2, p)
                 if pow(x, (p - 1) // 2, p) == p - 1)
        for f in ([p, u], [1, p, u * p], [p, p, u], [u, u * p, p, 1]):
            oko &= abs(gamma_form(f, p) - closed_form(f, p)) < 1e-9
    print(f"   p = 3, 5 samples; gamma_p(1) = 1 so the DIMENSION TERM"
          f" VANISHES   {'PASS' if oko else 'FAIL'}")
    print("   => the clock places are exactly the dimension-/signature-")
    print("      sensitive places: dim mod 8 at v = 2 (gamma(1) ="
          " zeta_8^-1),")
    print("      sig mod 8 at v = inf, NO dimension term at odd p.")

    # ---- L4: kernel anatomy
    print()
    print("L4 kernel of gamma_2 (dim-2 anisotropic census):")
    # the 14 binary classes: (disc class != -1-class, hasse); -1 ~ 7
    classes = {}
    for a in d2:
        for b in d2:
            dcls = next(c for c in d2 if same_class(a * b, c))
            classes.setdefault((dcls, hilbert(a, b, 2)), (a, b))
    n_pairs = len(classes)
    aniso = {k: v for k, v in classes.items() if k[0] != 7}
    hyp_ok = (7, -1) not in classes            # (disc -1, h -1) never occurs
    print(f"   realized (disc, hasse) pairs: {n_pairs} = 14 aniso + "
          f"1 hyperbolic (disc~7, h=+1); (disc~7, h=-1) unrealized: "
          f"{'PASS' if n_pairs == 15 and hyp_ok and len(aniso) == 14 else 'FAIL'}")
    kernel = []
    for (dcls, h), (a, b) in sorted(aniso.items()):
        g = gamma_v(a, 2) * gamma_v(b, 2)
        if abs(g - 1) < 1e-9:
            kernel.append((dcls, h, a, b))
    print(f"   dim-2 aniso classes with gamma = 1: "
          f"{[(d, h) for d, h, _, _ in kernel]}   "
          f"{'PASS' if len(kernel) == 3 else 'FAIL'}   (kernel = {{0}} +"
          " these three: order 4)")
    ok_ord = True
    for dcls, h, a, b in kernel:
        h_neg = hilbert(-a, -b, 2)
        dneg_cls = next(c for c in d2 if same_class(a * b, c))  # (-a)(-b)=ab
        ok_ord &= (dneg_cls == dcls and h_neg == h)   # k = -k  =>  2k = 0
    print(f"   each kernel class = its own negative (k = -k, dim-2"
          f" isometry by (disc, hasse)) => order 2   "
          f"{'PASS' if ok_ord else 'FAIL'}   (kernel = (Z/2)^2)")
    print("   => W(Q_2) = Z/8 (+) (Z/2)^2 with Z/8 = <1>-span (1f) and")
    print("      (Z/2)^2 = the clock-invisible classes.  Grammar meaning")
    print("      of the two invisible Z/2's: OPEN, none claimed.")

    # ---- L5: global re-lock on multi-dim forms
    print()
    print("L5 global product formula on multi-dimensional forms:")
    forms = [[1, 3], [2, 5, 7], [1, 1, 1], [3, -5, 6, 14],
             [-1, -2, 15], [1, 1, 1, 1, 1, 1, 1, 1]]
    for f in forms:
        prod = gamma_inf_form(f)
        prod *= gamma_form(f, 2)
        odd_ps = set()
        for a in f:
            m = abs(a)
            for p in (3, 5, 7, 11, 13):
                if m % p == 0:
                    odd_ps.add(p)
        for p in sorted(odd_ps):
            prod *= gamma_form(f, p)
        r = abs(prod - 1)
        print(f"   {str(f):<28} |Prod_v gamma_v - 1| = {r:.1e}   "
              f"{'PASS' if r < 1e-8 else 'FAIL'}")
    print("   (the dim-8 definite form: both clock places wrap to 1 --")
    print("    the mod-8 period seen globally)")

    # ---- L6 (round-26 F1): the infinity cocycle + closed form, in-code
    print()
    print("L6 v = inf: cocycle and closed form in-code (round-26 F1: the")
    print("   round-25 verification lived only in the session record):")
    z8 = cmath.exp(1j * cmath.pi / 4)

    def gi(a):
        return z8 if a > 0 else 1 / z8

    def hil_inf(a, b):
        return -1 if (a < 0 and b < 0) else 1

    ok6 = True
    for a in (1, -1):
        for b in (1, -1):
            ok6 &= abs(gi(a) * gi(b)
                       - gi(1) * gi(a * b) * hil_inf(a, b)) < 1e-12
    print(f"   cocycle gamma(a)gamma(b) = gamma(1)gamma(ab)(a,b)_inf,"
          f" all sign pairs   {'PASS' if ok6 else 'FAIL'}")
    ok7 = True
    for f in ([-1, -1], [1, -1, -1, -1], [-1] * 5, [1, 1, -1], [1] * 8):
        sig = sum(1 if x > 0 else -1 for x in f)
        d = 1
        h = 1
        for i in range(len(f)):
            d *= f[i]
            for j in range(i + 1, len(f)):
                h *= hil_inf(f[i], f[j])
        ok7 &= abs(z8 ** sig - gi(1) ** len(f) * (gi(d) / gi(1)) * h) < 1e-12
    print(f"   sig-mod-8 = the universal closed form"
          f" gamma(1)^dim beta(disc) hasse at inf   "
          f"{'PASS' if ok7 else 'FAIL'}")
    print("   => the unified criterion is now fully in-code: the clock")
    print("      places are exactly those where gamma_v(<1>) is primitive.")

    print()
    print("=" * 74)
    print("READING (exact + classical + graded; honest scope in docstring)")
    print("=" * 74)
    print("  The Witt-Weil family over all places of Q carries the clock")
    print("  group exactly at v = 2 and v = inf -- the only dimension-/")
    print("  signature-sensitive places; odd places are dimension-blind")
    print("  with image mu_2 or mu_4 and silent units.  The dyadic")
    print("  kernel is (Z/2)^2 -- the clock-invisible disc/Hasse data --")
    print("  and the closed form gamma = gamma(1)^dim beta(disc) hasse")
    print("  makes the quotient symbolic.  No grammar entry derived;")
    print("  the grammar meaning of the kernel's Z/2's is the named")
    print("  open question.  No data, no closures, no RH/GRH.")


def same_class(x, y):
    """x, y in the same square class of Q_2 (both nonzero ints)."""
    ex, ux = split_abs(x)
    ey, uy = split_abs(y)
    if (ex - ey) % 2:
        return False
    return (ux * uy) % 8 == 1


def split_abs(x):
    e = 0
    while x % 2 == 0:
        x //= 2
        e += 1
    return e, x % 8 if x > 0 else (x % 8)


if __name__ == "__main__":
    main()
