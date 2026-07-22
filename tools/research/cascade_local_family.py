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
expose that question precisely.  (Net-state: L8/Theorem 1h settles
the data's IDENTITY -- the zeta_4-norm structure; whether the
grammar READS it stays open.)

L5 (THE GLOBAL RE-LOCK; verified).  Weil's product formula
Prod_v gamma_v(q) = 1 for MULTI-DIMENSIONAL rational forms (1f
verified it per square class; here per form), including an
8-dimensional definite form (sig = dim = 8: both clock places
return 1 -- the mod-8 wrap seen globally).

L7 (ROUND 44 -- THE EXHAUSTIVE QUOTIENT + WHERE THE OPEN QUESTION
LIVES; verified; round-45 corrections applied).  NOTATION (round-45
F2: the first writing used <<1>> for the cyclic span, colliding with
the Pfister bracket): the span is written Z<1>; the Pfister bracket
is <<a,b>> := <1,-a> x <1,-b>, so <<-1,-1>> = <1,1,1,1>.  (a)
Directness -- the full forcer chain (round-45 F1: ord(<1>) = 8 was
leaned on without being named; without it the stated premises admit
a Z/16 (+) Z/2 counter-model passing every gate): ord(<1>) = 8
(1f; now ALSO gated: 8<1> = 4H by (dim, disc, Hasse)), so the span
Z<1> has exactly 8 elements; gamma_2(m<1>) = zeta_8^(-m) != 1 for
m = 1..7 puts none of the 7 nonzero span elements in the kernel,
so Z<1> cap ker = 0; with |W(Q_2)| = 32 = 8 x 4 (Lam, cited) this
forces W(Q_2) = Z<1> (+) ker gamma_2 as a DIRECT sum.  (b) The
full 32-class character table: on explicit diagonal representatives
m<1> + e1 k1 + e2 k2 (gamma multiplicative on orthogonal sums),
gamma_2 = zeta_8^(-m) on the <1>-coordinate, kernel-blind in every
mu_8-coset -- the quotient theorem made exhaustive rather than
generated.  SCOPE (round-45 F5): L7b gates the gamma-VALUES; the
32 representatives' pairwise distinctness as Witt classes follows
from the (a) chain plus L4/L7d, not from a separate gate, and L7b
cannot fail while L4 passes -- it is a consistency exhibit of the
table, not an independent failure mode.  (c) I^2-TRANSVERSALITY:
<1,1,1,1> = <<-1,-1>> generates I^2 (I^3 = 0 and |I^2| =
|Br_2(Q_2)| = 2, classical, cited) and gamma_2 of it is -1 != 1,
so gamma_2 does NOT factor through W/I^2 and ker gamma_2 cap I^2
= 0: the clock character is transverse to the fundamental-ideal
filtration.  (d) DISC-FAITHFULNESS: by the SIGNED discriminant
d+- = (-1)^(n(n-1)/2) det (the Witt-invariant disc), the four
kernel classes carry distinct square classes, so d+- : ker
gamma_2 -> I/I^2 = Q_2^x/sq is INJECTIVE, and d+- confirms
k1 + k2 = k3.  Reading: whatever
grammar meaning the invisible (Z/2)^2 carries, it is
DISCRIMINANT-LEVEL data, not deep-filtration data -- the open
question stays open; L7 narrows where its answer can live.

L8 (THEOREM 1h -- THE KERNEL'S IDENTITY; verified).  (a) The
signed-disc image of ker gamma_2, the subgroup H = {1,5,2,10} of
Q_2^x/sq (L7d), is EXACTLY ker(.,-1)_2 = N(Q_2(i)^x) mod squares
-- the norm group of Q_2(i); every element carries an explicit
unit-coordinate norm witness x^2+y^2 (Hensel-liftable), every
non-element fails the Hilbert symbol.  (b) The iff on the full
binary census: a dim-2 anisotropic class is clock-invisible
precisely when its signed disc is a NONTRIVIAL norm class of
Q_2(i), with the Hasse coordinate then forced -- per norm class
exactly one of the two h-values is in the kernel, per non-norm
class neither.  (c) Generators: d+-(ker) = <cls(-3), cls(2)> --
the COLOUR DISCRIMINANT (unramified: -3 = 5 mod 8, and
Q_2(sqrt(-3)) = Q_2(zeta_3) is THE unramified quadratic
extension; (2,-3)_2 = -1 is the same arithmetic fact as 1e(iv)'s
"2 is inert in colour") and the CLOCK PRIME 2 (ramified).  (d)
The infinity mirror is free: ker gamma_inf = 8Z inside W(R) = Z
(torsion-free, Sylvester, cited) -- the invisible TORSION is
dyadic-exclusive.  SLOGAN (structural; exact under the stated
reading, round-47 F2: gamma^2 is a primitive 4th root of unity
and Q_2 adjoined one is the unambiguous Q_2(zeta_4) = Q_2(i) --
no canonical embedding of mu_8(C) into Q_2-bar exists, so the
bare equation is notation for that reading): what the order-8
clock cannot see is what the field generated by the clock's
square norms away.  GRADING:
(a)-(d) are theorems on classical machinery (cocycle, Hilbert
symbols, local norm theory; forcers named, nothing
cascade-chosen); reading -3 as "the colour discriminant" is the
SAME identification 1e(iv) already carries, relocated, not a new
forcing; "quarter-turn field" is clock language for gamma^2 = i.
NO grammar entry derived; no closure; the open question is
TRANSFORMED: the data's identity is settled, whether the grammar
ever reads the two coordinates stays open.  Sharpened falsifier (round-47
F1 rescoped to the licensed form -- the first writing quantified
over all future colour-at-2 derivations, an unproved universal):
any future derivation routing colour through the CLOCK-INVISIBLE
part of W(Q_2) must land in exactly this subgroup, Hasse forced.

L8f (THE FORCED-HASSE FUNCTION -- the Remark; the round-48 edge
case dissolved; round-49 F2: this paragraph was misfiled at first
writing inside the L7 section as item "(f)" -- refiled here): h_beta(d) := zeta_8^2/beta(-d) --
by the closed form, the unique Hasse value a binary class of
signed disc d must carry to be clock-invisible; by the cocycle,
equivalently h_beta(d) = (d,-1)_2/beta(d) (beta(-1) = zeta_8^2).
Gated: the REALITY LOCUS of h_beta is exactly the norm group H
(non-norm discs are forced to +-i, an impossible Hasse value --
EXCLUSION BY IMPOSSIBILITY, not enumeration; the census iff
compresses to one formula); ker gamma_2 is the GRAPH of h_beta
over H, tied in-code to the L4 census; and at the trivial slot
h_beta(1) = +1 = the Hilbert axiom (a,-a)_2 = 1, so the two
forcing mechanisms round 48 verified separately provably
coincide -- there is no edge case.  The zeta_4 motif
again (round-49 F3: the "third appearance" ordinal was an
unverifiable, reading-dependent census -- dropped): invisible <=> forced Hasse real (mu_2), excluded
<=> a quarter-turn (mu_4 \ mu_2).  Pure consequence of the
cocycle + closed form; no new convention.  SCOPE
(round-49 F1, the L7b precedent): L8f1 and L8f2's census conjunct
gate the computed values but cannot fail while L2/L8a/L3/L4 pass
-- consistency exhibits, since h_beta(d)^2 = (d,-1)_2 follows
from the cocycle at (x,x) plus (-1,-1)_2 = -1, making the reality
locus a corollary of gated facts; the independent instruments are
L8f3 (the only gate pinning beta(-1) = zeta_8^2, now also gating
the squared identity) and L8f2's trivial-slot and axiom conjuncts
(this script's only (a,-a) exercise of the Hilbert symbol).

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
        # disc((-a)(-b)) = disc(ab) is an identity, not a gate (round-43
        # cleanup: the first version tested it against itself); the
        # operative own-negative check is the Hasse invariant
        ok_ord &= (h_neg == h)   # k = -k  =>  2k = 0
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

    # ---- L7 (round-44): exhaustive quotient + filtration transversality
    print()
    print("L7 the 32-class character table + the I^2 transversal (round 44):")
    z8i = gamma_v(1, 2)                       # zeta_8^{-1}
    # ord(<1>) = 8 gated in-code (round-45 F1: the first writing leaned
    # on this premise without naming or gating it -- without ord-8 the
    # chain admits a Z/16 (+) Z/2 counter-model passing every gate):
    # 8<1> = 4H in W(Q_2) by the (dim, disc, Hasse) classification of
    # forms over local fields (dim >= 3: classical, cited at L4) --
    # equal dims (8), equal disc classes, equal Hasse invariants.
    f8, h4 = [1] * 8, [1, -1] * 4
    ok8 = (next(c for c in d2 if same_class(disc(f8), c))
           == next(c for c in d2 if same_class(disc(h4), c)))
    ok8 &= hasse(f8, 2) == hasse(h4, 2)
    oka = ok8 and all(abs(z8i ** m - 1) > 0.5 for m in range(1, 8))
    print(f"   L7a ord(<1>) = 8 in-code (8<1> = 4H by (dim, disc,"
          f" Hasse)) + gamma(m<1>) != 1, m = 1..7 => span cap ker = 0;"
          f" with |W| = 32 (Lam): W = Z<1> (+) ker   "
          f"{'PASS' if oka else 'FAIL'}")
    ks = [(a, b) for _, _, a, b in kernel]    # the 3 census kernel reps
    okb7 = True
    for m in range(8):
        for e1 in (0, 1):
            for e2 in (0, 1):
                f = [1] * m + list(ks[0]) * e1 + list(ks[1]) * e2
                g = gamma_form(f, 2) if f else 1
                okb7 &= abs(g - z8i ** m) < 1e-8
    print(f"   L7b character table: all 32 classes on explicit reps,"
          f" gamma = zeta_8^-m, kernel-blind   {'PASS' if okb7 else 'FAIL'}")
    okc = abs(gamma_form([1, 1, 1, 1], 2) + 1) < 1e-8
    print(f"   L7c I^2 transversal: gamma(<<-1,-1>>) = -1 on the"
          f" generator of I^2 (I^3 = 0, |I^2| = 2: cited)   "
          f"{'PASS' if okc else 'FAIL'}")

    def dpm_class(f):
        n = len(f)
        d = (-1) ** (n * (n - 1) // 2) * disc(f)
        return next(c for c in d2 if same_class(d, c))

    kcls = [dpm_class(list(k)) for k in ks]
    okd = len(set(kcls)) == 3 and 1 not in kcls
    okd &= dpm_class(list(ks[0]) + list(ks[1])) == kcls[2]
    print(f"   L7d signed-disc faithful: kernel d+- classes {kcls}"
          f" distinct (0 -> 1), k1+k2 = k3   {'PASS' if okd else 'FAIL'}")
    print("   => the clock-invisible (Z/2)^2 is TRANSVERSE to the")
    print("      fundamental-ideal filtration and faithfully labeled by")
    print("      the signed discriminant: disc-level data, not deep-")
    print("      filtration data.  The grammar question stays OPEN;")
    print("      L7 narrows where its answer can live.")

    # ---- L8 (Theorem 1h): the kernel's identity -- the zeta_4-norm
    # structure
    print()
    print("L8 the kernel's identity (Theorem 1h): the clock-invisible")
    print("   classes are the zeta_4-norm structure:")
    H = [1, 5, 2, 10]
    ok8a = all(next(c for c in d2 if same_class(a * b, c)) in H
               for a in H for b in H)
    ok8a &= sorted(H) == sorted(c for c in d2 if hilbert(c, -1, 2) == 1)
    print(f"   L8a d+-(ker) = {{1,5,2,10}}: a subgroup, and equal to"
          f" ker(.,-1)_2 = N(Q_2(i)) mod sq   {'PASS' if ok8a else 'FAIL'}")

    def norm_witness(c):
        for x in range(1, 64, 2):          # unit coordinate: Hensel-lifts
            for y in range(64):
                if (x * x + y * y - c) % 64 == 0:
                    return (x, y)
        return None

    ok8b = all(norm_witness(c) is not None
               for c in (1, 2, 5, 10, -3, -6, -14))
    ok8b &= all(hilbert(c, -1, 2) == -1 for c in (3, 7, 6, 14))
    print(f"   L8b unit-coordinate norm witnesses x^2+y^2 mod 64 (Hensel)"
          f" for H and -3,-6,-14; Hilbert = -1 on the complement   "
          f"{'PASS' if ok8b else 'FAIL'}")
    ok8c = True
    per = {}
    for (dcl, h), (a, b) in sorted(aniso.items()):
        in_ker = abs(gamma_v(a, 2) * gamma_v(b, 2) - 1) < 1e-9
        dpm = next(c for c in d2 if same_class(-a * b, c))  # dim 2: d+- = -det
        if in_ker:
            ok8c &= hilbert(dpm, -1, 2) == 1 and dpm != 1
        per.setdefault(dpm, []).append(in_ker)
    ok8c &= all((sum(v) == 1) == (hilbert(dpm, -1, 2) == 1 and dpm != 1)
                for dpm, v in per.items())
    print(f"   L8c the iff on all 14 binary classes: in-kernel <=> d+- a"
          f" nontrivial norm class (Hasse forced: one per norm class,"
          f" zero per non-norm)   {'PASS' if ok8c else 'FAIL'}")
    ok8d = sorted({1, next(c for c in d2 if same_class(-3, c)),
                   next(c for c in d2 if same_class(2, c)),
                   next(c for c in d2 if same_class(-6, c))}) == sorted(H)
    chi32 = 1 if 2 % 3 == 1 else (-1 if 2 % 3 == 2 else 0)   # chi_-3(2)
    ok8d &= (-3) % 8 == 5 and hilbert(2, -3, 2) == chi32 == -1
    print(f"   L8d generators <cls(-3), cls(2)>: the colour discriminant"
          f" (unramified, Q_2(zeta_3)) + the clock prime; (2,-3)_2 = -1"
          f" IS 1e(iv)'s inert fact   {'PASS' if ok8d else 'FAIL'}")
    z8c = cmath.exp(1j * cmath.pi / 4)
    ok8e = all((abs(z8c ** s - 1) < 1e-12) == (s % 8 == 0)
               for s in range(-16, 17))
    print(f"   L8e the infinity mirror is free: zeta_8^sig = 1 <=> sig ="
          f" 0 mod 8; W(R) = Z torsion-free (Sylvester, cited) => ker ="
          f" 8Z   {'PASS' if ok8e else 'FAIL'}")
    # ---- L8f (the Remark: the forced-Hasse function -- the round-48
    # edge case dissolved)
    print()
    print("L8f the forced-Hasse function h_beta(d) = zeta_8^2/beta(-d):")

    def beta2(x):
        return gamma_v(next(c for c in d2 if same_class(x, c)), 2) / z8i

    def h_forced(d):
        return (z8i ** -2) / beta2(-d)

    def snap(z):
        return min((1, -1, 1j, -1j), key=lambda w: abs(z - w))

    vals = {d: snap(h_forced(d)) for d in d2}
    okf1 = all(abs(h_forced(d) - vals[d]) < 1e-9 for d in d2)
    okf1 &= all((vals[d] in (1, -1)) == (d in H) for d in d2)
    okf1 &= all(vals[d] in (1j, -1j) for d in d2 if d not in H)
    print(f"   L8f1 reality locus of h_beta == the norm group H; the"
          f" four non-norm discs forced to quarter-turns (+-i):"
          f" exclusion by impossibility   {'PASS' if okf1 else 'FAIL'}")
    okf2 = all(vals[next(c for c in d2 if same_class(-a * b, c))] == h
               for dcl, h, a, b in kernel)
    okf2 &= vals[1] == 1
    okf2 &= all(hilbert(a, -a, 2) == 1 for a in d2)
    print(f"   L8f2 ker gamma_2 == the graph of h_beta over H (tied to"
          f" the L4 census), incl. the trivial slot h_beta(1) = +1 ="
          f" the Hilbert axiom (a,-a)_2 = 1   {'PASS' if okf2 else 'FAIL'}")
    okf3 = all(abs(h_forced(d) - hilbert(d, -1, 2) / beta2(d)) < 1e-9
               for d in d2)
    okf3 &= all(abs(h_forced(d) ** 2 - hilbert(d, -1, 2)) < 1e-9
                for d in d2)   # squared identity: reality locus algebraic
    print(f"   L8f3 cocycle identities h_beta(d) = (d,-1)_2/beta(d) AND"
          f" h_beta(d)^2 = (d,-1)_2 on all 8 classes (beta(-1) ="
          f" zeta_8^2)   {'PASS' if okf3 else 'FAIL'}")
    print("   => one closed-form function forces the Hasse coordinate on")
    print("      all four kernel slots AND excludes the four non-norm")
    print("      discs; the norm criterion IS the reality condition; the")
    print("      round-48 edge case's two mechanisms are one formula.")

    print("   => THEOREM 1h: what the order-8 clock cannot see is what")
    print("      the quarter-turn field Q_2(i) = Q_2(gamma^2) norms away,")
    print("      coordinates = the colour discriminant + the clock prime.")
    print("      Identity settled; whether the grammar READS these")
    print("      coordinates stays OPEN.  No entry derived; category (a).")

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
    return e, x % 8   # (round-43: collapsed a dead two-branch form.
                      # round-45 F4: since round 44, dpm_class feeds
                      # NEGATIVE d values here; Python's floored %
                      # returns the correct non-negative odd-part
                      # residue for negatives (-3 % 8 = 5), so the
                      # collapsed form remains correct -- the
                      # round-43 "only positive inputs" premise is
                      # superseded, recorded, and the correctness now
                      # rests on floored-mod semantics, stated here)


if __name__ == "__main__":
    main()
