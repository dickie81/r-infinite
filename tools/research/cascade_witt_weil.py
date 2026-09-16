#!/usr/bin/env python3
"""
THE WITT STEP (Addendum 75): the clock group is the Weil-index
quotient of the dyadic Witt group.  Category (a): exact identities
and classical theorems, machine-verified; no data, no closures;
every identification graded; every "forced" names its forcer
(A66); no semiclassics (Check 7 -- everything below is Gauss sums,
Witt theory, and Weil's product formula, all already native to the
program via T6/T-loc3).

CONTEXT.  Round 18 (m3) named the open clock-corroborating route:
W(Q_2) has order 32 = Z/8 + Z/2 + Z/2 and <1> has additive order
8 = 2 x level(Q_2).  That was a CORROBORATION (an order-8 cyclic
subgroup exists at the dyadic place).  This file upgrades it to a
STRUCTURE THEOREM: the order-8 clock group mu_8 = <zeta_8> is a
canonical QUOTIENT of W(Q_2), realized by the Weil index -- the
same functional whose archimedean value is T6's clock -- and the
two realizations (real and dyadic) are locked inverse to each
other by Weil's product formula.

CONVENTION (stated because the Weil index is character-dependent).
The standard adelic additive character is used throughout:
psi_inf(x) = e^(2 pi i x);  psi_p(x) = e^(-2 pi i {x}_p).
Local Weil indices gamma_v(u) := phase of the (stabilized,
normalized) local Gauss oscillator of the form u x^2:
    gamma_inf(u) = e^(i pi sgn(u)/4)   (Fresnel; T6's clock),
    gamma_p(u)   = phase of  sum_{n mod p^k} e^(-2 pi i u0 n^2/p^k)
                   for u = p^e u0 (p !| u0), k = 2K - e, K large
                   (k of parity e; the phase stabilizes in k).
Character-covariance, graded honestly: replacing psi by psi_a
permutes the class values (gamma_{psi_a}(u) = gamma_psi(au)); the
psi-INDEPENDENT content is (i) the surjectivity of gamma_2 onto
mu_8 WITH <1> A GENERATOR -- strengthened by round-22 F2: ALL
EIGHT class values are primitive 8th roots (exponents odd,
verified below), so gamma_{psi_a}(<1>) = gamma(a) is primitive
for EVERY character choice -- (ii) the order 8 of <1> in W(Q_2)
(a Witt-group fact, 2 x level, no character anywhere), and (iii)
the product-formula lock Prod_v gamma_v(u) = 1.  What is NOT
psi-independent: the specific value gamma_2(<1>) = zeta_8^(-1)
(stated in the standard convention above -- the same one T-loc3's
compensation fixed) and the KERNEL as a subgroup, which moves
within its scaling orbit under psi -> psi_a.  "Canonical" below
means exactly the psi-independent structure, nothing more
(round-22 F2 grading).

W1 (THE DYADIC WEIL INDEX ON SQUARE CLASSES -- verified).  Q_2^x
has 8 square classes, represented by {1,3,5,7} (units) and
{2,6,10,14} (2 x units).  gamma_2 is verified: well-defined on
square classes (u and 9u, 25u agree; phases stabilize in k),
valued in mu_8 exactly, with gamma_2(<1>) = zeta_8^(-1).

W2 (THE QUOTIENT THEOREM -- verified + classical).  gamma_2 is
additive on diagonal sums by definition (Fubini) and kills the
hyperbolic plane (gamma(1) gamma(-1) = |gamma(1)|^2 = 1), so it
descends to the Witt group:  gamma_2 : W(Q_2) -> mu_8.  Verified:
the image is ALL of mu_8 (already the powers of gamma_2(<1>) =
zeta_8^(-1) generate it -- <1>'s image has exact order 8, matching
its additive order 8 = 2 x level(Q_2) in W(Q_2)).  With |W(Q_2)| =
32 (classical: Lam, Introduction to Quadratic Forms over Fields,
Ch. VI), the kernel has order 4:

    W(Q_2)  --gamma_2-->>  mu_8   (kernel of order 4)

THE CLOCK GROUP IS THE WEIL-INDEX QUOTIENT OF THE DYADIC WITT
GROUP, WITH <1> A GENERATOR OF THE QUOTIENT.  Forcer of the
quotient's existence and size: Weil's index theory + level(Q_2)=4
(both classical); nothing cascade-chosen.

W3 (THE PRODUCT-FORMULA LOCK, PER SQUARE CLASS -- verified).
Weil's product formula Prod_v gamma_v(u x^2) = 1, instantiated
numerically for u in {1,-1,2,-2,3,-3,5,-5,6,15, 9,-9,45,-18,25}
(round-22 F1 extended the original ten-class list, which was
odd-valuation-only at the odd places and so never exercised the
silence claims): the archimedean clock factor times the dyadic
factor times the odd RAMIFIED (odd-valuation) factors multiplies
to 1 every time.  The silence claims are now gated in-code:
gamma_p(u) = 1 for odd p at EVEN valuation (gamma_3(9),
gamma_3(45), gamma_5(25)) and for unramified odd p (gamma_5(3)),
and the odd-p factors are k-stability-gated like the dyadic ones.
In particular u = 1 gives gamma_2(<1>) = gamma_inf(<1>)^(-1) =
zeta_8^(-1): T-loc3's compensation is the u = 1 row of a theorem
that holds per class.

W4 (THE ARCHIMEDEAN MIRROR -- classical + verified at sig = +-1).
gamma_inf(m<1>) = zeta_8^m: the archimedean Weil index is
SIGNATURE MOD 8 -- the order-8 quotient of W(R) = Z (sig: W(R) ~ Z
classical).  So BOTH completions' Witt groups project onto the
SAME mu_8:
    W(R)  = Z    --sig mod 8-->>  mu_8    (<1> -> zeta_8)
    W(Q_2), o.32 --gamma_2----->>  mu_8    (<1> -> zeta_8^(-1))
and W3 locks the two projections inverse on rational forms.
Classical chain naming the SAME Z/8 (Wall; Atiyah-Bott-Shapiro):
the graded Brauer group BW(R) = Z/8 via [Cl(p,q)] <-> p - q mod 8
= signature mod 8 -- the Clifford/Bott period-8 IS this Z/8.
(Cited, not re-proved: it is textbook algebra; the machine
verifies the two Witt->mu_8 arrows and the lock.)

W5 (WHAT THIS DOES AND DOES NOT DO FOR N_c -- the honest scope).
Radon-Hurwitz: rho(2^(4a+b) m) = 8a + 2^b (m odd) -- a function of
v_2(n) ALONE (2-adically continuous in n; verified structurally
below), with period-8 in v_2 that is the Clifford-Bott Z/8 above.
The A2 grammar labels N_c = rho(12) - 1 = 2^(v_2(12)) - 1 = 3.
  DOES: give the grammar's mod-8 backbone a derived-classical
    two-place home -- the clock group is the Weil-index quotient
    of W(Q_2) and the signature-mod-8 quotient of W(R), locked by
    the product formula; the Radon-Hurwitz period-8 is the same
    classical Z/8 (Wall/ABS).  The round-18 m3 route is thereby
    WORKED at its achievable scope: from "order-8 subgroup exists"
    (corroboration) to "canonical quotient homomorphism with the
    clock as generator image" (structure theorem).
  DOES NOT: derive N_c = 3.  The count rho(12) - 1 = 3 is Adams'
    vector-field theorem (archimedean K-theory/topology; dependency
    decomposed in cascade_adams_loadbearing.py -- at the window's
    load-bearing dimensions only the Clifford construction +
    classical pre-K-theory bounds are needed), and the
    selection of layer 12 is the papers' gauge-layer structure.
    HONEST NEGATIVE, REGISTERED: no finite-place derivation of
    N_c is claimed; the open item NARROWS from "find the
    finite-place home of the mod-8/N_c entry" to "the mod-8 home
    is found and classical; the count and the layer remain
    archimedean (Adams + papers)".  Any future claim that the
    finite places produce the 3 is stopping-rule-gated.
No data, no closures, no RH/GRH, no semiclassics.
"""

import cmath
import math

MU8 = [cmath.exp(2j * cmath.pi * j / 8) for j in range(8)]
ZETA8 = MU8[1]


def nearest_mu8(z):
    """Return (j, dist) for the nearest 8th root of unity."""
    best = min(range(8), key=lambda j: abs(z - MU8[j]))
    return best, abs(z - MU8[best])


def gauss_phase(u0, p, k):
    """Phase of sum_{n mod p^k} e^(-2 pi i u0 n^2 / p^k)."""
    N = p ** k
    s = sum(cmath.exp(-2j * cmath.pi * ((u0 * n * n) % N) / N)
            for n in range(N))
    return s / abs(s)


def gamma_p(u, p, kbig=None):
    """Local Weil index gamma_p(u x^2), standard character psi_p.
    u = p^e u0 with p !| u0; phase of the level-k sum, k = e parity."""
    e = 0
    u0 = u
    while u0 % p == 0:
        u0 //= p
        e += 1
    if kbig is None:
        kbig = 8 if p == 2 else 4
    k = kbig + (e % 2 != kbig % 2)   # k of the same parity as e
    return gauss_phase(u0, p, k)


def gamma_inf(u):
    """Archimedean Weil index e^(i pi sgn(u)/4) (T6's clock)."""
    return cmath.exp(1j * cmath.pi * (1 if u > 0 else -1) / 4)


def fresnel_phase_check():
    """Independent numeric check of gamma_inf(1) = zeta_8: phase of
    int_0^T e^(2 pi i x^2) dx + analytic IBP tail (two terms)."""
    T = 10.0
    n = 2000000
    h = T / n
    main = sum(cmath.exp(2j * cmath.pi * ((i + 0.5) * h) ** 2) * h
               for i in range(n))
    # int_T^inf e^(2 pi i x^2) dx by two integrations by parts:
    #   -w/(4 pi i T) * (1 + 1/(4 pi i T^2)) + O(T^-5),  w = e^(2 pi i T^2)
    w = cmath.exp(2j * cmath.pi * T * T)
    tail = -w / (4j * cmath.pi * T) * (1 + 1 / (4j * cmath.pi * T * T))
    z = main + tail
    return z / abs(z)


def rho(n):
    """Radon-Hurwitz number: v_2(n) = 4a + b -> 8a + 2^b."""
    v = 0
    while n % 2 == 0:
        n //= 2
        v += 1
    a, b = divmod(v, 4)
    return 8 * a + 2 ** b


def main():
    print("=" * 74)
    print("THE WITT STEP: the clock group as the Weil-index quotient")
    print("=" * 74)

    # ---- W1: gamma_2 on the 8 square classes
    print()
    print("W1 dyadic Weil index on the 8 square classes of Q_2^x")
    print("   (phase of the level-k sum, k parity = v_2(u); convention:")
    print("   standard adelic character, minus sign at finite places):")
    reps = [1, 3, 5, 7, 2, 6, 10, 14]
    ok_mu8 = ok_stab = ok_class = True
    vals = {}
    for u in reps:
        g_lo = gamma_p(u, 2, kbig=8)
        g_hi = gamma_p(u, 2, kbig=10)
        j, d = nearest_mu8(g_hi)
        ok_mu8 &= d < 1e-9
        ok_stab &= abs(g_lo - g_hi) < 1e-9
        # square-class invariance: multiply by 9 and 25
        ok_class &= abs(gamma_p(9 * u, 2, kbig=10) - g_hi) < 1e-9
        ok_class &= abs(gamma_p(25 * u, 2, kbig=10) - g_hi) < 1e-9
        vals[u] = (j, g_hi)
        print(f"   <{u:>2}>  ->  zeta_8^{j}")
    print(f"   all values in mu_8 exactly   {'PASS' if ok_mu8 else 'FAIL'}")
    print(f"   stable in k (k, k+2)         {'PASS' if ok_stab else 'FAIL'}")
    print(f"   square-class invariant (x9, x25)   "
          f"{'PASS' if ok_class else 'FAIL'}")

    # ---- W2: the quotient theorem
    print()
    print("W2 the quotient  gamma_2 : W(Q_2) ->> mu_8:")
    g1 = vals[1][1]
    hyp = g1 * gamma_p(-1, 2, kbig=10)
    print(f"   hyperbolic plane -> 1:  |gamma(1)gamma(-1) - 1| ="
          f" {abs(hyp - 1):.1e}   {'PASS' if abs(hyp - 1) < 1e-9 else 'FAIL'}")
    print(f"   gamma_2(<1>) = zeta_8^(-1):  |gamma(1) - zeta_8^-1| ="
          f" {abs(g1 - MU8[7]):.1e}   "
          f"{'PASS' if abs(g1 - MU8[7]) < 1e-9 else 'FAIL'}")
    order = next(m for m in range(1, 9) if abs(g1 ** m - 1) < 1e-9)
    print(f"   image of <1> has exact order {order}   "
          f"{'PASS' if order == 8 else 'FAIL'}"
          "   (matches additive order 8 = 2 x level in W(Q_2))")
    image = {vals[u][0] for u in reps}
    g = 8
    for j in image:               # subgroup generated by the NUMERIC
        g = math.gcd(g, j)        # class exponents (additivity is
    surj = (8 // g) == 8          # definitional on diagonal sums)
    print(f"   image generates mu_8 (surjective)   "
          f"{'PASS' if surj else 'FAIL'}"
          f"   (numeric class exponents {sorted(image)}; generated"
          f" subgroup order {8 // g})")
    prim = all(vals[u][0] % 2 == 1 for u in reps)
    print(f"   ALL class exponents odd (primitive roots)   "
          f"{'PASS' if prim else 'FAIL'}   (round-22 F2)")
    print("   => psi-independence: gamma_{psi_a}(<1>) = gamma(a) is")
    print("      primitive for EVERY character, so 'surjection with <1>")
    print("      a generator' is character-free; the kernel moves in")
    print("      its scaling orbit -- 'canonical' = exactly this.")
    print("   |W(Q_2)| = 32 (classical, Lam Ch. VI; cited)  =>  kernel"
          " order 4")

    # ---- W3: product formula per square class
    print()
    print("W3 Weil product formula per class:  Prod_v gamma_v(u) = 1")
    print("   (places: inf, 2, and odd p with v_p(u) odd):")
    ok3 = True
    for u in [1, -1, 2, -2, 3, -3, 5, -5, 6, 15, 9, -9, 45, -18, 25]:
        prod = gamma_inf(u) * gamma_p(u, 2, kbig=10)
        m = abs(u)
        for p in (3, 5, 7, 11, 13):
            if m % p == 0:
                e = 0
                mm = m
                while mm % p == 0:
                    mm //= p
                    e += 1
                if e % 2 == 1:
                    prod *= gamma_p(u, p, kbig=4)
        r = abs(prod - 1)
        ok3 &= r < 1e-8
        print(f"   u = {u:>3}:  |Prod - 1| = {r:.1e}"
              f"   {'PASS' if r < 1e-8 else 'FAIL'}")
    print("   => T-loc3's compensation (u = 1 row) holds PER CLASS:"
          if ok3 else "   => FAILURE above",
          "gamma_2 and gamma_inf are locked inverse on rational forms.")
    sil = all(abs(gamma_p(*uv, kbig=4) - 1) < 1e-9
              for uv in [(9, 3), (45, 3), (25, 5), (3, 5)])
    print(f"   silence gates (round-22 F1): odd p at even valuation and"
          f" unramified\n   odd p give gamma_p = 1 exactly"
          f" (3|9, 3|45, 5|25, 5!|3)   {'PASS' if sil else 'FAIL'}")
    stab = all(abs(gamma_p(u, p, kbig=4) - gamma_p(u, p, kbig=6)) < 1e-9
               for u, p in [(3, 3), (5, 5), (15, 3), (15, 5)])
    print(f"   odd-p factors k-stable (k, k+2)   "
          f"{'PASS' if stab else 'FAIL'}")

    # ---- W4: the archimedean mirror
    print()
    print("W4 archimedean mirror  gamma_inf = zeta_8^sig  (W(R) ->> mu_8):")
    f = fresnel_phase_check()
    print(f"   Fresnel check of gamma_inf(1) = zeta_8:  |phase - zeta_8|"
          f" = {abs(f - ZETA8):.1e}   "
          f"{'PASS' if abs(f - ZETA8) < 1e-6 else 'FAIL'}")
    print("   gamma_inf(-1) = conj (exact, by conjugation); positive")
    print("   rescaling leaves the phase fixed (x -> x/sqrt(u) in R):")
    print("   gamma_inf depends on sig alone -- signature mod 8.")
    print("   Both Witt groups project onto the SAME mu_8; W3 locks the")
    print("   projections inverse.  The Z/8 is Wall/ABS's BW(R) =")
    print("   [Cl(p,q)] <-> p - q mod 8 (classical; cited).")

    # ---- W5: Radon-Hurwitz 2-adicity + the honest negative
    print()
    print("W5 Radon-Hurwitz is a function of v_2 alone; the count is not")
    print("   derived here:")
    ok5 = all(rho(2 ** (v + 4)) - rho(2 ** v) == 8 for v in range(8))
    ok5 &= all(rho(2 ** v * m) == rho(2 ** v) for v in range(6)
               for m in (1, 3, 5, 7, 9))
    print(f"   rho(2^(v+4) m) = rho(2^v m) + 8; odd part irrelevant   "
          f"{'PASS' if ok5 else 'FAIL'}   (period-8 = the W4 Z/8)")
    print(f"   rho(12) - 1 = {rho(12) - 1}   (the A2 label N_c ="
          " 2^(v_2(12)) - 1 = 3)")
    print("   HONEST NEGATIVE, REGISTERED: the 3 is Adams' theorem")
    print("   (archimedean); layer 12 is papers-side.  N_c is NOT")
    print("   derived from the finite places; the open item narrows to")
    print("   the Adams count + the layer selection.")

    print()
    print("=" * 74)
    print("READING (exact + classical + graded; honest scope in docstring)")
    print("=" * 74)
    print("  The clock group mu_8 is the Weil-index quotient of the")
    print("  dyadic Witt group (kernel order 4) and the signature-mod-8")
    print("  quotient of the real Witt group, with <1> -> zeta_8^(-1)")
    print("  and zeta_8 respectively, locked inverse by Weil's product")
    print("  formula per square class.  The Radon-Hurwitz period-8 is")
    print("  the same classical Z/8 (Wall/ABS).  Round-18 m3's open")
    print("  route is WORKED at its achievable scope; N_c = 3 itself")
    print("  remains underived (Adams + layer selection, archimedean).")
    print("  Identification content (graded): reading this mu_8 as THE")
    print("  grammar's clock is the same identification T6/D3.2 made,")
    print("  upgraded from corroboration to canonical-quotient status.")
    print("  No data, no closures, no RH/GRH, no semiclassics.")


if __name__ == "__main__":
    main()
