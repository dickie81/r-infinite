#!/usr/bin/env python3
"""
DOOR 3 (Addendum 69): the finite places -- the global potential
identity, the dyadic home of the clock, and the product-formula
avatar.  Category (a): exact identities, no data contact, no
closures; every identification graded; nothing here is claimed
"forced" (rule of A66: every forced must name its forcer -- none
does, so none is claimed).

CONTEXT.  The whole program to date lives at ONE place of Q: the
archimedean one (Gamma_R, the Gaussian, the Weil index, the
Theorem-1b bridge).  Yet the A2 grammar carries 2-adic entries
(N_c = 2^(v_2(12)) - 1, the Radon-Hurwitz count; the mod-8 clock)
and 3-adic entries (conductor-3 colour, Q(zeta_3)) with no account
of their arithmetic home.  This file opens the non-archimedean door
at the identity layer -- the safe layer -- in three exact steps.

D3.1 (GLOBAL POTENTIAL IDENTITY -- exact; a re-organization of
Theorem 1b).  Give EVERY place v of Q its local potential
    p_v(s) := (log E_v)'(s),
with E_infinity = Gamma_R (so p_infinity = the cascade potential
p(d), Theorem 1) and E_p = (1 - p^(-s))^(-1) (the Euler factor), so
    p_p(s) = (log E_p)'(s) = -ln p/(p^s - 1)   (negative: each
    finite place's potential DRAINS), and sum_p p_p = zeta'/zeta.
Then xi = (1/2) s(s-1) prod_v E_v gives, exactly:

    sum over ALL places  p_v(s)  =  xi'/xi(s) - 1/s - 1/(s-1).

THE BRIDGE'S "PRIME SIDE" IS (MINUS) THE FINITE PLACES' POTENTIALS:
Theorem 1b's "+ primes" term is -sum_p p_p(s) = sum Lambda(n)n^-s,
so 1b reads: the archimedean potential equals the zeros side minus
every OTHER place's potential.  (RUN RECORD: the first run of this
file stated the identity with the finite potentials' sign flipped
and D3.1 FAILED 3/3; the convention above is the corrected one and
the failure is kept on the record per the verified-record rule.)  The tower is one member of an adelic
family of towers, one per place.  Verified numerically below, with
the per-place shares ACROSS the record's layers: p = 2 and p = 3 --
exactly the primes carrying the program's discrete structure --
jointly carry ~94-100% of the finite-place total (94.2% at the
observer twist s = 4; 99.0% at s = 6; ~100% by s = 13; round-18 M2
replaced the earlier s=6-only '~99% at the record's layers').

D3.2 (THE CLOCK IS DYADIC -- classical, Gauss; verified by direct
summation).  The normalized quadratic Gauss sums G(q)/sqrt(q),
G(q) = sum_{n mod q} e^(2 pi i n^2/q):
    odd q:        phase in {1, i}        (order <= 4; 1 iff q = 1
                  mod 4, i iff q = 3 mod 4 -- Gauss's theorem),
    q = 0 mod 4:  phase = e^(i pi/4) = zeta_8  (the CLOCK),
    q = 2 mod 4:  G(q) = 0.
The order-8 element -- T6's Weil-index clock gamma = zeta_8 -- is
DYADIC-EXCLUSIVE among the finite-place Gauss phases: no odd
modulus produces it; every 4-divisible (dyadic-even) modulus does.
The grading of this statement: an exact classical theorem plus an
IDENTIFICATION (reading the dyadic Gauss phase as the finite-place
avatar of T6's archimedean clock); the identification is motivated
by D3.3, where the two provably meet.

D3.3 (PRODUCT-FORMULA AVATAR -- Landsberg-Schaar; verified
numerically).  The Landsberg-Schaar relation

  (1/sqrt p) sum_{n=0}^{p-1} e^(2 pi i n^2 q / p)
      = (e^(i pi/4)/sqrt(2q)) sum_{n=0}^{2q-1} e^(-pi i n^2 p/(2q))

(p, q positive integers; the classical avatar of Weil's metaplectic
product formula prod_v gamma_v = 1) exchanges the place-p data for
place-2q data with mediating constant e^(i pi/4) = gamma_infinity =
THE CLOCK: the archimedean Weil index is the exchange rate between
finite places.  Verified below on an 18-pair grid INCLUDING even p
and both parities of pq (round-18 m6: the original 10-pair grid was
odd-p-only and could not have detected a parity restriction); the
round-18 review independently brute-forced 1000 pairs at dps 40:
ZERO failures -- the unrestricted (p, q positive integers) form
stands, and no parity restriction exists to report.

WHAT THIS DOES AND DOES NOT DO (honest scope, stated first):
  DOES: establish the arena -- every place has a potential and the
    global sum is the zeros side (exact); locate the order-8 clock's
    finite-place home at p = 2 (exact + graded identification);
    machine-verify the product-formula avatar with the clock as
    mediator (exact).
  DOES NOT: derive any A2 grammar entry from the finite places (the
    N_c = 2^(v_2(12)) - 1 form remains a labeling; conductor-3
    colour remains T8's + the C2 convention); construct 2-adic or
    3-adic Tate theory (the open next step, named not opened);
    touch data, close anything, or use RH/GRH (the global identity
    is pole/zero-agnostic in the same paired sense as Theorem 1b).
"""

import cmath
import math

from mpmath import mp, mpf, zeta, diff, log, pi as mppi, gamma as mpgamma

mp.dps = 30

PRIMES = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def p_inf(s):
    return -log(mppi) / 2 + mp.digamma(mpf(s) / 2) / 2


def p_local(p, s):
    """Finite-place potential p_p(s) = (log E_p)'(s) = -ln p/(p^s-1)
    (negative; sum over p equals zeta'/zeta)."""
    return -log(p) / (mpf(p) ** s - 1)


def xi_logderiv(s):
    def xi(t):
        return mpf("0.5") * t * (t - 1) * mppi ** (-t / 2) \
            * mpgamma(t / 2) * zeta(t)
    return diff(lambda t: log(xi(t)), mpf(s))


def gauss_sum(q):
    return sum(cmath.exp(2j * cmath.pi * (n * n) / q) for n in range(q))


def ls_lhs(p, q):
    return sum(cmath.exp(2j * cmath.pi * n * n * q / p)
               for n in range(p)) / math.sqrt(p)


def ls_rhs(p, q):
    zeta8 = cmath.exp(1j * cmath.pi / 4)
    return zeta8 / math.sqrt(2 * q) * sum(
        cmath.exp(-1j * cmath.pi * n * n * p / (2 * q))
        for n in range(2 * q))


def main():
    print("=" * 74)
    print("DOOR 3: the finite places")
    print("=" * 74)

    # ---- D3.1: global potential identity
    print()
    print("D3.1 global potential identity"
          "  sum_v p_v(s) = xi'/xi - 1/s - 1/(s-1):")
    for s in (2, 6, 13):
        s = mpf(s)
        finite = diff(lambda t: log(zeta(t)), s)   # sum_p p_p = zeta'/zeta
        lhs = p_inf(s) + finite
        rhs = xi_logderiv(s) - 1 / s - 1 / (s - 1)
        r = abs(float(lhs - rhs))
        print(f"  s={int(s):>2}: |sum_v p_v - (xi'/xi - poles)| = {r:.2e}"
              f"   {'PASS' if r < 1e-25 else 'FAIL'}")
    print("  per-place shares of the finite-place total ACROSS the")
    print("  record's layers (round-18 M2: previously computed at s = 6")
    print("  only while claimed for 'the record's layers'):")
    for sv in (4, 5, 6, 13, 21):
        s = mpf(sv)
        total = float(diff(lambda t: log(zeta(t)), s))
        j = (float(p_local(2, s)) + float(p_local(3, s))) / total
        p2 = float(p_local(2, s)) / total
        print(f"    s={sv:>2}:  p=2: {p2*100:6.2f}%   p=2,3 jointly:"
              f" {j*100:6.2f}%")
    print("    => the joint share RANGES ~94-100% across the record's")
    print("       layers (94.2% at the observer twist s=4, 99.0% at s=6,")
    print("       ~100% by s=13); the '~99%' shorthand was s=6-only")

    # ---- D3.2: the clock is dyadic
    print()
    print("D3.2 normalized Gauss phases  G(q)/sqrt(q):")
    ok = True
    zeta8 = cmath.exp(1j * cmath.pi / 4)
    for q in [3, 5, 7, 11, 13, 17, 19, 97, 101, 499,
              9, 15, 21, 25, 27, 33, 35, 45, 49, 63, 81, 99, 105, 121,
              225, 495]:   # round-18 M1: composites included
        g = gauss_sum(q) / math.sqrt(q)
        want = 1 if q % 4 == 1 else 1j
        ok &= abs(g - want) < 1e-8
    print(f"  odd moduli (primes AND composites) up to 499: phase in"
          f" {{1, i}} exactly per q mod 4   {'PASS' if ok else 'FAIL'}"
          "   (order <= 4)")
    ok8 = True
    for q in [4, 8, 16, 32, 64,
              12, 20, 24, 28, 36, 44, 48, 60, 100, 108, 180]:
        # round-18 M1: non-power-of-2 4-divisible moduli included
        g = gauss_sum(q) / math.sqrt(q)
        ok8 &= abs(g / abs(g) - zeta8) < 1e-8
    print(f"  4-divisible moduli (powers of 2 AND others, to 180):"
          f" phase = zeta_8   {'PASS' if ok8 else 'FAIL'}"
          "   (order 8: DYADIC-EXCLUSIVE)")
    z2 = True
    for q in [6, 10, 14, 18]:
        z2 &= abs(gauss_sum(q)) < 1e-8
    print(f"  q = 2 mod 4: G(q) = 0   {'PASS' if z2 else 'FAIL'}")

    # ---- D3.3: Landsberg-Schaar
    print()
    print("D3.3 Landsberg-Schaar (product-formula avatar; mediator ="
          " e^(i pi/4) = the clock):")
    results = []
    for p, q in [(3, 1), (5, 1), (7, 1), (5, 3), (7, 2), (9, 4),
                 (11, 5), (13, 3), (15, 7), (21, 2),
                 (2, 3), (4, 5), (6, 7), (8, 3), (10, 9), (12, 5),
                 (16, 1), (18, 11)]:   # round-18 m6: even p included
        d = abs(ls_lhs(p, q) - ls_rhs(p, q))
        results.append((p, q, d))
    good = [(p, q) for p, q, d in results if d < 1e-9]
    bad = [(p, q, d) for p, q, d in results if d >= 1e-9]
    print(f"  verified exactly (<1e-9) at: {good}")
    if bad:
        print(f"  NOT satisfied at: {[(p,q) for p,q,_ in bad]}"
              " -- parity restriction reported as found")
    print("  the mediating constant between finite places is the")
    print("  archimedean Weil index gamma_inf = zeta_8 -- T6's clock as")
    print("  the inter-place exchange rate (identification graded in the")
    print("  docstring; the exact content is the identity itself).")

    print()
    print("=" * 74)
    print("READING (exact + graded)")
    print("=" * 74)
    print("  - The tower is ONE MEMBER of an adelic family: every place")
    print("    has a potential, and the global sum is the zeros side.")
    print("    Theorem 1b's 'prime side' is the finite places'")
    print("    potentials; p = 2, 3 carry ~94-100% across the record's")
    print("    layers (99.0% at s = 6) --")
    print("    the same primes carrying the grammar's discrete entries")
    print("    (v_2 counts; conductor-3 colour).  That coincidence is")
    print("    NOTED, not claimed as derivation.")
    print("  - The order-8 clock element is dyadic-exclusive among")
    print("    finite-place Gauss phases, and the clock itself is the")
    print("    Landsberg-Schaar exchange constant: the mod-8 structure")
    print("    is a real <-> 2-adic duality at the identity level.")
    print("  - No grammar entry is derived; 2-adic/3-adic Tate theory is")
    print("    the named next step.  No data, no closures, no RH/GRH.")


if __name__ == "__main__":
    main()
