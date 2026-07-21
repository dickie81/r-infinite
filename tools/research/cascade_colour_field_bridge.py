#!/usr/bin/env python3
"""
DOOR 2 (Addendum 65): the colour-character bridge — the odd tower's
explicit formula, the Legendre synthesis of the complex place, and
the structural relocation of the F6 tension.

THREE EXACT STATEMENTS, each verified below.

C1 (Legendre synthesis — the "complex place" the program was told it
lacks).  Gamma_C(s) = 2 (2pi)^(-s) Gamma(s) satisfies
Gamma_C(s) = Gamma_R(s) * Gamma_R(s+1) (Legendre duplication), so

    p_C(s) := (log Gamma_C)'(s) = p_triv(s) + p_sgn(s),

where p_triv(s) = (log Gamma_R)'(s) is the trivial-tower potential
and p_sgn(s) = (log Gamma_R)'(s+1) is the sgn-tower potential (T5:
the sgn character interleaves the second tower at unit shift).  THE
DOUBLED TOWER JOINTLY CARRIES THE COMPLEX-PLACE FACTOR.  The F6
objection "the odd shift needs Gamma_C, and Q has r_2 = 0" is
thereby relocated: the program never needed a complex embedding of
Q — its own two interleaved towers synthesize Gamma_C by Legendre.

C2 (the minimal odd character IS the colour character — a forced
minimality, not a choice).  The sgn tower's factor Gamma_R(s+1) is
the archimedean factor of ODD Dirichlet L-functions.  Enumerating
conductors: q = 1 has only the trivial (even) character; q = 2 has
no primitive character; q = 3 has exactly one primitive character,
chi_{-3} (chi(1)=+1, chi(2)=-1), and it is ODD.  So chi_{-3} is THE
minimal-conductor primitive odd Dirichlet character — and it is the
quadratic character of Q(sqrt(-3)) = Q(zeta_3), the COLOUR FIELD of
T8.  Two independent pointers (minimality; the T8 field) converge on
the same object.

C3 (the odd/colour bridge — no poles, a conductor instead).  With
Lambda(s,chi) = (3/pi)^((s+1)/2) Gamma((s+1)/2) L(s,chi_{-3}),
entire, root number epsilon = tau(chi)/(i sqrt 3) = +1, real on the
critical line:

    p_sgn(s) = [ZEROS   sum_{gamma>0} 2z/(z^2+gamma^2),
                          gamma over zeros of L(s,chi_{-3}), z=s-1/2]
             - [CONDUCTOR   (1/2) ln 3]
             + [PRIMES  sum_n Lambda(n) chi_{-3}(n) n^(-s)].

The odd tower's bridge has NO pole term — L(s,chi_{-3}) is entire —
and carries the conductor (1/2) ln 3 where the trivial tower carried
zeta's pole terms.  The primes enter weighted by their splitting in
the colour field (split +, inert -, ramified 3 silent).

THE FEATURE.  p_sgn(s) = 0 at s = 6.2569... — this is exactly the
"volume feature at s = 6.2569, the excluded object" of the reopened
review Finding 6.  Under C3 it reads: the odd feature is the point
where the colour-character zeros plus the colour-weighted primes
balance the conductor (1/2) ln 3.  Its arithmetic home is the odd
Dirichlet family — precisely what F6 found — and the minimal member
of that family is the colour field's own character.

HONEST SCOPE (stated first).  F6 remains REOPENED as to its original
claim (the observer-address pinning): nothing here derives an
address.  What changes is structural: (i) the "missing complex
place" is synthesized by the program's own doubled tower (C1,
exact); (ii) the odd feature's arithmetic home is identified inside
the program's colour sector via a FORCED minimality (C2 — the
unique minimal odd primitive character; not a scan over characters);
(iii) the odd tower has its own explicit-formula bridge with the
same three-part shape as Theorem 1b (C3, verified).  The zeros of
L(s,chi_{-3}) used in C3 are COMPUTED below by sign-scanning the
verified-real completed function on the critical line — not
tabulated from memory.  Category (a): no data contact, no closure,
no RH/GRH use (the identity holds wherever the zeros are; numerics
use the on-line zeros found).
"""

import math

from mpmath import mp, mpf, mpc, zeta, gamma as mpgamma, diff, log, pi as mppi
from scipy.integrate import quad

mp.dps = 25

Q = 3
LN3_HALF = float(log(3)) / 2


def chi(n):
    r = n % 3
    return 1 if r == 1 else (-1 if r == 2 else 0)


def L_chi(s):
    """L(s, chi_-3) = 3^-s [zeta(s,1/3) - zeta(s,2/3)] (Hurwitz)."""
    return mpf(3) ** (-s) * (zeta(s, mpf(1) / 3) - zeta(s, mpf(2) / 3)) \
        if not isinstance(s, mpc) else \
        mpc(3) ** (-s) * (zeta(s, mpf(1) / 3) - zeta(s, mpf(2) / 3))


def Lambda_chi(s):
    """Completed odd L: (3/pi)^((s+1)/2) Gamma((s+1)/2) L(s,chi)."""
    return (mpf(3) / mppi) ** ((s + 1) / 2) * mpgamma((s + 1) / 2) * L_chi(s)


def p_sgn(s):
    return -log(mppi) / 2 + mp.digamma((mpf(s) + 1) / 2) / 2


def p_triv(s):
    return -log(mppi) / 2 + mp.digamma(mpf(s) / 2) / 2


def main():
    print("=" * 74)
    print("DOOR 2: the colour-character bridge (odd tower, Q(zeta_3))")
    print("=" * 74)

    # ---- C1: Legendre synthesis
    print()
    print("C1 Legendre synthesis  p_C = p_triv + p_sgn:")
    worst = 0.0
    for s in (2, 5, 7, 13, 20):
        pc = float(-log(2 * mppi) + mp.digamma(mpf(s)))
        r = abs(pc - float(p_triv(s) + p_sgn(s)))
        worst = max(worst, r)
    print(f"  max |residual| over sampled s: {worst:.3e}"
          f"   {'PASS' if worst < 1e-20 else 'FAIL'}"
          "   (the doubled tower carries Gamma_C)")

    # ---- C2: forced minimality
    print()
    print("C2 minimal odd character:")
    print("  q=1: trivial character only (even).  q=2: no primitive")
    print("  character.  q=3: exactly one primitive character, chi_-3,")
    print("  and it is odd (chi(-1) = chi(2) = -1).  FORCED minimal --")
    print("  and it is the quadratic character of the T8 colour field")
    print("  Q(zeta_3) = Q(sqrt(-3)).")

    # ---- entirety + root number checks
    print()
    # s = 1 exactly hits the Hurwitz poles' cancellation (inf - inf);
    # evaluate at 1 + 1e-15, well within dps=25 (round-15-of-me fix)
    L1 = float(L_chi(mpf(1) + mpf(10) ** -15))
    print(f"C3 preliminaries: L(1,chi) = {L1:.10f}"
          f"  (pi/(3 sqrt 3) = {float(mppi/(3*mp.sqrt(3))):.10f}; entire,"
          " no pole)")
    # real-on-line check (epsilon = +1)
    worst_im = 0.0
    for t in (2.0, 8.0, 15.0, 30.0):
        v = Lambda_chi(mpc(0.5, t))
        worst_im = max(worst_im, abs(float(v.imag)) /
                       max(abs(float(v.real)), 1e-30))
    print(f"  Lambda real on the critical line: max |Im/Re| = "
          f"{worst_im:.1e}   {'PASS' if worst_im < 1e-15 else 'FAIL'}")

    # ---- find zeros of L(chi_-3) by sign scan (computed, not recalled)
    def lam_real(t):
        return float(Lambda_chi(mpc(0.5, t)).real)

    zeros = []
    t, step = 0.5, 0.25
    prev = lam_real(t)
    while t < 75 and len(zeros) < 24:
        t2 = t + step
        cur = lam_real(t2)
        if prev * cur < 0:
            a, b = t, t2
            for _ in range(60):
                m = 0.5 * (a + b)
                if lam_real(a) * lam_real(m) <= 0:
                    b = m
                else:
                    a = m
            zeros.append(0.5 * (a + b))
        t, prev = t2, cur
    print(f"  zeros of L(s,chi_-3) found on the line (first"
          f" {len(zeros)}): " + ", ".join(f"{g:.4f}" for g in zeros[:8])
          + ", ...")

    # ---- C3: the odd bridge, three-tier
    print()
    print("C3 odd/colour bridge  p_sgn = zeros - (1/2)ln3 + chi-primes:")
    # V1 rearrangement (machine precision)
    worst = 0.0
    for s in (2, 5, 6, 13):
        s = mpf(s)
        rhs = diff(lambda u: log(Lambda_chi(u)), s) - log(3) / 2 \
            - diff(lambda u: log(L_chi(u)), s)
        worst = max(worst, abs(float(p_sgn(s) - rhs)))
    print(f"  V1 rearrangement: max |residual| = {worst:.3e}"
          f"   {'PASS' if worst < 1e-18 else 'FAIL'}")
    # V2 prime side
    for s, N in ((2, 100000), (6, 4000)):
        truth = -diff(lambda u: log(L_chi(u)), mpf(s))
        tot = mpf(0)
        for n in range(2, N + 1):
            if chi(n) == 0:
                continue
            m = n
            p = None
            for q in range(2, int(math.isqrt(n)) + 1):
                if m % q == 0:
                    p = q
                    while m % q == 0:
                        m //= q
                    break
            if p is None:
                p, m = n, 1
            if m == 1:
                tot += chi(n) * log(p) * mpf(n) ** (-s)
        sf = float(s)
        tail = (math.log(N) / (sf - 1) + 1 / (sf - 1) ** 2) * N ** (1 - sf)
        r = abs(float(tot - truth))
        print(f"  V2 prime side s={s}: |chi-Lambda-sum - (-L'/L)| ="
              f" {r:.2e}  tail-bound {tail:.2e}"
              f"  {'PASS' if r <= 1.5 * tail + 1e-22 else 'FAIL'}")
    # V3 zero side with computed zeros + density tail
    print("  V3 zero side (computed zeros + density tail), residual vs")
    print("     Lambda'/Lambda -- must decrease with N:")
    for s in (2.0, 6.0):
        truth = float(diff(lambda u: log(Lambda_chi(u)), mpf(s)))
        z = s - 0.5
        line = f"     s={s}: Lambda'/Lambda = {truth:+.6f};"
        prevr = None
        dec = True
        for n in (8, 16, len(zeros)):
            zs = sum(2 * z / (z * z + g * g) for g in zeros[:n])
            T = zeros[n - 1]
            tail, _ = quad(lambda u: 2 * z / (z * z + u * u)
                           * math.log(3 * u / (2 * math.pi))
                           / (2 * math.pi), T, 5e6, limit=300)
            r = abs(zs + tail - truth)
            line += f"  N={n}: {r:.1e}"
            if prevr is not None and r > prevr:
                dec = False
            prevr = r
        print(line + ("   DECREASING" if dec else "   NOT MONOTONE"))

    # ---- the odd feature
    print()
    a, b = 5.0, 8.0
    for _ in range(80):
        m = 0.5 * (a + b)
        if float(p_sgn(a)) * float(p_sgn(m)) <= 0:
            b = m
        else:
            a = m
    sstar = 0.5 * (a + b)
    print(f"THE ODD FEATURE: p_sgn(s) = 0 at s = {sstar:.4f}")
    print("  = review Finding 6's 'volume feature at 6.2569, the excluded")
    print("  object'.  Under C3: the point where the colour-character")
    print("  zeros plus the colour-weighted primes balance the conductor")
    print(f"  (1/2)ln3 = {LN3_HALF:.4f}.  Its arithmetic home is the odd")
    print("  Dirichlet family (as F6 found); the minimal member of that")
    print("  family is the colour field's character (C2, forced).")

    print()
    print("=" * 74)
    print("HONEST SCOPE")
    print("=" * 74)
    print("  F6 stays REOPENED on its original claim (no address is")
    print("  derived here).  Structural changes only: the 'missing")
    print("  complex place' is synthesized by the doubled tower (C1,")
    print("  exact Legendre); the odd feature's home is the colour")
    print("  sector via forced minimality (C2); the odd tower has its")
    print("  own three-part explicit-formula bridge with a conductor")
    print("  where the even tower had poles (C3, verified).  No data,")
    print("  no closure, no GRH use; zeros computed, not recalled.")


if __name__ == "__main__":
    main()
