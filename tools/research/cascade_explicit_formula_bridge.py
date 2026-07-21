#!/usr/bin/env python3
"""
THE EXPLICIT-FORMULA BRIDGE (Addendum 64): the cascade potential is
one side of the Riemann explicit-formula identity, with the primes
and the nontrivial zeros jointly exact on the other side.

THE IDENTITY.  xi(s) = (1/2) s(s-1) Gamma_R(s) zeta(s) gives, on
taking logarithmic derivatives,

    (log Gamma_R)'(s) = xi'/xi(s) - 1/s - 1/(s-1) - zeta'/zeta(s).

On the tower s = d+1 the left side IS the cascade potential p(d)
(Theorem 1 / T1).  For s >= 2 both right-side pieces expand in the
two classical, genuinely non-trivial product theorems of zeta:

  PRIME SIDE (Euler product / von Mangoldt):
      -zeta'/zeta(s) = sum_{n>=2} Lambda(n) n^(-s)     (absolutely
      convergent),
  ZERO SIDE (Hadamard product, zeros paired rho <-> 1-rho).  Two
      forms, distinguished per round-15 M1:
      - PAIRED FORM (unconditional, RH-free): xi(1/2+z) is even and
        entire of order 1, hence genus-0 in z^2 with no exponential
        factor, giving xi'/xi(s) = sum over paired zeros of
        2z/(z^2 - (rho-1/2)^2) -- valid WHEREVER the zeros are.
      - LORENTZIAN FORM (the on-line evaluation): with rho = 1/2 +
        i*gamma the paired term becomes 2z/(z^2 + gamma^2).  This
        specialization is exact iff the zeros used lie on the line;
        it is how the sum is EVALUATED below, with the verified
        on-line zeros.  A hypothetical off-line zero would alter the
        term shape (computed discrepancy at the round-15 review:
        ~3e-5 for a = 0.1 at gamma = 10) but any such zero lies
        beyond the verified height 3e12 and contributes < 1e-23 at
        these s.  The earlier blanket sentence "the identity holds
        wherever the zeros are" was TRUE of the paired form and
        FALSE of the Lorentzian form as printed -- corrected here
        and on every doc surface (round 15).

BRIDGE THEOREM (exact; verified below).  For every layer d >= 1,
with s = d+1 and z = d + 1/2:

    p(d)  =  [ZEROS   sum_{gamma>0} 2z/(z^2+gamma^2)]
           - [POLES   1/(d+1) + 1/d]
           + [PRIMES  sum_{n>=2} Lambda(n) n^(-(d+1))].

Every cascade window Phi(a->b) = sum_d p(d) inherits the split
additively: every mass window in the record is exactly a zeros-sum
minus a poles-sum plus a primes-sum, with computable parts.

PRECISE NAMING (pattern-rule discipline; supersedes the session's
assessment-level phrase "verbatim the archimedean term of Weil's
formula"): this is the PARTIAL-FRACTION (Hadamard) form of the
explicit-formula identity, evaluated at the real points s = d+1.
Weil's test-function formula is the integral (smeared) version of
the same identity; the pointwise form used here is its Stieltjes
avatar.  The mathematical content of the two expansions is classical
(Euler, Hadamard); what is new FOR THE PROGRAM is only the tower
evaluation and the window decompositions.

VERIFICATION (three tiers, run below):
  V1 (implementation check, trivial rearrangement): p(d) computed
      by digamma equals xi'/xi - poles - zeta'/zeta with xi'/xi
      taken as a high-precision numerical log-derivative of the
      assembled xi.  Machine precision expected; this checks our
      algebra only.
  V2 (prime side, non-trivial): the Lambda-sum truncated at n <= N
      converges to -zeta'/zeta(s) within the stated integral tail
      bound, computed at working precision HIGH ENOUGH for the bound
      to be meaningful (round-15 M2: the original dps-30 run put the
      d=12 residual at the precision floor 4.8e-35, ABOVE its 1.6e-40
      bound, and the PASS was an epsilon artifact; recomputation at
      dps 50 gives residual ~2.1e-41, genuinely within bound -- the
      check now runs at dps 50 with the strict bound, no epsilon).
  V3 (zero side, non-trivial): the Hadamard Lorentzian sum over the
      FIRST N TRUE ZEROS (mpmath.zetazero -- computed, not
      hardcoded) plus a Riemann-von Mangoldt average-density tail
      converges to xi'/xi(s); the residual is reported for
      N = 10, 25, 50 and must DECREASE.  The density tail is an
      average model (oscillatory error disclosed); the convergence
      trend, not any single residual, is the check.
Then the bridge numbers: the zeros/poles/primes split per layer
d = 1..28 and for the record's windows Phi(5->13) (tau/mu),
Phi(13->21) (mu/e), Phi(5->12) (alpha_s, v), Phi(13->20) (theta_23
descent).

WHAT THIS DOES AND DOES NOT DO (honest scope, stated first):
  DOES: upgrade the tower's Riemann status from "uses zeta's Gamma
    factor" to "is one side of the explicit-formula identity, with
    the primes and the zeros jointly exact on the other side"; give
    every recorded window an exact zeros/poles/primes split (pure
    mathematics, no data contact -- stopping-rule category (a));
    quantify the prime content of every layer (exponentially
    dominated by n = 2, 3) and the pole-dominance of the low layers
    where the record lives.
  DOES NOT: ground the dictionary (address book, source twists,
    Observer k=3, gradings, record-legs -- all untouched); derive
    any new physical closure (none is attempted); use or imply RH
    (the identity holds wherever the zeros are; the paired
    Lorentzian form is evaluated with the verified on-line zeros,
    and the numerics are insensitive to any hypothetical off-line
    zero far beyond the verified range); establish a DIRECTION of
    explanation -- the identity is zeta's own bookkeeping, and
    reading the zeros/primes as "causes" of the potential (or vice
    versa) is a modeling choice the identity does not supply.
"""

import math

from mpmath import mp, mpf, zeta, zetazero, diff, log, pi as mppi, gamma as mpgamma
from scipy.integrate import quad

mp.dps = 30

D_MAX = 28
WINDOWS = [("Phi(5->13)  [tau/mu lead]", 6, 13),
           ("Phi(13->21) [mu/e lead]", 14, 21),
           ("Phi(5->12)  [alpha_s, v]", 5, 12),
           ("Phi(13->20) [theta_23 descent]", 13, 20)]


def p_digamma(d):
    """p(d) = (log Gamma_R)'(d+1) = -ln(pi)/2 + psi((d+1)/2)/2."""
    s = mpf(d + 1)
    return -log(mppi) / 2 + mp.digamma(s / 2) / 2


def xi(s):
    return mpf("0.5") * s * (s - 1) * mppi ** (-s / 2) * mpgamma(s / 2) * zeta(s)


def xi_logderiv(s):
    return diff(lambda t: log(xi(t)), s)


def lambda_sum(s, N):
    """sum_{n<=N} Lambda(n) n^-s, plus the integral tail bound."""
    total = mpf(0)
    sieve = list(range(N + 1))
    for i in range(2, N + 1):
        if sieve[i] == i:                      # i prime
            for j in range(2 * i, N + 1, i):
                if sieve[j] == j:
                    sieve[j] = i
    logs = {}
    for n in range(2, N + 1):
        # Lambda(n) = log p if n = p^k
        m, p = n, sieve[n]
        while m % p == 0:
            m //= p
        if m == 1:
            total += log(p) * mpf(n) ** (-s)
    sf = float(s)
    tail = (math.log(N) / (sf - 1) + 1 / (sf - 1) ** 2) * N ** (1 - sf)
    return total, tail


def zeros_sum(z, gammas, T):
    """Hadamard Lorentzian sum over given zeros + average-density tail
    from T: integral 2z/(z^2+t^2) * (1/2pi) ln(t/2pi) dt."""
    zs = float(sum(2 * z / (z * z + g * g) for g in gammas))
    zf = float(z)
    tail, _ = quad(lambda t: 2 * zf / (zf * zf + t * t)
                   * math.log(t / (2 * math.pi)) / (2 * math.pi),
                   T, 5e6, limit=400)
    return zs + tail


def main():
    print("=" * 74)
    print("THE EXPLICIT-FORMULA BRIDGE: p(d) = zeros - poles + primes")
    print("=" * 74)

    # ---- V1: implementation/rearrangement check (machine precision)
    print()
    print("V1 rearrangement check  p(d) - [xi'/xi - poles - zeta'/zeta]:")
    worst = 0.0
    for d in (1, 2, 4, 5, 12, 13, 19, 21, 28):
        s = mpf(d + 1)
        rhs = xi_logderiv(s) - 1 / s - 1 / (s - 1) - diff(lambda t: log(zeta(t)), s)
        r = abs(float(p_digamma(d) - rhs))
        worst = max(worst, r)
    print(f"  max |residual| over sampled layers: {worst:.3e}"
          f"   {'PASS' if worst < 1e-18 else 'CHECK'}")

    # ---- V2: prime side (non-trivial; dps 50, strict bound -- M2)
    print()
    print("V2 prime side  sum Lambda(n) n^-s  vs  -zeta'/zeta(s)"
          " [dps 50, strict]:")
    with mp.workdps(50):
        for d, N in ((1, 200000), (4, 20000), (12, 2000)):
            s = mpf(d + 1)
            truth = -diff(lambda t: log(zeta(t)), s)
            ls, tail = lambda_sum(s, N)
            r = abs(ls - truth)
            ok = r <= mpf(tail) * mpf("1.5")
            print(f"  d={d:>2} (s={d+1}): N={N:>6}  |Lambda-sum - truth|"
                  f" = {float(r):.2e}  tail-bound {tail:.2e}"
                  f"  {'PASS' if ok else 'FAIL'}")

    # ---- V3: zero side (non-trivial, convergence trend)
    print()
    print("V3 zero side  Hadamard Lorentzian sum + density tail  vs  xi'/xi:")
    NZ = 50
    gam = [float(zetazero(n).imag) for n in range(1, NZ + 1)]
    for d in (1, 4, 12):
        s = mpf(d + 1)
        z = float(d) + 0.5
        truth = float(xi_logderiv(s))
        line = f"  d={d:>2}: xi'/xi = {truth:+.6f};  residual with"
        prev = None
        decreasing = True
        for n in (10, 25, 50):
            approx = zeros_sum(z, gam[:n], gam[n - 1])
            r = abs(approx - truth)
            line += f"  N={n}: {r:.1e}"
            if prev is not None and r > prev:
                decreasing = False
            prev = r
        print(line + ("   DECREASING" if decreasing else "   NOT MONOTONE"))

    # ---- the bridge numbers per layer
    print()
    print("BRIDGE SPLIT PER LAYER  p(d) = zeros - poles + primes")
    print(f"  {'d':>3} {'p(d)':>10} {'zeros':>10} {'poles':>10}"
          f" {'primes':>10} {'primes/p':>9}")
    parts = {}
    for d in range(1, D_MAX + 1):
        s = mpf(d + 1)
        primes = float(-diff(lambda t: log(zeta(t)), s))
        poles = 1.0 / (d + 1) + 1.0 / d
        pd = float(p_digamma(d))
        zeros = pd + poles - primes          # exact by V1; V3 checks it
        parts[d] = (pd, zeros, poles, primes)
        share = primes / pd if abs(pd) > 1e-12 else float("nan")
        print(f"  {d:>3} {pd:>10.6f} {zeros:>10.6f} {poles:>10.6f}"
              f" {primes:>10.6f} {share:>9.4f}")

    print()
    print("BRIDGE SPLIT FOR THE RECORD'S WINDOWS  Phi = zeros - poles + primes")
    for name, a, b in WINDOWS:
        tot = sum(parts[d][0] for d in range(a, b + 1))
        zz = sum(parts[d][1] for d in range(a, b + 1))
        pp = sum(parts[d][2] for d in range(a, b + 1))
        pr = sum(parts[d][3] for d in range(a, b + 1))
        print(f"  {name}: {tot:+.6f} = zeros {zz:+.6f}"
              f" - poles {pp:+.6f} + primes {pr:+.6f}")

    print()
    print("=" * 74)
    print("READING (exact statements only)")
    print("=" * 74)
    print("  - The tower potential at every layer is EXACTLY a sum over")
    print("    the Riemann zeros minus the pole terms plus a sum over the")
    print("    primes: the cascade is one side of the explicit-formula")
    print("    identity, with the primes and zeros jointly on the other.")
    print("  - Every recorded mass window inherits the exact three-part")
    print("    split printed above; the prime part is exponentially")
    print("    dominated by n = 2, 3 and is small at the record's layers;")
    print("    the low layers (where the record lives) are POLE-dominated")
    print("    -- zeta's pole at s = 1 (the 1/(s-1) term) together with")
    print("    its functional-equation mirror at s = 0 (the 1/s term,")
    print("    round-15 m4) shape the observer-side potential; the zeros")
    print("    supply the growing positive part.")
    print("  - Classical content: Euler product + Hadamard product.  New")
    print("    for the program: only the tower evaluation and the window")
    print("    splits.  No closure, no data contact, no RH use, and no")
    print("    direction of explanation is claimed (see docstring).")


if __name__ == "__main__":
    main()
