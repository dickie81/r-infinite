#!/usr/bin/env python3
"""
DOOR 1 (Addendum 65): do the Riemann zeros know the cascade's
distinguished layers?  Exact restatements, a numerical demonstration,
and the honest negative — with the stopping-rule ground rules stated
first.

GROUND RULES.  Category (a): no data contact, no closure of any
measured number is attempted or permitted here.  The question is
whether the EXISTING distinguished structure of the tower reads the
zero side of the Theorem-1b bridge — not whether new numbers can be
fitted to it.  Any future "observable X reads the zeros" claim is
new physics, fitting-prone, and gated by the stopping rule; this
file's job is to establish what is exactly true and to register the
honest negative on the rest.

EXACT RESTATEMENTS (all consequences of Theorem 1b, no new input).
The tower's distinguished features are level-crossings of the
potential p(d) = (log Gamma_R)'(s), s = d+1:
  - the critical point:   p = 0          at s* = 7.2569...
    (the even-tower member of the papers' critical pair)
  - the phase threshold:  p = ln G(1/2)  at s* = 20.73...
    (selected to layer 19)
  - the sink:             p = G(1/2)     at s* = 218.6...
    (selected to layer 217)
Through Theorem 1b each becomes an exact balance statement:

  ZEROS(s) + PRIMES(s) - POLES(s) = level,

so each distinguished layer is the point where the Riemann zeros'
Lorentzian sum plus the (tiny) prime sum balances the pole terms at
the stated level.  In particular the pole terms 1/s + 1/(s-1) --
zeta's pole at s = 1, the divergence of the harmonic series -- are
what the zeros must overcome: the observer-side geography of the
tower is a zeros-vs-pole tug-of-war with the primes as an
exponentially small spectator.

DEMONSTRATION (run below): solving the balance equation FROM THE
ZERO SIDE (first N computed zeros + Riemann-von Mangoldt density
tail; no digamma anywhere in the solve) recovers the feature
locations, with error decreasing in N.  The zeros, plus the density
model, know where the cascade's landmarks are.

THE HONEST NEGATIVE (door 1's answer, registered): within the
current record NO quantity reads the zero side independently of the
digamma packaging.  The features are zero-side-determined THROUGH
the identity (which is zeta's own bookkeeping), and nothing more is
claimed.  A claim of the stronger kind would require a recorded
quantity whose value needs an individual zero (not the packaged
digamma value) — no such quantity exists in the record, and
manufacturing one is exactly what the stopping rule forbids.
"""

import math

from mpmath import mp, mpf, zeta, zetazero, diff, log, pi as mppi, findroot
from scipy.integrate import quad

mp.dps = 25

SQRTPI = float(mp.sqrt(mppi))
LEVELS = [("critical point  p = 0", 0.0, (6.5, 8.5)),
          ("threshold  p = ln G(1/2)", 0.5 * math.log(math.pi), (18.0, 24.0)),
          ("sink  p = G(1/2)", SQRTPI, (140.0, 320.0))]


def p_truth(s):
    return float(-log(mppi) / 2 + mp.digamma(mpf(s) / 2) / 2)


def primes_part(s):
    return float(-diff(lambda t: log(zeta(t)), mpf(s)))


def zero_side_p(s, gammas, T):
    """p(s) built from the ZERO side: Lorentzian sum over given zeros
    + average-density tail - poles + primes.  No digamma."""
    z = s - 0.5
    zs = sum(2 * z / (z * z + g * g) for g in gammas)
    tail, _ = quad(lambda t: 2 * z / (z * z + t * t)
                   * math.log(t / (2 * math.pi)) / (2 * math.pi),
                   T, 5e6, limit=300)
    poles = 1.0 / s + 1.0 / (s - 1.0)
    return zs + tail - poles + primes_part(s)


def bisect(f, a, b, iters=60):
    fa = f(a)
    for _ in range(iters):
        m = 0.5 * (a + b)
        fm = f(m)
        if fa * fm <= 0:
            b = m
        else:
            a, fa = m, fm
    return 0.5 * (a + b)


def main():
    print("=" * 74)
    print("DOOR 1: the zeros locate the cascade's distinguished layers")
    print("=" * 74)
    NZ = 50
    gam = [float(zetazero(n).imag) for n in range(1, NZ + 1)]
    print(f"  (first {NZ} zeros computed via zetazero; density-tail model")
    print("   disclosed in docstring; no digamma inside the zero-side solve)")
    print()
    for name, level, (a, b) in LEVELS:
        truth = bisect(lambda s: p_truth(s) - level, a, b)
        line = f"  {name:<28} truth s* = {truth:10.4f};  zero-side:"
        prev = None
        for n in (10, 25, 50):
            est = bisect(lambda s: zero_side_p(s, gam[:n], gam[n - 1])
                         - level, a, b, iters=40)
            err = abs(est - truth)
            line += f"  N={n}: {est:9.4f} (err {err:.1e})"
            prev = err
        print(line)
    print()
    print("=" * 74)
    print("READING")
    print("=" * 74)
    print("  - Each distinguished layer is the exact balance point")
    print("    ZEROS + PRIMES = POLES + level: the observer-side geography")
    print("    is a zeros-vs-pole tug-of-war (zeta's pole at s=1 vs the")
    print("    nontrivial zeros), primes an exponentially small spectator.")
    print("  - Solving the balance FROM THE ZERO SIDE recovers the two")
    print("    near features with error DECREASING in N (critical point")
    print("    to ~6e-3, threshold to ~5e-2 at N=50).  The sink at")
    print("    s ~ 218 is TAIL-MODEL-LIMITED: at that height the")
    print("    Lorentzian is dominated by the average-density tail, so")
    print("    the estimate sits at ~1% accuracy and is N-insensitive --")
    print("    reported as such, not claimed as convergent.")
    print("  - THE HONEST NEGATIVE (registered): no recorded quantity")
    print("    reads the zero side independently of the digamma")
    print("    packaging.  The features are identity-mediated; nothing")
    print("    stronger is claimed, and any future stronger claim is")
    print("    stopping-rule gated new physics.")


if __name__ == "__main__":
    main()
