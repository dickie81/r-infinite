#!/usr/bin/env python3
"""
The cascade clock as a prime-generation process: do the Riemann zeros
appear as the spectrum of arithmetic novelty in cascade time?

The intuition under test (user conjecture, formalised): the cascade resolves
one dimension per tick; each resolved dimension d adds the integer d to the
available arithmetic -- a new prime when d is prime (rate 1/ln d), a new
multiplicative relation among existing primes when d is composite.  The
arithmetic-novelty content of tick d is the von Mangoldt function
Lambda(d) = ln p if d = p^k, else 0.  By the explicit formula, the Fourier
dual of this event stream is the Riemann zeros: the truncated sum

    S_D(t) = | sum_{d <= D} Lambda(d) d^(-1/2) e^(-i t ln d) |

peaks at t = gamma_n (the zeros' imaginary parts), with resolution improving
as D grows.  In cascade terms: the zeros are not eigenvalues of the layer
geometry (closed in Addenda 2-4) but the RESONANT FREQUENCIES OF THE
RESOLUTION PROCESS ITSELF, and a tower that has resolved D dimensions has
"heard" the zeros to a certain depth.

This is classical number theory recast on the cascade clock -- the point is
to quantify it: how many zeros does the PHYSICAL tower (D = 217, the layer
count at which the cascade's Omega floor is reached) actually resolve, and
how does the focus improve with D?

Controls: (i) the same weights placed at random tick positions (destroys
the arithmetic, keeps the statistics); (ii) peak contrast at true zeros vs
midpoints between zeros.
"""

import math

import numpy as np


def lambda_von_mangoldt(D):
    lam = np.zeros(D + 1)
    for p in range(2, D + 1):
        # p prime iff not marked; simple sieve
        pass
    sieve = np.ones(D + 1, dtype=bool)
    sieve[:2] = False
    for i in range(2, int(D ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = False
    primes = np.nonzero(sieve)[0]
    for p in primes:
        pk = p
        while pk <= D:
            lam[pk] = math.log(p)
            pk *= p
    return lam, primes


def spectrum(lam, tgrid):
    d = np.arange(2, len(lam))
    w = lam[2:] / np.sqrt(d)
    logs = np.log(d)
    # S(t) = |sum w * exp(-i t log d)|
    ph = np.exp(-1j * np.outer(tgrid, logs))
    return np.abs(ph @ w)


def peak_positions(t, S):
    idx = np.nonzero((S[1:-1] > S[:-2]) & (S[1:-1] > S[2:]))[0] + 1
    return t[idx], S[idx]


ZEROS = [14.134725, 21.022040, 25.010858, 30.424876, 32.935062,
         37.586178, 40.918719, 43.327073, 48.005151, 49.773832,
         52.970321, 56.446248]


def match_report(D, tmax=58.0, quiet=False):
    lam, primes = lambda_von_mangoldt(D)
    t = np.arange(2.0, tmax, 0.01)
    S = spectrum(lam, t)
    pt, ps = peak_positions(t, S)
    hits = []
    for g in ZEROS:
        if g > tmax - 1:
            continue
        j = int(np.argmin(np.abs(pt - g)))
        hits.append((g, pt[j], pt[j] - g))
    n_good = sum(1 for g, p, e in hits if abs(e) < 0.5)
    if not quiet:
        print(f"  D = {D}: {len(primes)} primes resolved;"
              f" zeros matched within 0.5: {n_good}/{len(hits)}")
        for g, p, e in hits:
            mark = "MATCH" if abs(e) < 0.5 else "  -  "
            print(f"    gamma = {g:9.4f}   nearest peak {p:9.4f}"
                  f"   err {e:+7.3f}   {mark}")
    # contrast: mean S at zeros vs at midpoints
    zin = [g for g in ZEROS if g < tmax - 1]
    mids = [(zin[i] + zin[i + 1]) / 2 for i in range(len(zin) - 1)]
    Sz = np.mean([S[int(np.argmin(np.abs(t - g)))] for g in zin])
    Sm = np.mean([S[int(np.argmin(np.abs(t - m)))] for m in mids])
    return n_good, len(hits), Sz / Sm, lam, t, S


def main():
    print("=" * 78)
    print("PART A: the arrival rate (correcting the intuition's bookkeeping)")
    print("=" * 78)
    lam, primes = lambda_von_mangoldt(217)
    print(f"  ticks 2..217: 216 integers resolved, {len(primes)} primes,"
          f" {int((lam > 0).sum())} prime-power events")
    print(f"  new-prime rate at d: 1/ln d = {1/math.log(217):.3f} per tick"
          f" at the tower top (one per ~{math.log(217):.1f} ticks)")
    print("  each composite tick adds a RELATION among existing primes;")
    print("  arithmetic novelty per tick = von Mangoldt Lambda(d)")

    print()
    print("=" * 78)
    print("PART B: spectrum of the physical tower (D = 217)")
    print("=" * 78)
    n_good, n_tot, contrast, lam, t, S = match_report(217)
    print(f"  peak contrast (mean S at zeros / at midpoints): {contrast:.2f}")

    print()
    print("=" * 78)
    print("PART C: zeros come into focus as dimensions resolve")
    print("=" * 78)
    print(f"{'D':>7}{'primes':>8}{'matched':>10}{'contrast':>10}")
    for D in (30, 60, 100, 217, 500, 1000, 5000):
        n_good, n_tot, contrast, *_ = match_report(D, quiet=True)
        _, primes = lambda_von_mangoldt(D)
        print(f"{D:>7}{len(primes):>8}{n_good:>7}/{n_tot}{contrast:>10.2f}")

    print()
    print("=" * 78)
    print("PART D: controls")
    print("=" * 78)
    rng = np.random.default_rng(20260719)
    lam217, _ = lambda_von_mangoldt(217)
    vals = lam217[lam217 > 0]
    fake = np.zeros_like(lam217)
    pos = rng.choice(np.arange(2, 218), size=len(vals), replace=False)
    fake[pos] = vals
    t = np.arange(2.0, 58.0, 0.01)
    Sf = spectrum(fake, t)
    zin = [g for g in ZEROS if g < 57]
    mids = [(zin[i] + zin[i + 1]) / 2 for i in range(len(zin) - 1)]
    Szf = np.mean([Sf[int(np.argmin(np.abs(t - g)))] for g in zin])
    Smf = np.mean([Sf[int(np.argmin(np.abs(t - m)))] for m in mids])
    print(f"  random-position control (same weights, shuffled ticks):")
    print(f"    contrast at true zeros: {Szf / Smf:.2f}   (real stream:"
          f" {match_report(217, quiet=True)[2]:.2f})")
    # shifted-grid control on the real stream
    S217 = spectrum(lam217, t)
    sh = [g + 1.5 for g in zin[:-1]]
    Sz = np.mean([S217[int(np.argmin(np.abs(t - g)))] for g in zin])
    Ss = np.mean([S217[int(np.argmin(np.abs(t - g)))] for g in sh])
    print(f"  shifted-grid control (zeros + 1.5): S(zeros)/S(shifted)"
          f" = {Sz / Ss:.2f}")


if __name__ == "__main__":
    main()
