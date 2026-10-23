"""evalparts_probe.py: how far would keeping the evaluable parts of the dropped terms move the sieve route on the
curve `g7c`? (SIEVE-ROUTE.md §23, "What would move the limits"; README round 577's Monte Carlo; round 703.)
An estimate, not a certificate.

The certificate (`route_limits.replay`, `external/pnt/SieveCertDefs.lean`) drops a depth-2 term `S(A_{p1p2}, p2)`, or a
depth-4 term `S(A_{p1p2p3p4}, p4)`, at the cost of its whole `B`-share, `(1/∏α)·ω(μ/a)/a`, with `μ` the exponent of the
rough part `m` and `a` the last prime's exponent. Split `m` by its factorization into primes, all at least `x^a`: the
share is the sum over the factorizations, and a factorization in which some subset sum of all the prime exponents of
`n` lies in `U = (u₁, u₂) ∪ (1 − u₂, 1 − u₁)` is a Type II sum in that grouping (SIEVE-ROUTE.md §6), which the probe
keeps; it drops the non-evaluable part. The exponents of `n` sum to `1` and `U` is symmetric under `x ↦ 1 − x`, so it
suffices to test the subset sums of the exponents other than the largest prime of `m`. A factorization with one prime
in `m` is never evaluable (its subset sums are those of the dropped term, or their complements).

`ω(μ/a)/a = 1/μ + ∫_a^{μ/2} (dβ/β)·ω((μ − β)/β)/β` (`m` prime, or `x^β` its least prime), so the non-evaluable part is
estimated by a random recursion: `β` uniform on `[a, μ/2]` with the weight `(μ/2 − a)/β`; with `k ≤ K` the rough part's
factorizations of more than `K` primes all count as non-evaluable.

The loss is a midpoint sum on the grid of `route_limits.replay` (`n₂` cells a side for `(α₁, α₂)`, `n₃` for `α₃` and
`α₄`) with its rules: a depth-2 term is a candidate when `α₂ < α₁ < 1/2`, `α₁ + 2α₂ ≤ 1`, `α₁ ∉ (u₁, u₂)` and it is
not evaluable; it may be decomposed when `α₁ + α₂ < 1 − u₁` and `α₁ + α₂ + α₃ < 1 − u₁` for every non-evaluable `α₃`;
and it costs the smaller of its share and its depth-4 cost. `ω` is Buchstab's (a trapezoid table), or the
certificate's crude bound (`0` below `1`, `1/u` on `[1, 2)`, `0.5672` above).

Rows printed for each `L`: the crude bound (the certificate's integrand), true `ω`, and true `ω` with the evaluable
parts kept for `k ≤ 2`, `k ≤ 3` and every `k`. The windows are `route_limits.window`'s sampled scan for `g7c`.

Gate: at `L = 9/4` the crude row lies within 3% of `a`, the extrapolation of `route_limits.jsonl`'s replays at `9/4`
(`route_limits.fits`), and the rows decrease in the order printed. Exits 1 otherwise.

Usage: evalparts_probe.py [L ...]   (default 9/4 2245/1000 224/100 2235/1000 223/100), n₂ = 200, n₃ = 100, seed 7.
"""
import json
import os
import sys
import time
from fractions import Fraction as Fr

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import route_limits as rl  # noqa: E402

N2, N3, SEED = 200, 100, 7
TOP = 0.5672

# Buchstab's omega on [1, 20]: 1/u on [1, 2]; (u omega)' = omega(u - 1), trapezoid with step DU
DU = 1e-4
NU = int(round(19 / DU)) + 1
UG = 1 + DU * np.arange(NU)
OM = np.zeros(NU)
_K2 = int(round(1 / DU))
OM[:_K2 + 1] = 1 / UG[:_K2 + 1]
_F = 1.0
for _i in range(_K2 + 1, NU):
    _F += DU * 0.5 * (OM[_i - 1 - _K2] + OM[_i - _K2])
    OM[_i] = _F / UG[_i]


def omega(u):
    u = np.asarray(u, dtype=float)
    return np.where(u < 1, 0.0, np.interp(u, UG, OM))


def omega_crude(u):
    u = np.asarray(u, dtype=float)
    return np.where(u < 1, 0.0, np.where(u < 2, 1 / np.maximum(u, 1), TOP))


class Probe:
    def __init__(self, u1, u2, rng):
        self.u1, self.u2, self.rng = u1, u2, rng
        self.v = u2 - u1

    def inU(self, s):
        u1, u2 = self.u1, self.u2
        return ((s > u1) & (s < u2)) | ((s > 1 - u2) & (s < 1 - u1))

    def evaluable(self, cols):
        sums = [np.zeros_like(cols[0])]
        for c in cols:
            sums = sums + [s + c for s in sums]
        ev = np.zeros(cols[0].shape, bool)
        for s in sums[1:]:
            ev |= self.inU(s)
        return ev

    def noneval(self, base, mu, a, ns, kmax):
        """The non-evaluable part of omega(mu/a)/a, per row of `base` (the exponents fixed so far)."""
        P = base.shape[0]
        S = np.repeat(base, ns, axis=0)
        m = np.repeat(mu, ns)
        aa = np.repeat(a, ns)
        w = np.ones(P * ns)
        alive = np.ones(P * ns, bool)
        sums = [np.zeros(P * ns)]
        for j in range(S.shape[1]):
            sums = sums + [s + S[:, j] for s in sums]
        ev = np.zeros(P * ns, bool)
        for s in sums[1:]:
            ev |= self.inU(s)
        acc = np.zeros(P * ns)
        for lev in range(12):
            evk = ev if (kmax == 0 or lev + 1 <= kmax) else np.zeros_like(ev)
            acc += np.where(alive & ~evk, w / m, 0.0)
            can = alive & (m / 2 >= aa)
            if not can.any():
                break
            beta = aa + self.rng.random(P * ns) * np.maximum(m / 2 - aa, 0)
            w = np.where(can, w * (m / 2 - aa) / beta, 0.0)
            new = [s + beta for s in sums]
            for s in new:
                ev |= can & self.inU(s)
            sums = sums + new
            m = np.where(can, m - beta, m)
            aa = np.where(can, beta, aa)
            alive = can
        return acc.reshape(P, ns).mean(axis=1)

    def loss(self, omf, kmax=None):
        """kmax None: no parts kept; 0: every k; K: factorizations of at most K primes in m."""
        v, u1, u2 = self.v, self.u1, self.u2
        h = (0.5 - v) / N2
        al = v + h * (np.arange(N2) + 0.5)
        A1, A2 = np.meshgrid(al, al, indexing="ij")
        A1, A2 = A1.ravel(), A2.ravel()
        ok = (A2 < A1) & (A1 < 0.5) & (A1 + 2 * A2 <= 1) & ~((A1 > u1) & (A1 < u2))
        ok &= ~self.evaluable([A1, A2])
        A1, A2 = A1[ok], A2[ok]
        mu2 = 1 - A1 - A2
        if kmax is None:
            g2 = omf(mu2 / A2) / A2
        else:
            g2 = np.concatenate([self.noneval(np.stack([A1[i:i + 400], A2[i:i + 400]], 1), mu2[i:i + 400],
                                              A2[i:i + 400], 64, kmax) for i in range(0, len(A1), 400)])
        b2 = g2 / (A1 * A2) * h * h
        lim = 1 - u1
        h3 = (0.5 - v) / N3
        a3g = v + h3 * (np.arange(N3) + 0.5)
        total = 0.0
        for i in range(len(A1)):
            a1, a2 = A1[i], A2[i]
            a3 = a3g[(a3g < a2) & (a1 + a2 + 2 * a3g <= 1)]
            a3 = a3[~self.evaluable([np.full(a3.shape, a1), np.full(a3.shape, a2), a3])]
            if not (a1 + a2 < lim and np.all(a1 + a2 + a3 < lim)):
                total += b2[i]
                continue
            X3, X4 = np.meshgrid(a3, a3g, indexing="ij")
            X3, X4 = X3.ravel(), X4.ravel()
            sel = (X4 <= X3) & (a1 + a2 + X3 + 2 * X4 <= 1)
            X3, X4 = X3[sel], X4[sel]
            ne = ~self.evaluable([np.full(X3.shape, a1), np.full(X3.shape, a2), X3, X4])
            X3, X4 = X3[ne], X4[ne]
            ref = 0.0
            if len(X3):
                mu4 = 1 - a1 - a2 - X3 - X4
                if kmax is None:
                    g4 = omf(mu4 / X4) / X4
                else:
                    g4 = self.noneval(np.stack([np.full(X3.shape, a1), np.full(X3.shape, a2), X3, X4], 1), mu4, X4,
                                      1, kmax)
                ref = float(np.sum(g4 / (X3 * X4)) * h3 * h3 / (a1 * a2) * h * h)
            total += min(ref, b2[i])
        return total


def main():
    Ls = [Fr(s) for s in sys.argv[1:]] or [Fr(9, 4), Fr(2245, 1000), Fr(224, 100), Fr(2235, 1000), Fr(223, 100)]
    pieces = rl.parse('g7c')
    rows = [r for r in rl.rows_of(os.path.join(HERE, 'route_limits.jsonl')) if r['curve'] == 'g7c']
    fitted = {d['L']: d['a'] for d in rl.fits(rows)[0] if d['curve'] == 'g7c' and 'a' in d}
    bad = 0
    print(f"evalparts_probe: g7c, n2 = {N2}, n3 = {N3}, seed {SEED}; midpoint estimates of the loss (not certificates)")
    print("  L          window (1e-5)    crude    true     k<=2     k<=3     all k")
    for L in Ls:
        w1, w2 = rl.window(pieces, L)
        u1, u2 = round(float(w1) * 1e5) / 1e5, round(float(w2) * 1e5) / 1e5
        rng = np.random.default_rng(SEED)
        p = Probe(u1, u2, rng)
        vals = [p.loss(omega_crude), p.loss(omega), p.loss(omega, 2), p.loss(omega, 3), p.loss(omega, 0)]
        print(f"  {str(L):10s} [{round(u1 * 1e5)}, {round(u2 * 1e5)}]   " + "  ".join(f"{x:.4f}" for x in vals),
              flush=True)
        if any(vals[i + 1] > vals[i] + 1e-9 for i in range(len(vals) - 1)):
            print("  FAIL: the rows do not decrease in the order printed")
            bad += 1
        if L == Fr(9, 4):
            ref = fitted[Fr(9, 4)]
            print(f"  gate: the crude row at 9/4 against route_limits' extrapolation a = {ref:.4f}: "
                  f"{(vals[0] - ref) / ref:+.2%}")
            if abs(vals[0] - ref) > 0.03 * ref:
                print("  FAIL: not within 3%")
                bad += 1
    print("EVALPARTS", "PASS" if bad == 0 else f"FAIL ({bad})")
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
