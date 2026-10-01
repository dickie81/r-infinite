#!/usr/bin/env python3
"""Post-hoc: the tail of Im log R at sigma = 0.8 at the census heights vs the random model.
Im log R(s) is the continuous logarithm from Re s = +inf; for Re s > 1/2 it is the limit of
sum over inert p <= X of [log(1 + chi(p) p^-s) - log(1 - chi(p) p^-s)] (principal logs), and the X = 1e5 partial
sum is within about 0.02 of it at sigma = 0.8 (tail standard deviation).  Sample t uniformly (seed 2731) in each window,
compute the partial sums by prime ranges (p <= 30, 30 < p <= 1000, 1000 < p <= 1e5), and compare with the random model
(exact factors, independent uniform phases, same prime ranges): the tail probabilities of Im log R near the
targets -2.588 and 2 pi - 2.588 = 3.695, the fraction of samples with log R in the square of half-side 0.3 about log(-eps) (both branches), and the
correlations between the ranges.
Usage: argtail.py [sigma] [N]   (defaults 0.8 and 20000 per window; the round-273 run is argtail_08.log)"""
import math, sys
import numpy as np
kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1)
targ = math.atan2(-0.5257311121191336, -0.85065080835204)   # arg(-eps)
def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
pr = primes_upto(100_000); inert = pr[(pr % 5 == 2) | (pr % 5 == 3)]
chi = np.where(inert % 5 == 2, 1j, -1j); lp = np.log(inert.astype(float))
RANGES = [(0, 30), (30, 1000), (1000, 100_000)]
idx = [(int(np.searchsorted(inert, a, side='right')), int(np.searchsorted(inert, b, side='right'))) for a, b in RANGES]
SIG = float(sys.argv[1]) if len(sys.argv) > 1 else 0.8
N = int(sys.argv[2]) if len(sys.argv) > 2 else 20000
def parts_det(t):
    out = np.zeros((t.size, len(RANGES)), complex)
    for a in range(0, t.size, 400):
        tt = t[a:a + 400]
        for j, (i0, i1) in enumerate(idx):
            Z = chi[None, i0:i1]*np.exp(-SIG*lp[None, i0:i1] - 1j*np.outer(tt, lp[i0:i1]))
            out[a:a + 400, j] = np.sum(np.log1p(Z) - np.log1p(-Z), axis=1)
    return out
def parts_rand(n, rng):
    out = np.zeros((n, len(RANGES)), complex)
    for a in range(0, n, 400):
        m = min(400, n - a)
        for j, (i0, i1) in enumerate(idx):
            Z = chi[None, i0:i1]*np.exp(-SIG*lp[None, i0:i1] + 2j*np.pi*rng.random((m, i1 - i0)))
            out[a:a + m, j] = np.sum(np.log1p(Z) - np.log1p(-Z), axis=1)
    return out
def report(name, P):
    L = P.sum(axis=1); im = L.imag; re = L.real
    near = lambda c, w: np.mean((np.abs(im - c) < w) & (np.abs(re) < w))
    tl = np.mean(im < targ + 0.3); th_ = np.mean(im > targ + 2*np.pi - 0.3)
    C = np.corrcoef(np.vstack([P[:, j].imag for j in range(len(RANGES))]))
    print(f'{name:>22}: sd Im {im.std():.4f}  P(Im < {targ + 0.3:.3f}) {tl:.5f}  P(Im > {targ + 2*np.pi - 0.3:.3f}) {th_:.5f}  '
          f'P(near -eps, w=0.3) {near(targ, 0.3) + near(targ + 2*np.pi, 0.3):.5f}  '
          f'sd by range {" ".join(f"{P[:, j].imag.std():.3f}" for j in range(len(RANGES)))}  '
          f'corr(Im) 01 {C[0, 1]:+.3f} 02 {C[0, 2]:+.3f} 12 {C[1, 2]:+.3f}', flush=True)
rng = np.random.default_rng(2731)
for (a, b) in [(200, 2000), (2000, 5000), (5000, 10000)]:
    t = rng.uniform(a, b, N)
    report(f'census heights ({a},{b}]', parts_det(t))
report('random model', parts_rand(N*3, np.random.default_rng(27310)))
