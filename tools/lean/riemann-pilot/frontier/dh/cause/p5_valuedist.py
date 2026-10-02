#!/usr/bin/env python3
"""PREREG P5's fourth item (pre-registered, exploratory, no thresholds): the stationarity in height of the value
distribution of log|R(0.7 + it)|, R = L(s,chi)/L(s,chibar), over the three P3 windows, against the random model.
sigma = 0.8 is added (beyond the pre-registration; labelled).  t is sampled uniformly in each window (numpy seed 273,
N per window); R = (A + iB)/(A - iB) with A = zeta(s,1/5) - zeta(s,4/5), B = zeta(s,2/5) - zeta(s,3/5) (python-flint,
53 bits; the census instrument's evaluator, whose ball radii at these heights are below 1e-10).  The random model is
model/model_rate.py's: exact factors for the inert primes p <= 500 with independent uniform phases, the inert primes
in (500, X] as a complex Gaussian with their exact variance; X = inf, and X = 30, 100, 1000 for comparison.
Printed per window and sigma: mean and standard deviation of log|R|, its 5/25/50/75/95% quantiles, the two-sample
Kolmogorov-Smirnov distance to each other window and to the model samples.
Usage: p5_valuedist.py [N]   (default 6000 per window; about 4 minutes on one core)"""
import sys, math
import numpy as np
from flint import acb, ctx
from scipy.special import exp1
from scipy.stats import ks_2samp

N = int(sys.argv[1]) if len(sys.argv) > 1 else 6000
WINDOWS = [(200, 2000), (2000, 5000), (5000, 10000)]
SIGMAS = [0.7, 0.8]
ctx.prec = 53
AV = [acb(a)/5 for a in (1, 2, 3, 4)]
I = acb(0, 1)

def logabsR(sig, t):
    s = acb(sig, t)
    h = [acb.zeta(s, a) for a in AV]
    A, B = h[0] - h[3], h[1] - h[2]
    return math.log(abs(complex(A + I*B))) - math.log(abs(complex(A - I*B)))

def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
Y = 20_000_000
pr = primes_upto(Y); inert = pr[(pr % 5 == 2) | (pr % 5 == 3)].astype(float)
ex = inert[inert <= 500]; tail = inert[inert > 500]

def model_logabs(sig, X, n, rng):
    x = ex[ex <= X]**(-sig)
    tp = tail[tail <= X] if math.isfinite(X) else tail
    S0 = float(np.sum(tp**(-2*sig)))
    if not math.isfinite(X):
        S0 += 0.5*exp1((2*sig - 1)*math.log(Y))      # inert primes beyond Y, density 1/(2 log u)
    th = rng.random((n, x.size))*2*np.pi
    Vx = np.exp(1j*th)*x
    lr = np.sum(np.log1p(Vx) - np.log1p(-Vx), axis=1)
    z = (rng.standard_normal(n) + 1j*rng.standard_normal(n))/math.sqrt(2)
    return np.real(lr + 2*math.sqrt(S0)*z)

rng = np.random.default_rng(273)
ts = {w: np.sort(rng.uniform(w[0], w[1], N)) for w in WINDOWS}
mrng = np.random.default_rng(2730)
qs = [5, 25, 50, 75, 95]
for sig in SIGMAS:
    tag = '' if sig == 0.7 else '   [beyond the pre-registration]'
    print(f'\nsigma = {sig}{tag}', flush=True)
    vals = {w: np.array([logabsR(sig, t) for t in ts[w]]) for w in WINDOWS}
    models = {X: model_logabs(sig, X, 200_000, mrng) for X in (30, 100, 1000, math.inf)}
    for w in WINDOWS:
        v = vals[w]
        print(f'  window {w}: N = {v.size}  mean {v.mean():+.4f}  sd {v.std(ddof=1):.4f}  quantiles '
              + ' '.join(f'{np.percentile(v, q):+.3f}' for q in qs), flush=True)
    for X, m in models.items():
        print(f'  model X = {X}: mean {m.mean():+.4f}  sd {m.std(ddof=1):.4f}  quantiles '
              + ' '.join(f'{np.percentile(m, q):+.3f}' for q in qs))
    for i, w in enumerate(WINDOWS):
        for w2 in WINDOWS[i + 1:]:
            r = ks_2samp(vals[w], vals[w2])
            print(f'  KS {w} vs {w2}: D = {r.statistic:.4f}  p = {r.pvalue:.3g}')
    for w in WINDOWS:
        print(f'  KS {w} vs model: ' + '  '.join(f'X={X}: D = {ks_2samp(vals[w], m).statistic:.4f}'
                                               for X, m in models.items()))
