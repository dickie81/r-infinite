"""Shared parameters for one node of the simplicity covering (round 47): Zhu's one-stroke reduction
(arXiv 2608.24827, Thm 1.1, valid for every L > 0 with beta* > 0) at support [-L, L], L = GAP_L (a rational
p/q), T# = GAP_T, N = GAP_N even Legendre modes.  Generalises frontier/gap_L1/params.py (L = 1 only)."""
from flint import arb, acb, ctx
import os, math
LP, LQ = map(int, os.environ["GAP_L"].split("/"))
TS = int(os.environ["GAP_T"])
N = int(os.environ["GAP_N"])
PREC = int(1.6 * LP / LQ * TS) + 600          # nodes / Bessel-recurrence working precision
def _primepow(X):
    out = []
    for n in range(2, int(X) + 1):
        p = next(q for q in range(2, n + 1) if n % q == 0)      # smallest prime factor
        m = n
        while m % p == 0: m //= p
        if m == 1: out.append((n, p))
    return out
# (n, p) with Lambda(n) = log p, all prime powers n with log n < 2L
PRIMEPOW = _primepow(math.exp(2 * LP / LQ) + 1)
PRIMEPOW = [(n, p) for n, p in PRIMEPOW if math.log(n) < 2 * LP / LQ]
def consts():
    L = arb(LP) / LQ
    cn = [(n, 2 * arb(p).log() / arb(n).sqrt()) for n, p in PRIMEPOW]
    AL = sum((c for _, c in cn), arb(0))
    T = arb(TS)
    beta = (T / (2 * arb.pi())).log() - 1 / T - AL
    assert beta > 0 and TS >= 4
    return L, cn, AL, T, beta
def panels():
    e = [0, 0.5, 1]
    while e[-1] < min(128, TS): e.append(min(2 * e[-1], TS))
    while e[-1] < TS: e.append(min(e[-1] + 64, TS))
    return list(zip(e[:-1], e[1:]))
