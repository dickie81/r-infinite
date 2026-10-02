"""Shared parameters: Zhu's one-stroke reduction at L = 1 (support 2), even sector."""
from flint import arb, acb, ctx
import os
CFG = os.environ.get("GAPCFG", "L1")
L_NUM = 1 if CFG == "L1" else None     # L = 1 (or 4/5 for the L = 0.8 validation run)
TS = 2496 if CFG == "L1" else 200     # T#, integer
N = 1850 if CFG == "L1" else 200      # Legendre orders 0, 2, ..., 2N-2 (odd: 1, ..., 2N-1)
PRIMEPOW = [(2, 2), (3, 3), (4, 2), (5, 5), (7, 7)] if CFG == "L1" else [(2, 2), (3, 3), (4, 2)]   # (n, p): Lambda(n) = log p, all n < e^(2L)
def consts():
    L = arb(1) if CFG == "L1" else arb(4) / 5
    cn = [(n, 2 * arb(p).log() / arb(n).sqrt()) for n, p in PRIMEPOW]
    AL = sum(c for _, c in cn)
    T = arb(TS)
    beta = (T / (2 * arb.pi())).log() - 1 / T - AL
    return L, cn, AL, T, beta
def panels():
    P = [(0, 0.5), (0.5, 1), (1, 2), (2, 4), (4, 8), (8, 16), (16, 32), (32, 64), (64, 128)]
    a = 128
    while a < TS:
        P.append((a, min(a + 64, TS))); a += 64
    assert P[-1][1] == TS
    return P
