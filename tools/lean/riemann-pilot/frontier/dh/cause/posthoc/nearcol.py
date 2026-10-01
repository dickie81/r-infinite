#!/usr/bin/env python3
"""Post-hoc: the near-collision statistic, like for like.  For a height h, a(h) and b(h) are the on-line zeros of
L(1/2 + it, chi) and of L(1/2 + it, chibar) nearest to h, and the statistic is |a(h) - b(h)|/lambda(h),
lambda(h) = 2 pi/log(5h/2pi) (posthoc_beats.py's statistic at the off-line zeros).  Its median over three sets of
heights in (200, 10000]: the off-line zeros of dh, the on-line zeros of dh, and 20000 uniform heights (numpy seed 2733).
Usage: nearcol.py"""
import json, math, os, bisect, statistics
import numpy as np
D = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
files = [D + '/instrument/val_1_200.jsonl'] + [f'{D}/census/census_{k}.jsonl' for k in (1, 2, 3)]
W = [json.loads(l) for f in files for l in open(f) if l.strip()]
A = sorted(r for w in W for r in w['roots_chi']); B = sorted(r for w in W for r in w['roots_chibar'])
F = sorted(r for w in W for r in w['roots_f']); off = sorted(z[1] for w in W for z in w['offline'])
lam = lambda t: 2*math.pi/math.log(5*t/(2*math.pi))
def nearest(L, h):
    i = bisect.bisect_left(L, h)
    return min((L[j] for j in (i - 1, i) if 0 <= j < len(L)), key=lambda x: abs(x - h))
def stat(hs):
    return [abs(nearest(A, h) - nearest(B, h))/lam(h) for h in hs if 200 < h <= 10000]
rng = np.random.default_rng(2733)
for name, hs in (('off-line zeros of dh', off), ('on-line zeros of dh', F), ('uniform heights', rng.uniform(200, 10000, 20000))):
    v = stat(hs)
    print(f'{name:>22}: n = {len(v):5d}  median {statistics.median(v):.3f}  quartiles {np.percentile(v, 25):.3f} {np.percentile(v, 75):.3f}')
