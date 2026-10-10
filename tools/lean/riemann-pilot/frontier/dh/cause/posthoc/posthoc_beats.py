#!/usr/bin/env python3
"""Post-hoc (not pre-registered) analysis of PREREG P2(d)'s converse failure: are the zero-free same-type beats
without a nearby off-line zero compensated by a nearby overshoot (a same-type beat with two on-line zeros, or a
mixed beat with three)?  Re-uses score_cause.py's beat construction (same midpoint sign evaluations)."""
import sys, json, math, importlib.util
import os
D = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))     # frontier/dh/cause
files = [D + '/instrument/val_1_200.jsonl'] + [f'{D}/census/census_{k}.jsonl' for k in (1, 2, 3)]
W = sorted((json.loads(l) for f in files for l in open(f) if l.strip()), key=lambda w: w['T0'])
F = sorted(r for w in W for r in w['roots_f']); A = sorted(r for w in W for r in w['roots_chi'])
B = sorted(r for w in W for r in w['roots_chibar']); off = sorted((z[0], z[1]) for w in W for z in w['offline'])
src = open(D + '/score_cause.py').read().split("W = []")[0]    # take only the evaluator zz() and constants
sys.argv = ['x', 'dummy']; ns = {}
exec(src.replace("A_ = ap.parse_args()", "A_ = ap.parse_args(['dummy'])"), ns)
zz = ns['zz']
ev = sorted([(t, 'A') for t in A] + [(t, 'B') for t in B])
beats = []
for i in range(len(ev) - 1):
    (t0, k0), (t1, k1) = ev[i], ev[i + 1]
    zc, zb = zz((t0 + t1)/2)
    if (zc*zb) < 0:
        nf = sum(1 for r in F if t0 < r < t1)
        beats.append(((t0 + t1)/2, 'mixed' if k0 != k1 else 'same', nf, t0, t1))
lam = lambda t: 2*math.pi/math.log(5*t/(2*math.pi))
inr = lambda t: 200 < t <= 10000
same0 = [b for b in beats if b[1] == 'same' and b[2] == 0 and inr(b[0])]
over = [b for b in beats if inr(b[0]) and ((b[1] == 'same' and b[2] == 2) or (b[1] == 'mixed' and b[2] == 3))]
unmatched = [b for b in same0 if not any(abs(z[1] - b[0]) <= 2*lam(b[0]) for z in off)]
comp = [b for b in unmatched if any(abs(o[0] - b[0]) <= 2*lam(b[0]) for o in over)]
print(f"zero-free same-type beats: {len(same0)};  without an off-line zero within 2 lambda: {len(unmatched)};"
      f"  of those with an overshoot beat within 2 lambda: {len(comp)}")
print(f"overshoot beats: {len(over)} (same-type with 2 zeros: {sum(1 for o in over if o[1]=='same')}, mixed with 3: {sum(1 for o in over if o[1]=='mixed')})")
# the near-collision law: each off-line zero vs the nearest chi / chibar zero pair
dists = []
for s, g in off:
    if not inr(g): continue
    a = min(A, key=lambda x: abs(x - g)); b = min(B, key=lambda x: abs(x - g))
    dists.append((abs(a - b)/lam(g), s - 0.5))
import statistics
print(f"off-line zeros: {len(dists)}; nearest chi/chibar zero separation in units of lambda: median {statistics.median(d for d, _ in dists):.3f}, "
      f"90% below {sorted(d for d, _ in dists)[int(0.9*len(dists))]:.3f}")
# baseline: separation between each chi zero and its nearest chibar zero
base = [min(abs(a - b) for b in B[max(0, i - 3):i + 3])/lam(a) for i, a in enumerate(A) if inr(a)]
print(f"baseline (every chi zero): median {statistics.median(base):.3f}")
