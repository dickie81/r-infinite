#!/usr/bin/env python3
"""Post-hoc: summary of the other-heights controls (euler_zeros_heights.py outputs in heights/) against the census
heights (euler_zeros.py chunks in chunks/; the census itself from census/).  For each control set: windows of length
9800, the mean, standard deviation and range of the counts of zeros of g_X with Re > sigma0, and where the census
window (200, 10000] falls."""
import json, glob, os, statistics as st
H = os.path.dirname(os.path.abspath(__file__))
D = os.path.dirname(H)
ch = [json.load(open(f)) for f in glob.glob(os.path.join(H, 'chunks', 'ez_*.json'))]
CH_SIG0 = {r['sigma0'] for r in ch[0]['rows']}
def census_heights(X, s0):
    return sum(x['N'] for c in ch for r in c['rows'] if r['sigma0'] == s0 for x in r['res'] if x['X'] == X)
off = []
for k in (1, 2, 3):
    for l in open(f'{D}/census/census_{k}.jsonl'):
        if l.strip():
            off += [(z[0], z[1]) for z in json.loads(l)['offline']]
SETS = [('X = 30, heights 1e6 + 1e4 k (k < 60)', 30, ['heights_X30.json']),
        ('X = 300, random heights in (1e5, 1e8)', 300, ['heights_X300.json']),
        ('X = 300, heights 1e4 k (k = 1..20)', 300, ['heights_X300_low.json']),
        ('X = 3000, random heights in (1e5, 1e8)', 3000, ['heights_X3000.json', 'heights_X3000b.json', 'heights_X3000c.json']),
        ('X = 3000, heights 1e4 k (k = 1..9)', 3000, ['heights_X3000_low1.json', 'heights_X3000_low2.json', 'heights_X3000_low3.json'])]
for name, X, files in SETS:
    rows = [r for f in files for r in json.load(open(os.path.join(H, 'heights', f)))]
    assert all(r['X'] == X and r['L'] == 9800 for r in rows)
    bad = sum(v for r in rows for k, v in r.items() if k.startswith('unres_'))
    fe = max(v for r in rows for k, v in r.items() if k.startswith('frac_err_'))
    print(f'{name}: {len(rows)} windows (unresolved refinements {bad}, largest winding error {fe:.1e})')
    for s0 in (0.7, 0.75, 0.8, 0.85):
        if str(s0) not in rows[0]:
            continue
        v = [r[str(s0)] for r in rows]; m = st.mean(v); sd = st.stdev(v)
        line = f'  Re > {s0}: mean {m:.2f}  sd {sd:.2f}  range {min(v)}-{max(v)}  (Poisson sd {m**0.5:.2f});  '
        if s0 not in CH_SIG0:
            print(line + 'census heights not counted at this sigma0 (euler_zeros.py: 0.6, 0.7, 0.8, 0.85)')
            continue
        c = census_heights(X, s0)
        print(line + f'census heights {c} (z = {(c - m)/sd:+.2f}; {sum(1 for x in v if x >= c)} of {len(v)} windows at or above)')
print('\ndh itself on (200, 10000] (the census): ' + ', '.join(
    f'Re > {s0}: {sum(1 for z in off if 200 < z[1] <= 10000 and z[0] > s0)}' for s0 in (0.7, 0.75, 0.8, 0.85)))
