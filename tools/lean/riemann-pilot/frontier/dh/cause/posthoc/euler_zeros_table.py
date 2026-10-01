#!/usr/bin/env python3
"""Post-hoc: aggregate euler_zeros.py's chunk counts into the three P3 windows and print them beside the census
(the true function) and the random model at the same cutoff X (model/model_rate_N*_X*.json; rate x window length).
Usage: euler_zeros_table.py chunk_dir"""
import sys, json, glob, os, math
D = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))     # frontier/dh/cause
WINDOWS = [(200, 2000), (2000, 5000), (5000, 10000)]
chunks = [json.load(open(f)) for f in glob.glob(os.path.join(sys.argv[1], 'ez_*.json'))]
cover = sorted((c['T1'], c['T2']) for c in chunks)
assert cover[0][0] == 200 and cover[-1][1] == 10000 and all(a[1] == b[0] for a, b in zip(cover, cover[1:])), cover
XS = chunks[0]['XS']; SIG0 = [r['sigma0'] for r in chunks[0]['rows']]
worst = max(x['frac_err'] for c in chunks for r in c['rows'] for x in r['res'])
unres = sum(r['stats']['unresolved'] for c in chunks for r in c['rows'])
print(f'{len(chunks)} chunks covering (200, 10000]; unresolved refinements {unres}; largest distance of a winding '
      f'from an integer {worst:.1e} (automatic for a closed polygon, not a check; see grid_check.py)')
off = []
for k in (1, 2, 3):
    for l in open(f'{D}/census/census_{k}.jsonl'):
        if l.strip():
            off += [(z[0], z[1]) for z in json.loads(l)['offline']]
model = {}
for f in glob.glob(f'{D}/model/model_rate_N*_X*.json'):
    d = json.load(open(f)); X = d['X']
    model[float('inf') if X == 'inf' else float(X)] = {round(r['sigma'], 3): r['rate'] for r in d['rows']}
for s0 in SIG0:
    print(f'\nRe rho > {s0}:')
    print('  window          census | ' + ' '.join(f'{("X=%g" % X):>13}' for X in XS))
    for (a, b) in WINDOWS:
        cen = sum(1 for z in off if a < z[1] <= b and z[0] > s0)
        det = [sum(x['N'] for c in chunks if a <= c['T1'] and c['T2'] <= b
                   for r in c['rows'] if r['sigma0'] == s0 for x in r['res'] if x['X'] == X) for X in XS]
        mod = [model.get(float(X), {}).get(round(s0, 3)) for X in XS]
        cells = [f'{n:>5} ({"%5.1f" % (m*(b - a)) if m is not None else "  -  "})' for n, m in zip(det, mod)]
        print(f'  ({a},{b}]{"":>{12 - len(str(a)) - len(str(b))}}{cen:>5} | ' + ' '.join(f'{c:>13}' for c in cells))
    tot_c = sum(1 for z in off if 200 < z[1] <= 10000 and z[0] > s0)
    tot_d = [sum(x['N'] for c in chunks for r in c['rows'] if r['sigma0'] == s0 for x in r['res'] if x['X'] == X) for X in XS]
    tot_m = [model.get(float(X), {}).get(round(s0, 3)) for X in XS]
    print(f'  (200,10000]   {tot_c:>5} | ' + ' '.join(f'{f"{n:>5} ({m*9800:5.1f})" if m is not None else f"{n:>5} (  -  )":>13}'
                                                    for n, m in zip(tot_d, tot_m)))
inf = model[float('inf')]
print('\nrandom model at X = inf (rate x 9800): ' + ', '.join(f'Re > {s0}: {inf[round(s0, 3)]*9800:.1f}' for s0 in SIG0))
print('(cells: the deterministic count at the census heights and, in brackets, the random model at the same X, '
      'rate x window length; model/ has no file at X = 100000, so that column shows "-")')
