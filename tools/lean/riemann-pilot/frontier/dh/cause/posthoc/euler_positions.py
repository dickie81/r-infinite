#!/usr/bin/env python3
"""Post-hoc: positions, not only counts.  For every census zero rho with Re rho > 1/2 on (200, 10000], Newton's method
on g_X = c1 P_X + c2 (X = 1e5, the inert Euler product truncated at X) started at rho; prints how many starts converge
(step < 1e-10 and |g_X| < 1e-9; double precision over the X-prime sum floors the step near 1e-13), whether the limits
are distinct (no two census zeros mapped to one zero of g_X), and the distribution of |rho_X - rho|.
Usage: euler_positions.py [X]"""
import sys, json, math, os
import numpy as np
D = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
X = int(float(sys.argv[1])) if len(sys.argv) > 1 else 100_000
kappa = (math.sqrt(10 - 2*math.sqrt(5)) - 2)/(math.sqrt(5) - 1)
c1 = 0.5*(1 - 1j*kappa); c2 = 0.5*(1 + 1j*kappa)
def primes_upto(n):
    s = np.ones(n + 1, dtype=bool); s[:2] = False
    for i in range(2, int(n**0.5) + 1):
        if s[i]: s[i*i::i] = False
    return np.nonzero(s)[0]
pr = primes_upto(X); inert = pr[(pr % 5 == 2) | (pr % 5 == 3)]
chi = np.where(inert % 5 == 2, 1j, -1j); lp = np.log(inert.astype(float))
def g_and_dg(s):
    z = chi*np.exp(-s*lp)
    logP = np.sum(np.log1p(z) - np.log1p(-z))
    dlogP = np.sum(-2*z*lp/(1 - z*z))
    P = np.exp(logP)
    return c1*P + c2, c1*P*dlogP
off = []
for k in (1, 2, 3):
    for l in open(f'{D}/census/census_{k}.jsonl'):
        if l.strip():
            off += [complex(z[0], z[1]) for z in json.loads(l)['offline']]
off = sorted((z for z in off if 200 < z.imag <= 10000), key=lambda z: z.imag)
res = []
for rho in off:
    s = rho; ok = False
    for it in range(40):
        g, dg = g_and_dg(s)
        step = g/dg
        s = s - step
        if abs(step) < 1e-10:
            ok = abs(g_and_dg(s)[0]) < 1e-9; break
    res.append((rho, s, ok))
d = np.array([abs(s - rho) for rho, s, ok in res]); conv = sum(ok for *_, ok in res)
keys = [complex(round(s.real, 8), round(s.imag, 8)) for _, s, ok in res if ok]
print(f'X = {X}: {len(off)} census zeros with Re > 1/2 on (200, 10000]; Newton converged (step < 1e-10, |g| < 1e-9) '
      f'from {conv}; distinct limits {len(set(keys))}')
for lo in (0.5, 0.6, 0.7, 0.8):
    sel = np.array([rho.real >= lo for rho, *_ in res])
    print(f'  Re rho >= {lo}: n = {sel.sum()}  |rho_X - rho|: median {np.median(d[sel]):.2e}  90% {np.percentile(d[sel], 90):.2e}  '
          f'max {d[sel].max():.2e}')
worst = sorted(zip(d, [r for r, *_ in res]), key=lambda x: -x[0])[:5]
print('  largest moves: ' + '; '.join(f'{r.real:.4f}+{r.imag:.3f}i: {dd:.3f}' for dd, r in worst))
