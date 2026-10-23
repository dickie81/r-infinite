"""Gates on the cubic route's dual in the regime it needs (frequencies up to the modulus size), and on its theta
component.  Inputs, written by critical.py and theta.py (commands in CUBIC.md, section 6):
    critical_w.json   Z = 5000, 10^4, 2*10^4, 4*10^4, 8*10^4; H = Z^{3/4}, Z^{7/8}, Z/2, Z; every frequency k
    theta_w.json      Z = 10^4, 2*10^4, 4*10^4, 8*10^4; the same H; squarefree primary frequencies k

Gates (exit status 1 if any fails):
  C1  the cubic family's dual (mu G_3, cubic symbol) is at diagonal size: |S - diag|/diag <= 0.10 at every Z and H,
      and <= 0.02 for H >= Z^{7/8} at the largest Z
  C2  the sextic family's dual (mu G_6, sextic symbol): |S - diag|/diag <= 0.10 at every Z and H
  C3  without mu the excess at H = Z grows by 2^{1/3} per doubling of Z, to within 6%: Heath-Brown's (HZ)^{2/3}
      against the diagonal HZ
  C4  without mu the excess S - diag grows like H^{2/3} at fixed Z: log-log slope over the four H within 0.08 of 2/3
  T1  the excess is the cubic theta component c u(k) N(k)^{-1/6} m_w(k; Z): with u(k) = conj(G_3(k)) the fit removes at
      least 95% of the w = 1 excess at H = Z for every Z; each other candidate u removes at most 5%
  T2  c is one real constant: |Im c| <= 0.002, c(w = 1) and c(primes) within 0.01 of each other, spread over Z <= 0.01
  T3  after the component is removed, (S - diag)/diag <= 0.05 for w = 1, primes and the multiplicative sign 'mixed',
      at every Z and H (the remainder is at most diagonal size)
  T4  the Moebius rows contain the component with the Moebius mass m_mu(k; Z) = sum_{(n,k)=1} mu(n) N(n)^{-1/6}:
      the projection coefficient Re<X, T>/|X|^2, pooled over Z at H = Z with weights rows * |X|^2/diag, is within
      0.15 of 1 and more than 8 standard errors (1/sqrt(sum of weights)) from 0
  T5  the same for the multiplicative sign 'mixed' (a mass of order Z^{5/6} (log Z)^{-1/2}): projection within 0.10 of 1
      at every Z and H >= Z^{7/8}
  T6  the sextic family's dual, written over the cubic theta with its absorbed weight conj(c alpha G_2) chi2_n(k):
      pooled projection within 3 standard errors of 1 (the component exists there too; its mass is a Groessencharacter
      sum, CUBIC.md section 3)
"""
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f"[{'PASS' if ok else 'FAIL'}] {name}: {msg}")
        fails += 0 if ok else 1

    crit = json.load(open(os.path.join(HERE, 'critical_w.json')))['runs']
    th = json.load(open(os.path.join(HERE, 'theta_w.json')))['runs']

    print('critical_w.json: (S - diag)/diag')
    off = {}
    for r in crit:
        Z, Hs = r['Z'], r['H']
        for key, S in r['S'].items():
            dg = r['diag'][key.split('w=')[1]]
            off[(Z, key)] = [(s - g) / g for s, g in zip(S, dg)]
        print(f"  Z = {Z:6d} H = {Hs}: cubic mu " + ' '.join(f'{x:+.4f}' for x in off[(Z, 'd=3 w=mu')])
              + ' | sextic mu ' + ' '.join(f'{x:+.4f}' for x in off[(Z, 'd=6 w=mu')])
              + ' | cubic 1 ' + ' '.join(f'{x:+.3f}' for x in off[(Z, 'd=3 w=one')]))
    Zs = [r['Z'] for r in crit]
    c1 = max(abs(x) for Z in Zs for x in off[(Z, 'd=3 w=mu')])
    c1b = max(abs(x) for x in off[(Zs[-1], 'd=3 w=mu')][1:])
    gate('C1', c1 <= 0.10 and c1b <= 0.02, f'max |S - diag|/diag {c1:.4f}; at Z = {Zs[-1]}, H >= Z^(7/8): {c1b:.4f}')
    c2 = max(abs(x) for Z in Zs for x in off[(Z, 'd=6 w=mu')])
    gate('C2', c2 <= 0.10, f'max |S - diag|/diag {c2:.4f}')
    top = [off[(Z, 'd=3 w=one')][-1] for Z in Zs]
    growth = [top[j + 1] / top[j] for j in range(len(top) - 1)]
    gate('C3', all(abs(g / 2 ** (1 / 3) - 1) <= 0.06 for g in growth),
         'growth per doubling ' + ' '.join(f'{g:.3f}' for g in growth) + f' (2^(1/3) = {2 ** (1 / 3):.3f})')
    slopes = []
    for r in crit:
        E = [s - g for s, g in zip(r['S']['d=3 w=one'], r['diag']['one'])]
        slopes.append(float(np.polyfit(np.log(r['H']), np.log(E), 1)[0]))
    gate('C4', all(abs(s - 2 / 3) <= 0.08 for s in slopes), 'slopes ' + ' '.join(f'{s:.3f}' for s in slopes))

    print('theta_w.json: the component c conj(G_3(k)) N(k)^(-1/6) m_w(k; Z)')
    t1, t2c, t3, t5, pool = [], [], [], [], {'mu': [], 'sextic mu': []}
    for r in th:
        cand = r['candidates']
        t1.append((r['Z'], {k: v['explained'] for k, v in cand.items()}))
        c1, cp = complex(*cand['conj G3(k)']['c_one']), complex(*cand['conj G3(k)']['c_prime'])
        t2c.append((c1, cp))
        for wn in ('one', 'prime', 'mixed'):
            t3.append(max(r['weights'][wn]['after']))
        t5.extend(r['weights']['mixed']['projection'][1:])
        for wn in pool:
            x = r['weights'][wn]
            pool[wn].append((r['rows'][-1] * x['theta_over_diag'][-1], x['projection'][-1]))
        print(f"  Z = {r['Z']:6d}: c = {c1.real:.4f}{c1.imag:+.4f}i; mu projection "
              + ' '.join(f'{v:.3f}' for v in r['weights']['mu']['projection'])
              + ', component/diag ' + ' '.join(f'{v:.2e}' for v in r['weights']['mu']['theta_over_diag'])
              + '; sextic component/diag ' + ' '.join(f'{v:.2e}' for v in r['weights']['sextic mu']['theta_over_diag']))
    ok = all(e['conj G3(k)'] >= 0.95 and all(v <= 0.05 for k, v in e.items() if k != 'conj G3(k)') for _, e in t1)
    gate('T1', ok, '; '.join(f'Z = {Z}: ' + ', '.join(f'{k} {v:.3f}' for k, v in e.items()) for Z, e in t1))
    cs = [c.real for c, _ in t2c]
    ok = all(abs(c.imag) <= 0.002 and abs(c - cp) <= 0.01 for c, cp in t2c) and max(cs) - min(cs) <= 0.01
    gate('T2', ok, 'c = ' + ', '.join(f'{c.real:.4f} (primes {cp.real:.4f})' for c, cp in t2c))
    gate('T3', max(t3) <= 0.05, f'max (S - diag)/diag after removal {max(t3):+.4f}')
    res = {}
    for wn, pts in pool.items():
        wsum = sum(w for w, _ in pts)
        est = sum(w * p for w, p in pts) / wsum
        res[wn] = (est, 1 / math.sqrt(wsum))
    est, se = res['mu']
    gate('T4', abs(est - 1) <= 0.15 and est / se > 8, f'pooled projection {est:.3f} +- {se:.3f} ({est / se:.1f} standard errors from 0)')
    gate('T5', all(abs(p - 1) <= 0.10 for p in t5), 'projections ' + ' '.join(f'{p:.3f}' for p in t5))
    est6, se6 = res['sextic mu']
    gate('T6', abs(est6 - 1) <= 3 * se6, f'pooled projection {est6:.3f} +- {se6:.3f}')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
