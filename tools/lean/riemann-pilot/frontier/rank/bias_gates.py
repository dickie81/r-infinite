"""Gates on the bias computation (bias.py's output): the theta-function bias of Gauss sums, and its
absence for the Moebius weight that the order-N families' duals carry.

Inputs: bias_w_3e5.json (Z[w], orders 3 and 6) and bias_i_3e5.json (Z[i], orders 4 and 2), written by
    gcc -O2 -o periods periods.c -lm
    ./periods w 300000 > periods_w_3e5.txt     (about 4.5 min)
    ./periods i 300000 > periods_i_3e5.txt     (about 4.5 min)
    python3 bias.py w periods_w_3e5.txt 300000 300 bias_w_3e5.json
    python3 bias.py i periods_i_3e5.txt 300000 300 bias_i_3e5.json
T_w(k; Z) = sum_{N(n) <= Z} w(n) Gtilde_d(k; n) over the squarefree primary moduli n (coprime to 6 over
Z[w], to 1+i over Z[i]), for the weights w = 1 ('one'), the indicator of primes ('prime') and mu.
The mean squares are over the frequencies k with 0 < N(k) <= 300 (1074 over Z[w], 948 over Z[i]); the
random baseline is (number of k) * (number of moduli with N(n) <= Z).

Gates (exit status 1 if any fails):
  B1  Patterson-type bias: for d = 3 and d = 4, every frequency k with |T_one(k; X)| >= 4 sqrt(X) has a
      log-log slope over Z in [X/64, X] within 0.05 of 1/2 + 1/d (5/6 and 3/4)
  B2  no bias with mu: for d = 3, 4 and 6, |T_mu(k; X)| <= 2 sqrt(#moduli) for every k tested
  B3  the bias follows the weight's mass: at the untwisted frequencies (k = 1, and k = 8 resp. 16, which
      are cubes resp. fourth powers prime to every modulus), T_prime/T_one lies within 0.03 of
      mass(prime)/mass(one) in modulus and within 5 degrees in argument, and |T_mu/T_one| <= 0.1
  B4  the duals' mean squares with mu (d = 3, 4, 6) are within [0.5, 1.2] of the random baseline at
      Z = X/8, X/4, X/2, X
  B5  without mu the mean square's excess over the baseline grows by 2^{2/d} per doubling of Z (to within
      10%) over the last three doublings, for d = 3, 4 and 6: the square of the bias Z^{1/2+1/d}
"""
import cmath
import json
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))


def slope(grid, vals, lo):
    pts = [(math.log(z), math.log(abs(v))) for z, v in zip(grid, vals) if z >= lo and abs(v) > 0]
    xs, ys = zip(*pts)
    return float(np.polyfit(xs, ys, 1)[0])


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f"[{'PASS' if ok else 'FAIL'}] {name}: {msg}")
        fails += 0 if ok else 1

    R = {f: json.load(open(os.path.join(HERE, f'bias_{f}_3e5.json'))) for f in ('w', 'i')}
    orders = {'w': (3, 6), 'i': (4, 2)}
    b1, b2, b3, b4, b5 = [], [], [], [], []
    for f, r in R.items():
        X, grid, nmod = r['X'], r['grid'], r['moduli']
        print(f"Z[{f}]: X = {X}, {nmod} squarefree primary moduli; masses at X: "
              + ', '.join(f'{w} {round(v[-1])}' for w, v in r['mass'].items()))
        print(f"  {'sum':30s} {'slope':>6s} {'|T(X)|':>9s} {'|T|/sqrt X':>10s}")
        for key, vals in r['single'].items():
            v = [complex(*x) for x in vals]
            d = int(key.split()[0][2:])
            s = slope(grid, v, X / 64)
            print(f"  {key:30s} {s:6.3f} {abs(v[-1]):9.1f} {abs(v[-1]) / math.sqrt(X):10.3f}")
            if d in (3, 4) and key.split()[1] == 'w=one' and abs(v[-1]) >= 4 * math.sqrt(X):
                b1.append((key, s, abs(s - (0.5 + 1 / d)) <= 0.05))
            if d in (3, 4, 6) and key.split()[1] == 'w=mu':
                b2.append((key, abs(v[-1]), abs(v[-1]) <= 2 * math.sqrt(nmod)))
        mass = {w: v[-1] for w, v in r['mass'].items()}
        dmain = orders[f][0]
        for k in ('(1, 0)', '(8, 0)' if f == 'w' else '(16, 0)'):
            T1 = complex(*r['single'][f'd={dmain} w=one k={k}'][-1])
            Tp = complex(*r['single'][f'd={dmain} w=prime k={k}'][-1])
            Tm = complex(*r['single'][f'd={dmain} w=mu k={k}'][-1])
            q = Tp / T1
            ok = abs(abs(q) - mass['prime'] / mass['one']) <= 0.03 and abs(math.degrees(cmath.phase(q))) <= 5 \
                and abs(Tm / T1) <= 0.1
            b3.append((f, k, abs(q), mass['prime'] / mass['one'], math.degrees(cmath.phase(q)), abs(Tm / T1), ok))
        nk = r['nk']
        cnt = r['counts']
        print(f"  mean squares over {nk} frequencies, ratio to the random baseline:")
        for d in orders[f]:
            for w in ('mu', 'one'):
                ratios = [r['meansq'][f'd={d} w={w} Z={z}'] / (nk * cnt[str(z)]) for z in grid if z >= X / 8]
                print(f"    d={d} w={w:4s} " + '  '.join(f'{x:8.3f}' for x in ratios))
                if w == 'mu' and d in (3, 4, 6):
                    b4.append((f, d, ratios, all(0.5 <= x <= 1.2 for x in ratios)))
                if w == 'one' and d in (3, 4, 6):
                    growth = [ratios[j + 1] / ratios[j] for j in range(len(ratios) - 1)]
                    b5.append((f, d, growth, all(abs(g / 2 ** (2 / d) - 1) <= 0.10 for g in growth)))

    gate('B1', all(ok for _, _, ok in b1),
         f'{len(b1)} biased sums; slopes ' + ', '.join(f"{k.split()[0]} k={k.split(' k=')[1]}: {s:.3f}" for k, s, _ in b1))
    gate('B2', all(ok for _, _, ok in b2), f'{len(b2)} Moebius sums; max |T_mu| {max(t for _, t, _ in b2):.1f}')
    gate('B3', all(x[-1] for x in b3),
         '; '.join(f'Z[{f}] k={k}: |Tp/T1| {a:.3f} vs mass {m:.4f}, arg {g:.1f} deg, |Tmu/T1| {t:.3f}'
                   for f, k, a, m, g, t, _ in b3))
    gate('B4', all(x[-1] for x in b4),
         '; '.join(f'Z[{f}] d={d}: ' + ' '.join(f'{x:.2f}' for x in ratios) for f, d, ratios, _ in b4))
    gate('B5', all(x[-1] for x in b5),
         '; '.join(f'Z[{f}] d={d}: ' + ' '.join(f'{g:.3f}' for g in growth) + f' (2^(2/d) = {2 ** (2 / d):.3f})'
                   for f, d, growth, _ in b5))
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
