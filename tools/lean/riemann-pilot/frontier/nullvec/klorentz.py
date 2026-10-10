#!/usr/bin/env python3
"""Round 170 (PREREG_lorentz.md): grid-point density on the hyperboloids x^2+y^2+z^2-t^2 = n of Z^{3,1}."""
import numpy as np, math, json
X = 2_000_000
sq = np.zeros(X + 1, dtype=np.int64); k = np.arange(0, math.isqrt(X) + 1); sq[k*k] += 2; sq[0] = 1
def conv(a, b):
    n = 1 << (2*X + 1).bit_length()
    c = np.fft.irfft(np.fft.rfft(a.astype(float), n)*np.fft.rfft(b.astype(float), n), n)[:X + 1]
    return np.rint(c).astype(np.int64)
r3 = conv(conv(sq, sq), sq)
def delta(n, T):
    t = np.arange(-T, T + 1); m = n + t*t; ok = m >= 0; m = m[ok]
    return r3[m].sum()/(2*math.pi*np.sqrt(m.astype(float)).sum())
chi = lambda d: 1 if d % 4 == 1 else -1 if d % 4 == 3 else 0
pred = lambda n: sum(chi(d)/d for d in range(1, abs(n) + 1) if abs(n) % d == 0)
res = {}
for T in (1000, 1400):
    res[T] = {n: delta(n, T) for n in list(range(-399, 400, 2))}
d1, dm1 = res[1400][1], res[1400][-1]
rows = []
for n in range(-399, 400, 2):
    base = d1 if n > 0 else dm1
    meas = res[1400][n]/base; err = abs(res[1400][n] - res[1000][n])/base
    rows.append((n, meas, pred(n), err))
dev = [abs(m - p) for _, m, p, _ in rows]; errs = [e for *_, e in rows]
print('delta(1)=%.5f delta(-1)=%.5f' % (d1, dm1))
print('L2: max |measured - predicted| = %.4f ; max T-spread = %.4f ; median dev %.4f' % (max(dev), max(errs), float(np.median(dev))))
for n, m, p, e in rows:
    if abs(n) in (1, 3, 5, 9, 13, 15, 21, 25, 45, 65, 105, 225, 399): print(n, round(m, 4), round(p, 4), round(e, 4))
# L1 multiplicativity on odd coprime pairs (positive n)
D = res[1400]; worst = 0; cnt = 0
for m in range(3, 60, 2):
    for n in range(m + 2, 60, 2):
        if math.gcd(m, n) == 1 and m*n <= 399:
            cnt += 1; worst = max(worst, abs(D[m*n]*d1 - D[m]*D[n])/d1**2)
print('L1: %d odd coprime pairs, max |d(mn)d(1)-d(m)d(n)|/d(1)^2 = %.4f' % (cnt, worst))
json.dump(dict(d1=d1, dm1=dm1, rows=rows, L1_pairs=cnt, L1_worst=worst), open('klorentz_results.json', 'w'))
