"""Round 182: the lumpy ball. For the lattice ball Z^d, the number of teeth r_d(n) on shell |x|^2 = n,
divided by the smooth (round-sphere) expectation, is its lumpiness. Test: is the lumpiness exactly a product
over primes of local factors (Siegel's singular series)? Classical expectation: yes for d <= 8 (Z^d is alone
in its genus), no from d = 9 (a second lattice, E8+Z, joins the genus; a cusp form appears)."""
import json, math
import numpy as np
from sympy import primerange

NMAX, P = 40, 400

def r_counts(d):
    th = np.zeros(NMAX + 1, dtype=object); th[0] = 1
    for k in range(1, int(NMAX**0.5) + 1): th[k*k] += 2
    out = np.zeros(NMAX + 1, dtype=object); out[0] = 1
    for _ in range(d):
        new = np.zeros(NMAX + 1, dtype=object)
        for i in range(NMAX + 1):
            if out[i]: new[i:] += out[i] * th[:NMAX + 1 - i]
        out = new
    return [int(v) for v in out]

def local_density(d, n, p):
    v = 0; m = n
    while m % p == 0: m //= p; v += 1
    k = v + (3 if p == 2 else 1); mod = p**k
    sq = np.zeros(mod, dtype=np.float64)
    for x in range(mod): sq[x * x % mod] += 1
    acc = np.zeros(mod); acc[0] = 1
    for _ in range(d):
        acc = np.real(np.fft.ifft(np.fft.fft(acc) * np.fft.fft(sq)))
    return acc[n % mod] / mod**(d - 1)

def smooth(d, n): return math.pi**(d / 2) / math.gamma(d / 2) * n**(d / 2 - 1)

res = {}
for d in range(4, 11):
    r = r_counts(d); rows = []
    for n in range(1, NMAX + 1):
        S = 1.0
        for p in primerange(2, P): S *= local_density(d, n, p)
        rows.append((n, r[n], smooth(d, n) * S))
    rel = [abs(a - b) / a for _, a, b in rows]
    res[d] = dict(max_rel_err=max(rel), worst_n=rows[int(np.argmax(rel))][0],
                  sample=[(n, a, round(b, 3)) for n, a, b in rows[:6]])
    print(d, f"max rel err {max(rel):.2e}", "worst n", res[d]["worst_n"], res[d]["sample"][:4])
json.dump(res, open("klumpy_results.json", "w"), indent=1)
