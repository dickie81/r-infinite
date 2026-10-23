"""Round 188: angular grinding. Gaussian primes (the 2D ball's wheels) as points on circles:
does their angle spread evenly, and how big is the angular drift?
A_k(X) = sum over Gaussian primes pi with N(pi) <= X of log N(pi) * cos(4 k arg pi)  (units removed by 4k).
k = 0 is the ordinary prime drift (psi - X); k >= 1 is the angular drift, governed by Hecke L(s, xi^k)."""
import json, math
import numpy as np

X = 10**8
lim = int(X**0.5) + 1
sieve = np.ones(X + 1, bool); sieve[:2] = False
for i in range(2, int(X**0.5) + 1):
    if sieve[i]: sieve[i*i::i] = False
norms, angs = [], []
for a in range(1, lim):
    b = np.arange(0, a + 1)            # first octant: 0 <= b <= a
    n = a * a + b * b
    ok = (n <= X)
    b, n = b[ok], n[ok]
    pr = sieve[n]
    for bb, nn in zip(b[pr], n[pr]):
        if nn == 2:
            norms.append(2); angs.append(math.pi / 4)           # 1+i
        elif bb == 0:
            continue                                          # a prime a with b=0 is not Gaussian-prime unless a=3 mod 4 (handled below)
        elif bb == a:
            continue
        else:
            th = math.atan2(bb, a)
            norms += [nn, nn]; angs += [th, -th]               # pi and its conjugate
# inert primes p = 3 mod 4: Gaussian prime p, norm p^2, angle 0
P = np.nonzero(sieve[:lim + 1])[0]
for p in P[P % 4 == 3]:
    if p * p <= X: norms.append(int(p * p)); angs.append(0.0)
norms = np.array(norms, dtype=np.int64); angs = np.array(angs)
order = np.argsort(norms); norms, angs = norms[order], angs[order]
out = {"X": X, "n_gaussian_primes": int(len(norms))}
for k in range(0, 5):
    w = np.log(norms) * np.cos(4 * k * angs)
    A = np.cumsum(w) - (norms.astype(float) if k == 0 else 0.0)
    blocks = []
    for j in range(10, 27):
        lo, hi = 2**j, min(2**(j + 1), X)
        s = np.searchsorted(norms, [lo, hi])
        if s[1] > s[0]: blocks.append((lo, float(np.max(np.abs(A[s[0]:s[1]])))))
    lx = np.log([b[0] for b in blocks]); ly = np.log([b[1] for b in blocks])
    sel = lx > math.log(1e4)
    slope = float(np.polyfit(lx[sel], ly[sel], 1)[0])
    out[f"k={k}"] = dict(exponent=slope, maxabs_over_sqrtX_last=blocks[-1][1] / math.sqrt(blocks[-1][0]))
    print(f"k={k}: drift exponent {slope:.3f}, max|A|/sqrt(X) in last block {blocks[-1][1]/math.sqrt(blocks[-1][0]):.3f}")
# sector counts: fraction of split-prime angles in 8 equal sectors of [0, pi/2)
th = np.mod(angs, math.pi / 2)
hist = np.histogram(th, bins=8, range=(0, math.pi / 2))[0]
out["sector_fractions"] = (hist / hist.sum()).round(5).tolist()
print("sector fractions (uniform = 0.125):", out["sector_fractions"])
json.dump(out, open("kangle_results.json", "w"), indent=1)
