"""A barrier for arguments built from polynomials shorter than q, at the critical block (README round 575; SEVEN-THIRDS.md section 43).

The class.  Bound the number of characters chi mod q (q prime) with |S(chi)| >= V, where S(chi) = sum_n w(n/N) chi(n)
is a block with weight 0 <= w <= 1 supported on [1, 2], by sum_chi P(chi) with P = sum_j |G_j|^2 and each G_j(chi) =
sum_{m < q} g_j(m) chi(m) a Dirichlet polynomial of length below q.  Since distinct integers below q are distinct mod q,
sum_chi P(chi) = (q - 1) sum_j ||g_j||^2 exactly.  Suppose the inequality P >= 1 is proved at every completely
multiplicative f with |f(p)| = 1 for all p (a point of the infinite torus) at which |sum_n w(n/N) f(n)| >= V, not only
at characters.  The fourth moment (P = |S|^4 / V^4), the 2k-th moments with N^k < q, moments twisted by amplifiers of
total length below q, and finite sums of these are in the class.

The construction.  L = the primes in [N, 2N], K = |L|, K_w = sum_{p in L} w(p/N), and rho = 2V/K_w, which is at most 1
when K_w >= 2V (at V = N^(5/7) this holds for large N, since K_w is about N/log N).  Under the law Omega, f(p) = 1 with
probability rho and is uniform on the circle otherwise for p in L, and f(p) is uniform for every other prime, all
independently.  Then E F = 2V and Var F <= sum_n w(n/N)^2 <= N + 1 for F = sum_n w(n/N) f(n), so by Chebyshev
Omega(|F| >= V) >= 1 - (N + 1)/V^2.  E f(m) conj f(m') = rho^d if m and m' have the same part outside L, where d
counts the primes of L at which their exponents differ, and 0 otherwise.  When q <= N^3, an integer below q has at
most two primes of L, so the Gram matrix of Omega on the polynomials of length below q is block diagonal, each block a
principal submatrix of the kernel rho^d on the multisets of at most two primes of L.  So its top eigenvalue is at most
lam, the kernel's, which is the Perron root of the 4 x 4 quotient on the orbits {1}, {p}, {pp'}, {p^2} (an equitable
partition), with equality when (2N)^2 < q; lam = x^2/2 + O(x) with x = rho^2 K.  For P in the class,
nu = (Omega restricted to |F| >= V)/lam has int |G|^2 dnu <= ||g||^2 for every G of length below q, so
Omega(|F| >= V)/lam <= int P dnu <= sum_j ||g_j||^2, and

    sum_chi P(chi) >= (q - 1)(1 - (N + 1)/V^2)/lam.

At the critical block (N = q^(7/18), V = N^(5/7)) and with w near 1 on [1, 2], x is about 4V^2/K, about 4 N^(3/7) log N,
and the floor is about q^(2/3)/(8 (log N)^2); the fourth moment counts q^(2/3) times a constant times log N.

Weights.  w is 1 on [1.05, 1.95] and rises and falls smoothly on [1, 1.05] and [1.95, 2].

Checks.
  (D1) The quotient's Perron root equals the top eigenvalue of the full kernel on the multisets of at most two of K
       primes, for K in (6, 10, 16, 24) and rho in (0.2, 0.5, 0.9), to relative error 1e-9; and for K = 10^8,
       x^2/2 <= lam <= x^2/2 + 5x + 5 at x = 10, 100, 1000, 10^4.
  (D2) Monte Carlo at N = 10^6 and V = N^(5/7) (where rho < 1): of 40 draws from Omega, at least 95% have |F| >= V.
  (D3) The Gram formula by Monte Carlo (4 * 10^5 draws, rho = 1/2): E f(m) conj f(m') against rho^d for
       (m, m') = (p1, 1), (p1 p2, 1), (p1^2, p1), (p1 p2, p1 p3), (p1 p2, p3 p4) and (s p1, p1) with s a prime outside L
       (prediction 0), each within 0.01.
  (D4) The premise at q = 211: sum_chi |G(chi)|^2 = (q - 1) ||g||^2 for a random G of length 210, to relative error 1e-9.
  (D5) Weak duality, as a consistency check, at N = 2000 with V = K_w/4 (so rho = 1/2) and q = N^(18/7)
       ((2N)^2 < q < N^3): the floor (q - 1)(1 - (N + 1)/V^2)/lam is at most the fourth moment's count (q - 1)E_2/V^4, where
       E_2 = sum_m (sum_{n n' = m} w(n/N) w(n'/N))^2 is computed exactly.  The fourth moment is in the class, so a
       floor above it would refute the construction.
  (D6) The critical floor at N = 10^6, q = N^(18/7), V = N^(5/7), with K and K_w from a sieve: rho <= 1,
       (2N)^2 < q < N^3, and the floor is at least q^(2/3)/(16 (log N)^2).
  Printed, not gated: lam/(x^2/2) in D1; the floor's ratio to q^(2/3)/(8 (log N)^2) in D6 and at q = 10^24, 10^48, 10^96
  with K = N/log N and K_w = 0.95 K.
Mutations, each of which must fail a gate: (m1) rho = 0 in Omega (fails D2); (m2) the Gram formula rho^(d/2) (fails D3);
(m3) the quotient without the disjoint pairs' term C(K-2, 2) rho^4 (fails D1); (m4) G of length 300 > q in D4.

Scope.  This is a statement about the class, not about characters: no argument in the class gives a power saving at
the critical block, since the fourth moment is in the class and is within a power of log N of the floor.  Outside the
class: nonnegative majorants that are not sums of squares of polynomials shorter than q (the floor is proved only for
sums of squares), and arguments that use the periodicity of characters (Poisson summation, Gauss and Jacobi sums,
Burgess's shifts), the functional equation, or congruences of height at least q.
"""
import sys
from itertools import combinations_with_replacement
from math import comb, log

import numpy as np

KS = (6, 10, 16, 24)
RHOS = (0.2, 0.5, 0.9)
XS = (10, 100, 1000, 10000)
MUTS = ("m1", "m2", "m3", "m4")
EDGE = 0.05


def step(t):
    """A smooth step from 0 at t <= 0 to 1 at t >= 1."""
    t = np.clip(t, 0.0, 1.0)
    a = np.where(t > 0, np.exp(-1 / np.maximum(t, 1e-300)), 0.0)
    b = np.where(t < 1, np.exp(-1 / np.maximum(1 - t, 1e-300)), 0.0)
    return a / (a + b)


def weight(u):
    """1 on [1 + EDGE, 2 - EDGE], 0 outside (1, 2), smooth in between."""
    u = np.asarray(u, dtype=float)
    return step((u - 1) / EDGE) * step((2 - u) / EDGE)


def quotient(K, r, mut=None):
    c = comb
    disj = 0.0 if mut == "m3" else c(K - 2, 2) * r ** 4
    B = np.array([
        [1, K * r, c(K, 2) * r ** 2, K * r],
        [r, 1 + (K - 1) * r ** 2, (K - 1) * r + c(K - 1, 2) * r ** 3, r + (K - 1) * r ** 2],
        [r ** 2, 2 * r + (K - 2) * r ** 3, 1 + 2 * (K - 2) * r ** 2 + disj, 2 * r ** 2 + (K - 2) * r ** 3],
        [r, r + (K - 1) * r ** 2, (K - 1) * r ** 2 + c(K - 1, 2) * r ** 3, 1 + (K - 1) * r ** 2]], dtype=float)
    return float(max(np.linalg.eigvals(B).real))


def full_kernel(K, r):
    sets = [()] + [s for k in (1, 2) for s in combinations_with_replacement(range(K), k)]
    vec = np.zeros((len(sets), K), dtype=np.int64)
    for i, s in enumerate(sets):
        for p in s:
            vec[i, p] += 1
    d = (vec[:, None, :] != vec[None, :, :]).sum(-1)
    return float(np.linalg.eigvalsh(r ** d)[-1])


def primes_upto(n):
    s = np.ones(n + 1, dtype=bool)
    s[:2] = False
    for p in range(2, int(n ** 0.5) + 1):
        if s[p]:
            s[p * p::p] = False
    return np.nonzero(s)[0]


def factor_pairs(N, _cache={}):
    """For n in [N, 2N]: (row, prime index) pairs, one per prime factor with multiplicity, over the primes up to 2N."""
    if N in _cache:
        return _cache[N]
    ps = primes_upto(2 * N)
    pidx = np.full(2 * N + 1, -1, dtype=np.int64)
    pidx[ps] = np.arange(len(ps))
    rest = np.arange(N, 2 * N + 1, dtype=np.int64)
    rows, cols = [], []
    for p in ps[ps * ps <= 2 * N]:
        while True:
            hit = np.nonzero(rest % p == 0)[0]
            if hit.size == 0:
                break
            rows.append(hit)
            cols.append(np.full(hit.size, pidx[p]))
            rest[hit] //= p
    big = np.nonzero(rest > 1)[0]
    rows.append(big)
    cols.append(pidx[rest[big]])
    _cache[N] = (ps, np.concatenate(rows), np.concatenate(cols))
    return _cache[N]


def d2(mut=None, _cache={}):
    key = mut == "m1"
    if key in _cache:
        return _cache[key]
    N = 10 ** 6
    V = N ** (5 / 7)
    ps, rows, cols = factor_pairs(N)
    inL = ps >= N
    w = weight(np.arange(N, 2 * N + 1) / N)
    Kw = float(weight(ps[inL] / N).sum())
    rho = 0.0 if mut == "m1" else 2 * V / Kw
    rng = np.random.default_rng(575)
    hits = 0
    for _ in range(4):
        th = rng.random((len(ps), 10))
        th[(rng.random((len(ps), 10)) < rho) & inL[:, None]] = 0.0
        for c in range(10):
            phase = np.bincount(rows, weights=th[cols, c], minlength=N + 1)
            hits += int(abs(w @ np.exp(2j * np.pi * phase)) >= V)
    _cache[key] = (hits / 40, 1 - (N + 1) / V ** 2, rho)
    return _cache[key]


def d3(mut=None):
    rng = np.random.default_rng(5751)
    S, rho = 400000, 0.5
    th = rng.random((5, S))
    th[:4][rng.random((4, S)) < rho] = 0.0
    p1, p2, p3, p4, s = np.exp(2j * np.pi * th)
    pairs = (((p1, 1), 1), ((p1 * p2, 1), 2), ((p1 ** 2, p1), 1), ((p1 * p2, p1 * p3), 2), ((p1 * p2, p3 * p4), 4),
             ((s * p1, p1), None))
    worst = 0.0
    for (a, b), dist in pairs:
        emp = complex(np.mean(a * np.conj(b)))
        pred = 0.0 if dist is None else rho ** (dist / 2 if mut == "m2" else dist)
        worst = max(worst, abs(emp - pred))
    return worst


def d4(mut=None):
    q = 211
    g = 2
    while len({pow(g, k, q) for k in range(1, q)}) != q - 1:
        g += 1
    dl = np.zeros(q, dtype=np.int64)
    x = 1
    for j in range(q - 1):
        dl[x] = j
        x = x * g % q
    rng = np.random.default_rng(57511)
    length = 300 if mut == "m4" else q - 1
    coef = rng.normal(size=length) + 1j * rng.normal(size=length)
    m = np.arange(1, length + 1)
    keep = m % q != 0
    vec = np.zeros(q - 1, dtype=complex)
    np.add.at(vec, dl[m[keep] % q], coef[keep])
    G = np.fft.fft(vec)
    return abs((np.abs(G) ** 2).sum() / ((q - 1) * (np.abs(coef) ** 2).sum()) - 1)


def d5(mut=None):
    N = 2000
    q = N ** (18 / 7)
    ps = primes_upto(2 * N)
    L = ps[ps >= N]
    K, Kw = len(L), float(weight(L / N).sum())
    V = Kw / 4
    lam = quotient(K, 2 * V / Kw, mut)
    floor = (q - 1) * (1 - (N + 1) / V ** 2) / lam
    ns = np.arange(N, 2 * N + 1)
    w = weight(ns / N)
    conv = np.zeros(4 * N * N + 1)
    for n, wn in zip(ns, w):
        if wn:
            conv[n * ns] += wn * w
    fourth = (q - 1) * float((conv ** 2).sum()) / V ** 4
    return {"ok": (2 * N) ** 2 < q < N ** 3 and floor <= fourth, "floor": floor, "fourth": fourth}


def d6(mut=None):
    N = 10 ** 6
    q = N ** (18 / 7)
    V = N ** (5 / 7)
    ps = primes_upto(2 * N)
    L = ps[ps >= N]
    K, Kw = len(L), float(weight(L / N).sum())
    rho = 2 * V / Kw
    lam = quotient(K, rho, mut)
    floor = (q - 1) * (1 - (N + 1) / V ** 2) / lam
    ref = q ** (2 / 3) / (8 * log(N) ** 2)
    ok = rho <= 1 and (2 * N) ** 2 < q < N ** 3 and floor >= ref / 2
    return {"ok": ok, "K": K, "rho": rho, "x": rho * rho * K, "floor": floor, "ratio": floor / ref}


def run(mut=None):
    ok = True
    worst = 0.0
    for K in KS:
        for r in RHOS:
            a, b = quotient(K, r, mut), full_kernel(K, r)
            worst = max(worst, abs(a - b) / b)
    ok &= worst <= 1e-9
    asym = []
    for x in XS:
        lam = quotient(10 ** 8, (x / 10 ** 8) ** 0.5, mut)
        asym.append((x, lam / (x * x / 2)))
        ok &= x * x / 2 <= lam <= x * x / 2 + 5 * x + 5
    frac, cheb, rho = d2(mut)
    ok &= frac >= 0.95
    gram = d3(mut)
    ok &= gram <= 0.01
    prem = d4(mut)
    ok &= prem <= 1e-9
    r5, r6 = d5(mut), d6(mut)
    ok &= r5["ok"] and r6["ok"]
    return bool(ok), {"worst": worst, "asym": asym, "frac": frac, "cheb": cheb, "rho": rho, "gram": gram,
                      "prem": prem, "d5": r5, "d6": r6}


def main():
    ok, rec = run()
    print(f"D1: quotient vs full kernel, worst relative error {rec['worst']:.1e}; lam/(x^2/2) at x = "
          + ", ".join(f"{x}: {v:.5f}" for x, v in rec["asym"]), flush=True)
    print(f"D2: N = 10^6, V = N^(5/7), rho = {rec['rho']:.4f}: fraction of draws with |F| >= V = {rec['frac']:.3f} "
          f"(Chebyshev floor {rec['cheb']:.4f})", flush=True)
    print(f"D3: largest deviation of the Gram formula from Monte Carlo {rec['gram']:.4f}", flush=True)
    print(f"D4: premise at q = 211, relative error {rec['prem']:.1e}", flush=True)
    r5 = rec["d5"]
    print(f"D5: N = 2000, V = K_w/4: floor {r5['floor']:.4e} <= fourth moment's count {r5['fourth']:.4e} "
          f"(ratio {r5['fourth'] / r5['floor']:.2f})", flush=True)
    r6 = rec["d6"]
    print(f"D6: N = 10^6, q = N^(18/7), V = N^(5/7): K = {r6['K']}, rho = {r6['rho']:.4f}, x = {r6['x']:.1f}; "
          f"floor = {r6['floor']:.4e}, which is {r6['ratio']:.3f} times q^(2/3)/(8 (log N)^2)", flush=True)
    for e in (24, 48, 96):
        N = 10 ** (e * 7 / 18)
        V, K = N ** (5 / 7), N / log(N)
        rho = 2 * V / (0.95 * K)
        x = rho * rho * K
        floor = (1 - (N + 1) / V ** 2) / (x * x / 2 + 4 * x) * 10 ** e
        print(f"  q = 10^{e} (K = N/log N, K_w = 0.95 K, lam = x^2/2 + 4x): rho = {rho:.2e}, x = {x:.3e}, "
              f"floor / (q^(2/3)/(8 (log N)^2)) = {floor / (10 ** (2 * e / 3) / (8 * log(N) ** 2)):.3f}", flush=True)
    caught = {m: not run(m)[0] for m in MUTS}
    print(f"gates {'pass' if ok else 'FAIL'}; mutations: "
          + ", ".join(f"{k} {'caught' if v else 'NOT CAUGHT'}" for k, v in caught.items()))
    return 0 if ok and all(caught.values()) else 1


if __name__ == "__main__":
    sys.exit(main())
