"""The dual mean squares in the regime the cubic route needs: frequencies up to the modulus size.

The cubic family's MeanSquare(sigma) has, after Poisson summation in u, dual rows k with N(k) <= H = Z^{1-sigma}
against columns n with N(n) <= Z, and the rows' total must be << Z^{2+eps}; going below 7/8 needs sigma < 1/8,
i.e. some H > Z^{7/8}.  Over Z[w], for the squarefree primary moduli n of norm <= Z (coprime to 6) and every
frequency k with 0 < N(k) <= H, this script computes
    S_w^{(d)}(H, Z) = sum_k | sum_n w(n) Gtilde_d(n) conj(chi_n^{(d)}(k)) |^2,    d in {3, 6},
for the weights w = 1 ('one'), mu ('mu') and the indicator of primes ('prime'), together with the exact
diagonal sum_k sum_{(n, k) = 1} |w(n)|^2.  The off-diagonal S - diag is the part a large sieve has to control.
(d = 3 with w = mu is the cubic family's dual, alpha conj(G_3)^2 up to the unit, identities.py A2; d = 6 with
w = mu is the sextic family's dual, the companion's case.)

Usage:  python3 critical.py periods_w_FILE out.json Z1 [Z2 ...]
(H: Z^{3/4}, Z^{7/8}, Z/2, Z for each Z).  Output: {"runs": [...]} and a table per Z.
"""
import json
import math
import os
import sys
import time

import numpy as np
from scipy import sparse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from composite import Field, SplitPrime, load_primes, squarefree_moduli    # noqa: E402
from bias import elements_up_to                                            # noqa: E402

ORDERS = (3, 6)
WEIGHTS = ('one', 'mu', 'prime')


def symbol_table(P):
    """(index function, table): table[index(ks, kt)] = exponent j of (k/pi)_N, or -1 where pi | k."""
    if isinstance(P, SplitPrime):
        p = P.p
        x = np.arange(p, dtype=np.int64)
        y, base, e = np.ones(p, dtype=np.int64), x.copy(), P.e
        while e:
            if e & 1:
                y = (y * base) % p
            base = (base * base) % p
            e >>= 1
        tab = np.full(p, -1, dtype=np.int64)
        for val, j in P.pow_index.items():
            tab[y == val] = j
        tab[0] = -1
        r = P.r
        return (lambda ks, kt: (ks + kt * r) % p), tab
    q = P.q
    s, t = np.meshgrid(np.arange(q), np.arange(q), indexing='ij')
    tab = P.sym_arrays(s.ravel(), t.ravel())
    return (lambda ks, kt: (ks % q) * q + (kt % q)), tab


def default_H(Z):
    return sorted({round(Z ** 0.75), round(Z ** 0.875), Z // 2, Z})


def run(path, Z, Hs, CH=1000):
    t0 = time.time()
    F = Field('w')
    N = F.N
    primes = load_primes(F, path, Z)
    nm, om, el, G, pr = squarefree_moduli(F, primes, Z)
    nmod, npr = len(nm), len(primes)
    rows = np.repeat(np.arange(nmod), [len(p) for p in pr])
    cols = np.concatenate([np.array(p) for p in pr])
    inc = sparse.csr_matrix((np.ones(len(rows), dtype=np.int64), (rows, cols)), shape=(nmod, npr))
    tables = [symbol_table(P) for P in primes]
    w = {'one': np.ones(nmod), 'mu': (-1.0) ** om, 'prime': (om == 1).astype(float)}
    keys = [(d, wn) for d in ORDERS for wn in WEIGHTS]
    C = np.array([w[wn] * G[:, N // d] for d, wn in keys])            # (len(keys), nmod)
    Cr, Ci = np.ascontiguousarray(C.real), np.ascontiguousarray(C.imag)
    W2 = np.array([w[wn] ** 2 for wn in WEIGHTS])                     # (3, nmod)
    zeta = np.exp(2j * np.pi * np.arange(N) / N)
    ks, kt = elements_up_to(F, max(Hs))
    knorm = ks * ks - ks * kt + kt * kt
    S = np.zeros((len(keys), len(Hs)))
    diag = np.zeros((len(WEIGHTS), len(Hs)))
    for start in range(0, len(ks), CH):
        a, b = ks[start:start + CH], kt[start:start + CH]
        M = np.stack([tab[f(a, b)] for f, tab in tables])             # (npr, chunk)
        E = (inc @ np.where(M < 0, 0, M)) % N                          # exponent of (k/n)_N
        D = (inc @ (M < 0).astype(np.int64)) > 0                       # (n, k) != 1
        R = np.zeros((len(keys), M.shape[1]), dtype=complex)
        for j in range(N):
            B = ((E == j) & ~D).astype(np.float64)
            Rj = Cr @ B + 1j * (Ci @ B)
            for i, (d, wn) in enumerate(keys):
                R[i] += zeta[(-(N // d) * j) % N] * Rj[i]
        sq = np.abs(R) ** 2
        dg = W2.sum(axis=1)[:, None] - W2 @ D.astype(np.float64)       # sum over (n, k) = 1 of |w(n)|^2
        kn = knorm[start:start + CH]
        for h, H in enumerate(Hs):
            m = kn <= H
            S[:, h] += sq[:, m].sum(axis=1)
            diag[:, h] += dg[:, m].sum(axis=1)
    nk = [int(np.sum(knorm <= H)) for H in Hs]
    res = {'Z': Z, 'H': Hs, 'moduli': int(nmod), 'primes': int(np.sum(om == 1)), 'nk': nk,
           'S': {f'd={d} w={wn}': [float(x) for x in S[i]] for i, (d, wn) in enumerate(keys)},
           'diag': {wn: [float(x) for x in diag[i]] for i, wn in enumerate(WEIGHTS)},
           'seconds': round(time.time() - t0, 1)}
    return res


def show(res):
    print(f"Z = {res['Z']}: {res['moduli']} moduli ({res['primes']} prime), {res['seconds']} s")
    print(f"  {'':16s}" + ''.join(f"{'H=' + str(H):>14s}" for H in res['H']))
    print(f"  {'#k':16s}" + ''.join(f'{x:14d}' for x in res['nk']))
    for key, vals in res['S'].items():
        wn = key.split('w=')[1]
        dg = res['diag'][wn]
        print(f"  {key:16s}" + ''.join(f'{(s - g) / g:+14.4f}' for s, g in zip(vals, dg)) + '   (S - diag)/diag')


if __name__ == '__main__':
    path, out, Zs = sys.argv[1], sys.argv[2], [int(z) for z in sys.argv[3:]]
    runs = []
    for Z in Zs:
        runs.append(run(path, Z, default_H(Z)))
        show(runs[-1])
        json.dump({'runs': runs}, open(out, 'w'))
