"""Patterson-type bias in weighted sums of twisted Gauss sums, and the dual mean squares.

For a weight w on squarefree primary moduli n (coprime to 6), a frequency k and an order
d | N (d = 3: cubic, d = 6: sextic, d = 4: quartic), put
    T_w(k; Z) = sum_{N(n) <= Z} w(n) Gtilde_d(k; n),   Gtilde_d(k; n) = conj(chi_n^{(d)}(k)) Gtilde_d(n),
which is 0 when (k, n) != 1.  Weights: 'one' (all squarefree n), 'prime' (n prime), 'mu' (Moebius).

Prediction tested: the theta-function bias (Patterson: T_one ~ C Z^{1/2+1/d}) is proportional to
the mean value of the weight, so it is present for 'one' and 'prime' and absent for 'mu'.
"""
import json
import math
import sys

import numpy as np

sys.path.insert(0, '.')
from composite import Field, load_primes, squarefree_moduli


def elements_up_to(F, H):
    """All nonzero k in O with N(k) <= H, as integer arrays (ks, kt)."""
    R = int(math.isqrt(4 * H)) + 2
    out = []
    for b in range(-R, R + 1):
        for a in range(-R, R + 1):
            nk = F.norm((a, b))
            if 0 < nk <= H:
                out.append((a, b))
    out.sort(key=lambda z: (F.norm(z), z))
    return np.array([z[0] for z in out]), np.array([z[1] for z in out])


def prime_symbol_matrix(primes, ks, kt):
    """M[i, j] = exponent of (k_j / pi_i)_N, or -1 if pi_i | k_j."""
    return np.stack([P.sym_vec(ks, kt) for P in primes])


def run(fname, path, X, K_list, H, d_list, out_json):
    F = Field(fname)
    N = F.N
    primes = load_primes(F, path, X)
    nm, om, el, G, pr = squarefree_moduli(F, primes, X)
    nmod = len(nm)
    mu = (-1.0) ** om
    weights = {'one': np.ones(nmod), 'prime': (om == 1).astype(float), 'mu': mu}
    grid = sorted(set([int(X / 2 ** j) for j in range(0, 12)] + [X]))
    grid = [z for z in grid if z >= 50]
    idx_at = np.searchsorted(nm, grid, side='right')       # number of moduli with N(n) <= Z
    result = {'field': fname, 'X': X, 'moduli': int(nmod), 'grid': grid, 'single': {}, 'meansq': {},
              'counts': {str(z): int(c) for z, c in zip(grid, idx_at)},
              'mass': {wn: [float(np.sum(wv[:c])) for c in idx_at] for wn, wv in weights.items()}}

    # ---- single frequencies
    ks = np.array([k[0] for k in K_list])
    kt = np.array([k[1] for k in K_list])
    M = prime_symbol_matrix(primes, ks, kt)                 # (#primes, #K)
    E = np.zeros((nmod, len(K_list)), dtype=np.int64)
    dead = np.zeros((nmod, len(K_list)), dtype=bool)
    for i, plist in enumerate(pr):
        rows = M[plist]
        dead[i] = np.any(rows < 0, axis=0)
        E[i] = np.sum(np.where(rows < 0, 0, rows), axis=0) % N
    zeta = np.exp(2j * np.pi * np.arange(N) / N)
    for d in d_list:
        a = N // d                                          # chi^{(d)} = chi^{a}, chi the order-N symbol
        Gd = G[:, a]
        for wname, w in weights.items():
            for j, k in enumerate(K_list):
                tw = np.where(dead[:, j], 0, w * Gd * zeta[(-a * E[:, j]) % N])
                cs = np.concatenate([[0], np.cumsum(tw)])
                vals = cs[idx_at]
                result['single'][f'd={d} w={wname} k={k}'] = [[float(v.real), float(v.imag)] for v in vals]

    # ---- mean squares over all k with 0 < N(k) <= H
    if H:
        ksH, ktH = elements_up_to(F, H)
        nk = len(ksH)
        result['H'] = H
        result['nk'] = int(nk)
        acc = {}
        CH = 100
        for start in range(0, nk, CH):
            sl = slice(start, min(nk, start + CH))
            Mh = prime_symbol_matrix(primes, ksH[sl], ktH[sl])
            Eh = np.zeros((nmod, Mh.shape[1]), dtype=np.int64)
            Dh = np.zeros((nmod, Mh.shape[1]), dtype=bool)
            for i, plist in enumerate(pr):
                rows = Mh[plist]
                Dh[i] = np.any(rows < 0, axis=0)
                Eh[i] = np.sum(np.where(rows < 0, 0, rows), axis=0) % N
            for d in d_list:
                a = N // d
                Gd = G[:, a]
                for wname in ('one', 'mu'):
                    w = weights[wname]
                    tw = np.where(Dh, 0, (w * Gd)[:, None] * zeta[(-a * Eh) % N])
                    cs = np.cumsum(tw, axis=0)
                    for zi, Z in enumerate(grid):
                        cnt = idx_at[zi]
                        if cnt == 0:
                            continue
                        key = f'd={d} w={wname} Z={Z}'
                        acc[key] = acc.get(key, 0.0) + float(np.sum(np.abs(cs[cnt - 1]) ** 2))
        result['meansq'] = acc
    json.dump(result, open(out_json, 'w'))
    return result


if __name__ == '__main__':
    fname, path, X, H, out = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
    if fname == 'w':
        K = [(1, 0), (1, 2), (0, 1), (2, 0), (1, -1), (4, 3), (-2, 3), (8, 0), (7, 0), (1, 3)]
        d_list = [3, 6]
    else:
        K = [(1, 0), (0, 1), (1, 1), (2, 0), (3, 2), (1, 2), (-1, 2), (16, 0), (3, 0)]
        d_list = [4, 2]
    res = run(fname, path, X, K, H, d_list, out)
    print('done', res['moduli'], 'moduli')
