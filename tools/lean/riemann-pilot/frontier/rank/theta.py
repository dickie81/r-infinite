"""The cubic theta component of the dual rows (the Dunn-Radziwill correction term), fitted and removed.

Rows are indexed by squarefree primary frequencies k (prime to 6) with N(k) <= H, the rows of Dunn-Radziwill's
cubic large sieve with correction (arXiv:2109.07463, Proposition 9.1):
    T_w(k; Z) = sum_{N(n) <= Z} w(n) G_3(n) conj(chi_n(k)),        chi_n = (./n)_3,  w in {1, prime, mu}.
Their correction term predicts the theta component
    c * u(k) * N(k)^{-1/6} * m_w(k; Z),     m_w(k; Z) = sum_{N(n) <= Z, (n, k) = 1} w(n) N(n)^{-1/6},
with an absolute constant c and a unimodular u(k) built from Gauss sums at k (its form depends on the symbol and
Gauss-sum conventions, so the candidates G_3(k), conj(G_3(k)), G_3(k)^2, conj(G_3(k))^2 and 1 are all tried).
One complex constant c per candidate is fitted by least squares on the weight w = 1 at the largest H; the same c
is then applied to every weight and every H.  Reported: the off-diagonal (S - diag)/diag before and after the
theta component is removed, and the fitted c for w = 1 and for w = prime separately.

Usage:  python3 theta.py periods_w_FILE out.json Z1 [Z2 ...]      (one run per Z, written as {"runs": [...]})
"""
import json
import os
import sys
import time

import numpy as np
from scipy import sparse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from composite import Field, load_primes, squarefree_moduli    # noqa: E402
from critical import symbol_table                              # noqa: E402

WEIGHTS = ('one', 'prime', 'mu', 'mixed')


def run(path, Z, CH=1000):
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
    G3 = G[:, 2]
    # 'mixed': the multiplicative sign w(pi) = -1 if N(pi) = 7 mod 8, else +1 (a quarter of the split primes):
    # sign-changing and multiplicative like mu, but with a mass, sum w(n) N(n)^{-s} ~ zeta_K(s)^{1/2} near s = 1
    sgn = np.array([-1.0 if P.norm % 8 == 7 else 1.0 for P in primes])
    mixed = np.array([np.prod(sgn[p]) for p in pr])
    w = {'one': np.ones(nmod), 'prime': (om == 1).astype(float), 'mu': (-1.0) ** om, 'mixed': mixed}
    C = np.array([w[wn] * G3 for wn in WEIGHTS])
    Cr, Ci = np.ascontiguousarray(C.real), np.ascontiguousarray(C.imag)
    Wm = np.array([w[wn] * nm ** (-1 / 6) for wn in WEIGHTS])        # for the masses m_w(k; Z)
    W2 = np.array([w[wn] ** 2 for wn in WEIGHTS])
    zeta = np.exp(2j * np.pi * np.arange(N) / N)
    ks = np.array([z[0] for z in el])
    kt = np.array([z[1] for z in el])
    T = np.zeros((len(WEIGHTS), nmod), dtype=complex)
    mass = np.zeros((len(WEIGHTS), nmod))
    diag = np.zeros((len(WEIGHTS), nmod))
    # the sextic family's dual: mu(n) G_6(n) conj(chi6_n(k)) = conj(b_n G_3(n) conj(chi_n(k))) with
    # b_n = conj(beta_n) chi2_n(k), beta_n = mu(n) G_6(n) / conj(G_3(n)) (identities.py A3: c(n) alpha(n) G_2(n))
    mu = w['mu']
    C6 = mu * G[:, 1]
    beta = mu * G[:, 1] * G3
    Wb = np.conj(beta) * nm ** (-1 / 6)
    T6 = np.zeros(nmod, dtype=complex)
    mass6 = np.zeros(nmod, dtype=complex)
    for start in range(0, nmod, CH):
        sl = slice(start, min(nmod, start + CH))
        M = np.stack([tab[f(ks[sl], kt[sl])] for f, tab in tables])
        E = (inc @ np.where(M < 0, 0, M)) % N
        D = (inc @ (M < 0).astype(np.int64)) > 0
        Df = D.astype(np.float64)
        for j in range(N):
            B = ((E == j) & ~D).astype(np.float64)
            T[:, sl] += zeta[(-2 * j) % N] * (Cr @ B + 1j * (Ci @ B))
            T6[sl] += zeta[(-j) % N] * (C6.real @ B + 1j * (C6.imag @ B))
            mass6[sl] += (-1) ** j * (Wb.real @ B + 1j * (Wb.imag @ B))
        mass[:, sl] = Wm.sum(axis=1)[:, None] - Wm @ Df
        diag[:, sl] = W2.sum(axis=1)[:, None] - W2 @ Df
    cands = {'G3(k)': G3, 'conj G3(k)': np.conj(G3), 'G3(k)^2': G3 ** 2, 'conj G3(k)^2': np.conj(G3) ** 2,
             '1': np.ones(nmod, dtype=complex)}
    Hs = sorted({round(Z ** 0.75), round(Z ** 0.875), Z // 2, Z})
    masks = [nm <= H for H in Hs]
    out = {'Z': Z, 'H': Hs, 'rows': [int(np.sum(m)) for m in masks], 'candidates': {}, 'weights': {}}
    i1, ip = WEIGHTS.index('one'), WEIGHTS.index('prime')

    def fit(X, Y):
        return complex(np.vdot(X, Y) / np.vdot(X, X))

    def stats(Y, X, dg):
        """per H: (S - diag)/diag before and after removing X, |X|^2/diag, and Re<X, Y>/|X|^2."""
        r = {'before': [], 'after': [], 'theta_over_diag': [], 'projection': []}
        for m in masks:
            d = dg[m].sum()
            S0, S1 = np.sum(np.abs(Y[m]) ** 2), np.sum(np.abs(Y[m] - X[m]) ** 2)
            XX = np.sum(np.abs(X[m]) ** 2)
            r['before'].append(float((S0 - d) / d))
            r['after'].append(float((S1 - d) / d))
            r['theta_over_diag'].append(float(XX / d))
            r['projection'].append(float(np.real(np.vdot(X[m], Y[m])) / XX))
        return r

    for cname, u in cands.items():
        X = u[None, :] * nm[None, :] ** (-1 / 6) * mass
        c1, cp = fit(X[i1], T[i1]), fit(X[ip], T[ip])
        S0 = np.sum(np.abs(T[i1]) ** 2)
        S1 = np.sum(np.abs(T[i1] - c1 * X[i1]) ** 2)
        out['candidates'][cname] = {'c_one': [c1.real, c1.imag], 'c_prime': [cp.real, cp.imag],
                                    'explained': float((S0 - S1) / (S0 - diag[i1].sum()))}
    best = max(out['candidates'], key=lambda k: out['candidates'][k]['explained'])
    c = complex(*out['candidates'][best]['c_one'])
    X = cands[best][None, :] * nm[None, :] ** (-1 / 6) * mass * c
    for i, wn in enumerate(WEIGHTS):
        out['weights'][wn] = stats(T[i], X[i], diag[i])
    # the sextic dual: its theta component is conj of the cubic one for the weight b_n
    X6 = np.conj(c * cands[best] * nm ** (-1 / 6) * mass6)
    out['weights']['sextic mu'] = stats(T6, X6, diag[WEIGHTS.index('mu')])
    out['best'] = best
    out['c'] = [c.real, c.imag]
    out['mass_total'] = {wn: float(np.sum(Wm[i])) for i, wn in enumerate(WEIGHTS)}
    out['seconds'] = round(time.time() - t0, 1)
    return out


def show(r):
    print(f"Z = {r['Z']}: rows {r['rows']} at H = {r['H']}; {r['seconds']} s; "
          f"sum_n w(n) N(n)^(-1/6): " + ', '.join(f'{k} {v:.1f}' for k, v in r['mass_total'].items()))
    for cname, x in r['candidates'].items():
        c1, cp = complex(*x['c_one']), complex(*x['c_prime'])
        print(f"  u(k) = {cname:13s} c(one) {c1.real:+.4f}{c1.imag:+.4f}i, c(prime) {cp.real:+.4f}{cp.imag:+.4f}i,"
              f" share of the excess (w = 1, H = Z) removed {x['explained']:.3f}")
    print(f"  with u(k) = {r['best']} and c = {r['c'][0]:+.4f}{r['c'][1]:+.4f}i (fitted on w = 1):")
    for wn, x in r['weights'].items():
        print(f"    {wn:9s} before " + ' '.join(f'{v:+7.3f}' for v in x['before'])
              + ' | after ' + ' '.join(f'{v:+7.3f}' for v in x['after'])
              + ' | theta/diag ' + ' '.join(f'{v:8.2e}' for v in x['theta_over_diag'])
              + ' | projection ' + ' '.join(f'{v:6.3f}' for v in x['projection']))


if __name__ == '__main__':
    path, out, Zs = sys.argv[1], sys.argv[2], [int(z) for z in sys.argv[3:]]
    runs = []
    for Z in Zs:
        runs.append(run(path, Z))
        show(runs[-1])
        json.dump({'runs': runs}, open(out, 'w'))
