"""The sextic theta component of Gauss-sum rows over Z[w], measured from the dual side (PAIRING.md, section 5).

Moduli: the squarefree primary n (prime to 6) of norm <= Z.  Rows: every nonzero k in Z[w] with N(k) <= H (H = Z
unless given).  The normalized sextic Gauss sum at frequency k is g(n, k) = G_6(n) conj(chi_n(k)), chi_n = (./n)_6,
which is zero when (n, k) != 1.  The weight-one rows R(k) = sum_n g(n, k) are the release's additive polynomial without
its ray-class coefficient.  For each modulus c this script computes the dual projection and its exact diagonal
    T(c) = sum_k conj(R(k)) g(c, k),        diag(c) = #{k : (k, c) = 1},
so y(c) = T(c) - diag(c) = sum_{n != c} sum_k conj(g(n, k)) g(c, k) is an off-diagonal row sum of the Gram matrix.
For any weight w and R_w(k) = sum_n w(n) g(n, k):  <R, R_w> - sum_c w(c) diag(c) = sum_c w(c) y(c).

Unit classes.  The rows are closed under the six units e, and g(n, e k) = conj(chi_n(e)) g(n, k).  Summing over the
units gives exactly T(c) = sum_k conj(R_u(k)) g(c, k), where u = u(c) is the restriction of chi_c to the units (the
exponent of chi_c(1 + w)) and R_u(k) = sum_{n : u(n) = u} g(n, k): a modulus sees only the moduli of its unit class.

The theta reading: by Kubota, sum_c g(c, k) N(c)^{-s} has its pole at s = 2/3, with residue proportional to the
sextic theta coefficient at k.  Within a unit class this predicts R_u(k) ~ rho_u(k) m_u(k), with
m_u(k) = sum_{n in u, (n,k)=1} N(n)^{-1/3}, and
    y(c) ~ N(c)^{-1/3} kappa(c),   kappa(c) = sum_{(k,c)=1} e_u(k)/m_u(k),   e_u(k) = |R_u(k)|^2 - #{n in u : (n,k)=1},
with u = u(c) (e_u(k) estimates |rho_u(k) m_u(k)|^2): within a unit class, the same function of N(c) for every
modulus, whatever its other arithmetic.  Summed over the moduli of one class the two sides agree exactly (both totals
are sum_k e_u(k)); the content is in how y(c) is spread over the moduli of a class.  If the prediction holds modulus
by modulus, every weight w satisfies the mass rule
    sum_c w(c) y(c) ~ sum_c w(c) N(c)^{-1/3} kappa(c),
Moebius and twisted-Moebius weights included.  sextic_stats.py tests it.  The cruder prediction with one class (R, e,
m in place of R_u, e_u, m_u) is stored as kappa1 for comparison.

Also computed, for the forward check: S_w = sum_k |R_w(k)|^2 and diag_w = sum_k sum_{(n,k)=1} w(n)^2 for the
weights one, prime, mixed (the sign -1 on the primes of norm 7 mod 8, as in theta.py) and mu.

Usage:  python3 sextic.py periods_w_FILE OUTDIR Z1[:H1] [Z2[:H2] ...]   (H defaults to Z; writes
        OUTDIR/sextic_w_<Z>.npz, or OUTDIR/sextic_w_<Z>_H<H>.npz when H != Z)
"""
import os
import sys
import time

import numpy as np
from scipy import sparse

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from bias import elements_up_to                                # noqa: E402
from composite import Field, load_primes, squarefree_moduli    # noqa: E402
from critical import symbol_table                              # noqa: E402

WEIGHTS = ('one', 'prime', 'mixed', 'mu')
KUMMER = {'2': (2, 0), 'omega': (0, 1), 'lambda': (1, 2), '-1': (-1, 0), '1+w': (1, 1)}


def run(path, Z, H=None, CH=1000):
    H = Z if H is None else H
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
    # sextic symbols of a few fixed numerators at every modulus (Kummer characters of c); u(c) from 1 + w
    kum = {}
    for name, z in KUMMER.items():
        ex = [P.sym(z) for P in primes]
        kum[name] = np.array([-1 if any(ex[i] is None for i in p) else int(sum(ex[i] for i in p) % N) for p in pr])
    u = kum['1+w']
    U = np.array([(u == j).astype(np.float64) for j in range(N)])          # (6, nmod) class indicators
    G6 = G[:, 1]
    sgn = np.array([-1.0 if P.norm % 8 == 7 else 1.0 for P in primes])
    mixed = np.array([np.prod(sgn[p]) for p in pr])
    w = {'one': np.ones(nmod), 'prime': (om == 1).astype(float), 'mixed': mixed, 'mu': (-1.0) ** om}
    C = np.concatenate([np.array([w[wn] * G6 for wn in WEIGHTS]), U * G6[None, :]])   # 4 weights, then 6 classes
    Cr, Ci = np.ascontiguousarray(C.real), np.ascontiguousarray(C.imag)
    W2 = np.array([w[wn] ** 2 for wn in WEIGHTS])
    Wm = nm ** (-1 / 3)
    UWm = U * Wm[None, :]
    zeta = np.exp(2j * np.pi * np.arange(N) / N)
    zc = np.conj(zeta)
    ks, kt = elements_up_to(F, H)
    T = np.zeros(nmod, dtype=complex)
    dg = np.zeros(nmod)
    kap1 = np.zeros(nmod)
    kap6 = np.zeros(nmod)
    S = np.zeros(len(WEIGHTS))
    dS = np.zeros(len(WEIGHTS))
    nw = len(WEIGHTS)
    for start in range(0, len(ks), CH):
        a, b = ks[start:start + CH], kt[start:start + CH]
        M = np.stack([tab[f(a, b)] for f, tab in tables])
        E = (inc @ np.where(M < 0, 0, M)) % N
        D = (inc @ (M < 0).astype(np.int64)) > 0
        Em = np.where(D, -1, E).astype(np.int8)
        R = np.zeros((C.shape[0], M.shape[1]), dtype=complex)
        for j in range(N):
            B = (Em == j).astype(np.float64)
            R += zc[j] * (Cr @ B + 1j * (Ci @ B))
        Df = D.astype(np.float64)
        # one class
        d1 = nmod - Df.sum(axis=0)
        m1 = Wm.sum() - Wm @ Df
        q1 = (np.abs(R[0]) ** 2 - d1) / m1
        kap1 += q1.sum() - Df @ q1
        # unit classes
        du = U.sum(axis=1)[:, None] - U @ Df                                # (6, chunk)
        mu_ = UWm.sum(axis=1)[:, None] - UWm @ Df
        qu = np.where(mu_ > 0, (np.abs(R[nw:]) ** 2 - du) / np.where(mu_ > 0, mu_, 1), 0.0)
        for j in range(N):
            idx = u == j
            kap6[idx] += qu[j].sum() - Df[idx] @ qu[j]
        dg += M.shape[1] - Df.sum(axis=1)
        Rc = np.conj(R[0])
        for j in range(N):
            B = (Em == j).astype(np.float64)
            T += zc[j] * (B @ Rc)
        S += (np.abs(R[:nw]) ** 2).sum(axis=1)
        dS += (W2.sum(axis=1)[:, None] - W2 @ Df).sum(axis=1)
    T *= G6
    return dict(Z=Z, H=H, nk=len(ks), norm=nm, omega=om, el=np.array(el), mixed=mixed, G6=G6, u=u,
                y=T - dg, diag=dg, kappa=kap6, kappa1=kap1, S=S, dS=dS, weights=np.array(WEIGHTS),
                kummer_names=np.array(list(KUMMER)), kummer=np.array([kum[n] for n in KUMMER]),
                seconds=time.time() - t0)


if __name__ == '__main__':
    path, outdir, args = sys.argv[1], sys.argv[2], sys.argv[3:]
    for arg in args:
        Z, H = (int(x) for x in arg.split(':')) if ':' in arg else (int(arg), int(arg))
        r = run(path, Z, H)
        np.savez(os.path.join(outdir, f'sextic_w_{Z}' + ('' if H == Z else f'_H{H}') + '.npz'), **r)
        print(f"Z = {Z}: {len(r['norm'])} moduli, {r['nk']} rows, {r['seconds']:.1f} s; (S - diag)/diag: "
              + ', '.join(f'{wn} {(s - d) / d:+.4f}' for wn, s, d in zip(WEIGHTS, r['S'], r['dS'])), flush=True)
