"""Models of the release's coefficients against two sieves' extremal terms (FIVE-SIXTHS.md, sections 7 and 8).

The column term.  In the proof of the release's Lemma lem:hybrid-energy, the rows k (squarefree, norm about K) meet the
dual columns n through the quadratic symbols chi_k(n)^3 = (n/k)_2, and the quadratic large sieve charges K + N.  When
the dual is longer than the rows (N > K, round 500's first branch) that is the column term N, the crossing cost of
section 8.  It is attained by a coefficient aligned with one row's character; target T3 asks for the bound K sum |c_n|^2
for the release's dual coefficients.  By Proposition prop:completed-reflection those coefficients carry the cubic theta
expansions' cusp coefficients d(mu); at squarefree indices this script takes the normalized cubic Gauss sum's conjugate
as their model, times the angle alpha(n) = n/|n|, and in one case times a two-slot sum S(n) built like the release's
marked slots (one-prime factors gamma_2(p) alpha(p)^{-2}/sqrt(q_p), the mark-mark phase (q/p)_3^2 and the column
character chi_P(n)^{-2}).  These are models of the coefficients, not the release's coefficients.

The statistic.  Q = sum_k |sum_n c_n (n/k)_2|^2 / (#rows sum_n |c_n|^2), over the squarefree primary rows k of norm
<= K and the squarefree primary columns n of norm in (N/2, N], all built from the pilot's Gauss sums over Z[w]
(composite.py; the prime data of PAIRING.md section 7).  With no column term Q is about 1; for the aligned sequence
c_n = (n/k0)_2 it is about #columns/#rows.

Gates (exit status 1 if one fails; skipped, and reported, without the prime data):
  N2  at (N, K) = (8*10^4, 250), (8*10^4, 500) and (4*10^4, 1000), with #columns/#rows between 20 and 160: the aligned
      control has Q >= #columns/(2 #rows); random phases, the Gauss-sum models conj(g3), conj(g3) alpha,
      conj(g3) alpha^2 and conj(g3) mu, and the two-slot model conj(g3) alpha S have Q <= 1.5.  So at these sizes these
      coefficient models show no column term.  This is evidence about models of the coefficients at small norms, not a
      bound.

  N3  the cubic large sieve's (NL)^{2/3} term for the slot coefficients' model (FIVE-SIXTHS.md, target T1).  With
      R_k = sum_j |sum_P gamma_2(P) alpha(P)^k chi_P(j)^{-2}|^2 / (#columns sum |coefficient|^2) over the squarefree P
      of norm in (L/2, L] and the squarefree columns j of norm <= N (chi_P(j)^{-2} = conj((j/P)_3), the release's
      column character): at (L, N) = (2*10^4, 500), (4*10^4, 10^3), (8*10^4, 2*10^3) and (8*10^4, 500), the untwisted
      sum (k = 0) has R_0 >= 5, increasing along the first three by a factor between 1.1 and 1.45 per doubling (at
      L/N = 40 the theta term's size (NL)^{2/3}/N grows by 2^{1/3} = 1.26 per doubling): Patterson's theta term, on
      average over the columns.  The angle twists k = -2 (the slot coefficient's), -1, 1, 2 have R_k <= 1.5: no
      excess over the diagonal.  Controls at every size: random unit phases have R <= 1.5, and the coefficient
      conj(chi_P(j0)^{-2}) aligned with one column's character has R >= n0/(2 #columns), with n0 the number of moduli
      prime to j0 (the aligned column alone contributes n0/#columns).  Evidence about models at small norms, not a
      bound.  N3 sums over all squarefree P of one norm range, inert primes included, with no slot windows or weights.

  N4  the largest single row (target T3).  The column term is attained when one row's character aligns with the
      coefficients, and then max_k |sum_n c_n (n/k)_2|^2 / sum |c_n|^2 is about #columns.  At N2's three sizes the
      aligned control's largest row has share at least #columns/2, and every coefficient model of N2 (random phases,
      the Gauss-sum models and the two-slot model) has largest-row share at most 2 log(#rows) + 2, the size of a
      maximum of #rows variables of mean one: no alignment.  Evidence about models at small norms, not a bound.

  N5  target T3 in operator form.  U(k, P) = sum_n beta_n (n/k)_2 conj((n/P)_3), with rows k squarefree of norm <= K,
      moduli P squarefree of norm in (L/2, L] and columns n squarefree of norm in (N/2, N].  T3's hybrid sum is
      sum_k |sum_P c_P U(k, P)|^2 <= ||U||_op^2 sum_P |c_P|^2, so a bound ||U||_op^2 << Z^eps (K + L) sum |beta|^2 for
      the release's dual coefficients would bound it by Z^eps (K + L) sum |beta|^2 sum |c_P|^2, with no column term N:
      a sufficient form of T3.  At (N, K, L) = (4*10^4, 600, 600), (8*10^4, 1000, 600) and (8*10^4, 2000, 1200) the
      ratio ||U||_op^2 / (sum |beta|^2 (sqrt(#rows) + sqrt(#moduli))^2), about the coprime fraction for a random
      matrix, is at most 1.2 for random phases, conj(g3) and conj(g3) alpha, and at least 4 for the aligned control
      beta_n = (n/k0)_2 (n/P0)_3.  Evidence about models at small norms, not a bound.

Usage: python3 columnterm.py periods_w_8e4.txt     (15-30 s; without the prime data every gate is skipped and
reported)
"""
import math
import os
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from composite import Field, load_primes, squarefree_moduli    # noqa: E402

ZETA = np.exp(2j * np.pi * np.arange(6) / 6)
N3_SIZES = ((20000, 500), (40000, 1000), (80000, 2000), (80000, 500))
N5_SIZES = ((40000, 600, 600), (80000, 1000, 600), (80000, 2000, 1200))


def setup(path, N, K):
    F = Field('w')
    primes = load_primes(F, path, N)
    nm, om, el, G, pr = squarefree_moduli(F, primes, N)
    cols = np.flatnonzero((nm > N // 2) & (nm <= N))
    rows = [i for i in range(len(nm)) if nm[i] <= K]
    ns = np.array([el[i][0] for i in cols]); nt = np.array([el[i][1] for i in cols])
    used = sorted({p for i in rows for p in pr[i]})
    sym = {p: primes[p].sym_vec(ns, nt) for p in used}
    X = np.zeros((len(rows), len(cols)))
    for r, i in enumerate(rows):
        E = np.zeros(len(cols), dtype=np.int64)
        Z = np.zeros(len(cols), dtype=bool)
        for p in pr[i]:
            s = sym[p]
            Z |= s < 0
            E += np.where(s < 0, 0, s)
        X[r] = np.where(Z, 0.0, np.where(E % 2 == 0, 1.0, -1.0))   # (n/k)_6^3 = (-1)^E
    z = np.array([complex(el[i][0] - 0.5 * el[i][1], math.sqrt(3) / 2 * el[i][1]) for i in cols])
    return dict(primes=primes, cols=cols, rows=rows, X=X, alpha=z / np.abs(z), g3=G[cols, 2], om=om[cols],
                ns=ns, nt=nt, nm=nm, pr=pr)


def trilinear(d, L, seed):
    """N5: ||U||_op^2 / (sum |beta|^2 (sqrt(#rows) + sqrt(#moduli))^2) for U(k, P) = sum_n beta_n (n/k)_2
    conj((n/P)_3), over the moduli P squarefree of norm in (L/2, L] and setup's rows and columns."""
    primes, ns, nt, nm, pr, X = d['primes'], d['ns'], d['nt'], d['nm'], d['pr'], d['X']
    mods = np.flatnonzero((nm > L // 2) & (nm <= L))
    sym = {p: primes[p].sym_vec(ns, nt) for p in sorted({p for i in mods for p in pr[i]})}
    Y = np.zeros((len(mods), len(ns)), dtype=complex)
    for r, i in enumerate(mods):
        E = np.zeros(len(ns), dtype=np.int64)
        Z = np.zeros(len(ns), dtype=bool)
        for p in pr[i]:
            s = sym[p]
            Z |= s < 0
            E += np.where(s < 0, 0, s)
        Y[r] = np.where(Z, 0, ZETA[(-2 * E) % 6])                      # chi_P(n)^{-2} = conj((n/P)_3)
    nr, nmod = X.shape[0], len(mods)
    scale = (math.sqrt(nr) + math.sqrt(nmod)) ** 2
    ratio = lambda b: float(np.linalg.norm((X * b) @ Y.T, 2) ** 2 / (np.sum(np.abs(b) ** 2) * scale))
    rng = np.random.default_rng(seed)
    out = {'random': ratio(np.exp(2j * np.pi * rng.random(len(ns)))), 'conj g3': ratio(np.conj(d['g3'])),
           'conj g3 alpha': ratio(np.conj(d['g3']) * d['alpha'])}
    out['aligned'] = ratio(X[nr // 2] * np.conj(Y[nmod // 2]))        # (n/k0)_2 (n/P0)_3
    return nr, nmod, len(ns), out


def slot_sum(d, Pslot):
    """two disjoint windows of split primes of norm in (Pslot, 2 Pslot]: S(n) = sum_{p in W1, q in W2} a(p) a(q)
    (q/p)_3^2 chi_p(n)^{-2} chi_q(n)^{-2}, a(p) = gamma_2(p) alpha(p)^{-2} / sqrt(q_p)."""
    primes, ns, nt = d['primes'], d['ns'], d['nt']
    sp = [i for i, P in enumerate(primes) if Pslot < P.norm <= 2 * Pslot and P.norm % 3 == 1]
    W1, W2 = sp[:len(sp) // 2], sp[len(sp) // 2:]
    a, col = {}, {}
    for i in sp:
        P = primes[i]
        pz = complex(P.el[0] - 0.5 * P.el[1], math.sqrt(3) / 2 * P.el[1])
        a[i] = P.G[2] * (abs(pz) / pz) ** 2 / math.sqrt(P.norm)
        s = P.sym_vec(ns, nt)
        col[i] = np.where(s < 0, 0.0, ZETA[(-2 * np.maximum(s, 0)) % 6])   # chi_p(n)^{-2} = (n/p)_6^{-2}
    S = np.zeros(len(ns), dtype=complex)
    pairs = 0
    for p in W1:
        for q in W2:
            e = primes[p].sym(primes[q].el)
            if e is None:
                continue
            S += a[p] * a[q] * ZETA[(4 * e) % 6] * col[p] * col[q]           # (q/p)_3^2 = (q/p)_6^4
            pairs += 1
    return S, pairs


def cubic_sieve(path, L, N, ks=(0, -2, -1, 1, 2)):
    """R_k = sum_j |sum_P gamma_2(P) alpha(P)^k chi_P(j)^{-2}|^2 / (#columns sum |coefficient|^2), over the squarefree
    moduli P of norm in (L/2, L] and the squarefree columns j of norm <= N; chi_P(j)^{-2} = conj((j/P)_3)."""
    F = Field('w')
    primes = load_primes(F, path, max(L, N))
    nm, om, el, G, pr = squarefree_moduli(F, primes, max(L, N))
    mods = np.flatnonzero((nm > L // 2) & (nm <= L))
    cols = np.flatnonzero(nm <= N)
    js = np.array([el[i][0] for i in cols]); jt = np.array([el[i][1] for i in cols])
    used = sorted({p for i in mods for p in pr[i]})
    sym = {p: primes[p].sym_vec(js, jt) for p in used}
    Y = np.zeros((len(mods), len(cols)), dtype=complex)
    for r, i in enumerate(mods):
        E = np.zeros(len(cols), dtype=np.int64)
        Z = np.zeros(len(cols), dtype=bool)
        for p in pr[i]:
            s = sym[p]
            Z |= s < 0
            E += np.where(s < 0, 0, s)
        Y[r] = np.where(Z, 0, ZETA[(-2 * E) % 6])
    z = np.array([complex(el[i][0] - 0.5 * el[i][1], math.sqrt(3) / 2 * el[i][1]) for i in mods])
    al, g = z / np.abs(z), G[mods, 2]
    R = lambda c: float(np.sum(np.abs(c @ Y) ** 2) / (len(cols) * np.sum(np.abs(c) ** 2)))
    out = {k: R(g * al ** k) for k in ks}
    rng = np.random.default_rng(L + N)
    j0 = len(cols) // 2
    n0 = float(np.sum(np.abs(Y[:, j0]) ** 2))
    ctrl = dict(random=R(np.exp(2j * np.pi * rng.random(len(mods)))), aligned=R(np.conj(Y[:, j0])),
                floor=n0 / (2 * len(cols)))
    return out, ctrl


def ratio(X, c):
    T = X @ c
    return float(np.sum(np.abs(T) ** 2) / (X.shape[0] * np.sum(np.abs(c) ** 2)))


def main():
    path = sys.argv[1] if len(sys.argv) > 1 else None
    if not (path and os.path.exists(path)):
        print('N2: SKIPPED  (no prime data given; pass periods_w_8e4.txt, see PAIRING.md section 7)')
        print('N3: SKIPPED  (no prime data given)')
        print('N4: SKIPPED  (no prime data given)')
        print('N5: SKIPPED  (no prime data given)')
        return
    ok, lines, ok4, lines4 = True, [], True, []
    for N, K, Pslot in ((80000, 250, None), (80000, 500, None), (40000, 1000, 50)):
        d = setup(path, N, K)
        X, al, g3 = d['X'], d['alpha'], d['g3']
        nr, nc = X.shape
        rng = np.random.default_rng(N + K)
        models = {'random': np.exp(2j * np.pi * rng.random(nc)), 'conj g3': np.conj(g3),
                  'conj g3 alpha': np.conj(g3) * al, 'conj g3 alpha^2': np.conj(g3) * al ** 2,
                  'conj g3 mu': np.conj(g3) * (-1.0) ** d['om']}
        if Pslot:
            S, pairs = slot_sum(d, Pslot)
            models['conj g3 alpha S'] = np.conj(g3) * al * S
        q = {k: ratio(X, c) for k, c in models.items()}
        aligned = ratio(X, X[nr // 2].astype(complex))
        ok = ok and aligned >= nc / (2 * nr) and all(v <= 1.5 for v in q.values()) and 20 <= nc / nr <= 160
        mx = {k: float(np.max(np.abs(X @ c) ** 2) / np.sum(np.abs(c) ** 2)) for k, c in models.items()}
        ma = float(np.max(np.abs(X @ X[nr // 2]) ** 2) / np.sum(X[nr // 2] ** 2))
        ok4 = ok4 and ma >= nc / 2 and all(v <= 2 * math.log(nr) + 2 for v in mx.values())
        lines4.append(f'N = {N}, K = {K}: aligned {ma:.0f} (#columns/2 = {nc / 2:.0f}), models '
                      f'{min(mx.values()):.2f}-{max(mx.values()):.2f} (2 log(#rows) + 2 = {2 * math.log(nr) + 2:.1f})')
        lines.append(f'N = {N}, K = {K}: {nr} rows, {nc} columns, aligned Q = {aligned:.1f}; '
                     + ', '.join(f'{k} {v:.3f}' for k, v in q.items())
                     + (f' ({pairs} slot pairs)' if Pslot else ''))
    print(f'N2: {"PASS" if ok else "FAIL"}  ' + '; '.join(lines))
    print(f'N4: {"PASS" if ok4 else "FAIL"}  ' + '; '.join(lines4))
    r3 = {LN: cubic_sieve(path, *LN) for LN in N3_SIZES}
    grow = [r3[LN][0][0] for LN in N3_SIZES[:3]]
    ratios = [grow[1] / grow[0], grow[2] / grow[1]]
    ok3 = (all(r3[LN][0][0] >= 5 for LN in N3_SIZES) and all(1.1 <= q <= 1.45 for q in ratios)
           and all(v <= 1.5 for LN in N3_SIZES for k, v in r3[LN][0].items() if k != 0)
           and all(r3[LN][1]['random'] <= 1.5 and r3[LN][1]['aligned'] >= r3[LN][1]['floor'] for LN in N3_SIZES))
    print(f'N3: {"PASS" if ok3 else "FAIL"}  ' + '; '.join(
        f'(L, N) = {LN}: ' + ', '.join(f'k = {k}: {v:.3f}' for k, v in r3[LN][0].items())
        + f', random {r3[LN][1]["random"]:.3f}, aligned {r3[LN][1]["aligned"]:.1f} (floor {r3[LN][1]["floor"]:.1f})'
        for LN in N3_SIZES) + f'; growth of R_0 per doubling {ratios[0]:.3f}, {ratios[1]:.3f} (2^(1/3) = 1.260)')
    ok5, lines5 = True, []
    for N, K, L in N5_SIZES:
        nr, nmod, nc, r5 = trilinear(setup(path, N, K), L, N + K + L)
        ok5 = ok5 and r5['aligned'] >= 4 and all(v <= 1.2 for k, v in r5.items() if k != 'aligned')
        lines5.append(f'(N, K, L) = ({N}, {K}, {L}): {nr} rows, {nmod} moduli, {nc} columns; '
                      + ', '.join(f'{k} {v:.3f}' for k, v in r5.items()))
    print(f'N5: {"PASS" if ok5 else "FAIL"}  ' + '; '.join(lines5))
    if not (ok and ok3 and ok4 and ok5):
        sys.exit(1)
    print('all gates pass')


if __name__ == '__main__':
    main()
