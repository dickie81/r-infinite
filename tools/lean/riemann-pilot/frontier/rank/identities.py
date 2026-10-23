"""Moebius absorption for order-N twisted families: the Gauss-sum identities, checked exactly.

For the family A_Z(u) = sum_n mu(n) (u/n)_N W(N(n)/Z), Poisson summation in u leaves, for each
pair of columns, mu(n) times the normalized Gauss sum G_N(n) of chi_n = (./n)_N (the companion
paper's paired identity is the case N = 6; pilot round 304).  Which Gauss sum mu(n) G_N(n) equals,
up to a Hecke character and a unit factor fixed by n modulo a small modulus, decides which theta
function the dual step needs.  Notation: alpha(n) = n/|n| (primary generator), G_d(n) = normalized
Gauss sum of the order-d character (./n)_d, conj = complex conjugate, mu(n) = (-1)^{omega(n)}.

The moduli are all squarefree primary n of norm <= NMAX: products of split primes, inert primes
and conjugate pairs pi*conj(pi) (over Z[w] the prime 2 is excluded with lambda, as in the
companion's family; over Z[i] the prime 1+i is excluded).  Gauss sums at split primes come from
the Gauss periods of periods.c, at inert primes by enumerating F_{q^2}, and at composite moduli by
twisted multiplicativity (composite.py).

Gates (exit status 1 if any fails):
  A0  the composite Gauss sums agree with brute-force sums over O/n (gausslab.py) for every
      modulus that is a product of split primes of distinct norms, all orders, error < 1e-9
  A1  Z[w], cubic:   G_3(n)^3 = mu(n) alpha(n) exactly
  A2  Z[w], cubic family's dual:  mu(n) G_3(n) = alpha(n) conj(G_3(n))^2 exactly
  A3  Z[w], sextic family's dual: mu(n) G_6(n) = c(n) alpha(n) conj(G_3(n)) G_2(n), c(n) a cube root
      of unity fixed by n mod 4 (the companion's absorption: a single cubic Gauss sum)
  A4  Z[w], cubic family's dual as one sextic sum: mu(n) G_3(n) = c(n) alpha(n) conj(G_6(n)) conj(G_2(n)),
      c(n) a sixth root of unity fixed by n mod 4
  A5  Z[w], quadratic: G_2(n) is fixed by n mod 4, and mu(n) is not: the quadratic family's dual keeps
      the Moebius function
  A6  Z[i], quartic: G_4(n)^2 = c(n) mu(n) alpha(n) G_2(n), c(n) = +-1 fixed by n mod 8; G_2(n) = 1
  A7  Z[i], quartic family's dual: mu(n) G_4(n) = c(n) alpha(n) conj(G_4(n)) conj(G_2(n)), c(n) = +-1
      fixed by n mod 8 (a single conjugate quartic Gauss sum)
  A8  Z[w], the cubic family's paired coefficient (round 304's identity at order 3), by brute force over
      O/(z1 z2) for coprime z1, z2 (one or two split primes each, distinct norms, N(z1 z2) <= PAIRMAX):
      mu(z1) mu(z2) G(chi_{z1} conj(chi_{z2})) = a(z1) conj(a(z2)) exactly, a(n) = alpha(n) conj(G_3(n))^2
  A9  Z[i], the same at order 4: mu(z1) mu(z2) G(chi_{z1} conj(chi_{z2})) = c(z1, z2) b(z1) conj(b(z2)),
      b(n) = alpha(n) conj(G_4(n)) conj(G_2(n)), with c = +-1 fixed by (z1 mod 8, z2 mod 8)
"""
import cmath
import itertools
import math
import os
import subprocess
import sys
import tempfile

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import gausslab as gl                                            # noqa: E402
from composite import Field, load_primes, squarefree_moduli      # noqa: E402

NMAX = 2500
PMAX = 200
PAIR_PMAX = 120
PAIRMAX = 3000


def periods_file(field, pmax, tmp):
    exe = os.path.join(tmp, 'periods')
    if not os.path.exists(exe):
        subprocess.run(['gcc', '-O2', '-o', exe, os.path.join(HERE, 'periods.c'), '-lm'], check=True)
    path = os.path.join(tmp, f'periods_{field}_{pmax}.txt')
    with open(path, 'w') as fh:
        subprocess.run([exe, field, str(pmax)], stdout=fh, check=True)
    return path


def root_exp(z, N, tol=1e-9):
    if abs(abs(z) - 1) > tol:
        return None
    ang = cmath.phase(z) / (2 * math.pi) * N
    j = round(ang)
    return j % N if abs(ang - j) < 1e-7 else None


def classify(vals, keys, N):
    """(number of values that are not N-th roots of unity, whether the root is fixed by the key, set of roots)."""
    tab, bad = {}, 0
    for v, k in zip(vals, keys):
        j = root_exp(v, N)
        if j is None:
            bad += 1
            continue
        tab.setdefault(k, set()).add(j)
    fixed = all(len(s) == 1 for s in tab.values())
    roots = sorted(set().union(*tab.values())) if tab else []
    return bad, fixed, roots


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f"[{'PASS' if ok else 'FAIL'}] {name}: {msg}")
        fails += 0 if ok else 1

    with tempfile.TemporaryDirectory() as tmp:
        data = {}
        for f in ('w', 'i'):
            F = Field(f)
            primes = load_primes(F, periods_file(f, PMAX, tmp), NMAX)
            data[f] = (F, primes, squarefree_moduli(F, primes, NMAX))

    # A0: brute force
    worst, checked = 0.0, 0
    for f, (F, primes, (nm, om, el, G, pr)) in data.items():
        for k in range(len(nm)):
            Ps = [primes[i] for i in pr[k]]
            if any(not hasattr(P, 'p') for P in Ps) or len(set(P.p for P in Ps)) < len(Ps):
                continue
            combo = [P.el for P in Ps]
            for a in range(1, F.N):
                g, n, M = gl.gauss_brute(f, combo, F.N, a)
                worst = max(worst, abs(g / math.sqrt(M) - G[k][a]))
            checked += 1
    gate('A0', worst < 1e-9, f'{checked} moduli against brute force, all orders; max error {worst:.1e}')

    F, primes, (nm, om, el, G, pr) = data['w']
    mu = (-1.0) ** om
    al = np.array([F.to_c(z) / abs(F.to_c(z)) for z in el])
    key4 = [(z[0] % 4, z[1] % 4) for z in el]
    G6, G3, G2 = G[:, 1], G[:, 2], G[:, 3]
    n_w = len(nm)
    ninert = sum(1 for P in primes if not hasattr(P, 'p'))
    print(f'    Z[w]: {n_w} squarefree primary moduli of norm <= {NMAX}; {len(primes)} primes ({ninert} inert)')
    err = float(np.max(np.abs(G3 ** 3 - mu * al)))
    gate('A1', err < 1e-9, f'G3^3 = mu alpha on all {n_w}; max error {err:.1e}')
    err = float(np.max(np.abs(mu * G3 - al * np.conj(G3) ** 2)))
    gate('A2', err < 1e-9, f'mu G3 = alpha conj(G3)^2 on all {n_w}; max error {err:.1e}')
    bad, fixed, roots = classify(mu * G6 / (al * np.conj(G3) * G2), key4, 6)
    gate('A3', bad == 0 and fixed and set(roots) <= {0, 2, 4},
         f'mu G6 / (alpha conj(G3) G2): {bad} not roots of unity; fixed by n mod 4: {fixed}; exponents (of e^(2 pi i/6)) {roots}')
    bad, fixed, roots = classify(mu * G3 / (al * np.conj(G6) * np.conj(G2)), key4, 6)
    gate('A4', bad == 0 and fixed, f'mu G3 / (alpha conj(G6) conj(G2)): {bad} not roots of unity; fixed by n mod 4: {fixed}; exponents {roots}')
    bad2, fixed2, _ = classify(G2, key4, 4)
    _, fixed_mu, _ = classify(mu + 0j, key4, 2)
    gate('A5', bad2 == 0 and fixed2 and not fixed_mu,
         f'G2 fixed by n mod 4: {fixed2}; mu fixed by n mod 4: {fixed_mu}')

    F, primes, (nm, om, el, G, pr) = data['i']
    mu = (-1.0) ** om
    al = np.array([F.to_c(z) / abs(F.to_c(z)) for z in el])
    key8 = [(z[0] % 8, z[1] % 8) for z in el]
    G4, G2 = G[:, 1], G[:, 2]
    n_i = len(nm)
    ninert = sum(1 for P in primes if not hasattr(P, 'p'))
    print(f'    Z[i]: {n_i} squarefree primary moduli of norm <= {NMAX}; {len(primes)} primes ({ninert} inert)')
    bad, fixed, roots = classify(G4 ** 2 / (mu * al * G2), key8, 4)
    g2one = float(np.max(np.abs(G2 - 1)))
    gate('A6', bad == 0 and fixed and set(roots) <= {0, 2} and g2one < 1e-9,
         f'G4^2 / (mu alpha G2): {bad} not roots of unity; fixed by n mod 8: {fixed}; exponents (of i) {roots}; max |G2 - 1| {g2one:.1e}')
    bad, fixed, roots = classify(mu * G4 / (al * np.conj(G4) * np.conj(G2)), key8, 4)
    gate('A7', bad == 0 and fixed and set(roots) <= {0, 2},
         f'mu G4 / (alpha conj(G4) conj(G2)): {bad} not roots of unity; fixed by n mod 8: {fixed}; exponents {roots}')

    # A8, A9: the paired coefficients, by brute force
    for f, N, a in (('w', 6, 2), ('i', 4, 1)):
        primes = gl.primary_primes(f, PAIR_PMAX)
        pairs = []
        for k1 in (1, 2):
            for c1 in itertools.combinations(primes, k1):
                for k2 in (1, 2):
                    for c2 in itertools.combinations(primes, k2):
                        norms = [gl.norm(f, q) for q in c1 + c2]
                        if len(set(norms)) == len(norms) and math.prod(norms) <= PAIRMAX:
                            pairs.append((c1, c2))

        def G1(combo, aa):
            g, n, M = gl.gauss_brute(f, list(combo), N, aa)
            return g / math.sqrt(M), n

        worst, tab, bad = 0.0, {}, 0
        for c1, c2 in pairs:
            g, n, M = gl.gauss_brute_pair(f, c1, c2, N, a)
            lhs = (-1) ** (len(c1) + len(c2)) * g / math.sqrt(M)
            (g1, z1), (g2, z2) = G1(c1, a), G1(c2, a)
            al1, al2 = gl.alpha(f, z1), gl.alpha(f, z2)
            if f == 'w':
                worst = max(worst, abs(lhs - al1 * g1.conjugate() ** 2 * (al2 * g2.conjugate() ** 2).conjugate()))
            else:
                (q1, _), (q2, _) = G1(c1, 2), G1(c2, 2)
                j = root_exp(lhs / (al1 * g1.conjugate() * q1.conjugate() * (al2 * g2.conjugate() * q2.conjugate()).conjugate()), 4)
                if j is None:
                    bad += 1
                else:
                    tab.setdefault(((z1[0] % 8, z1[1] % 8), (z2[0] % 8, z2[1] % 8)), set()).add(j)
        if f == 'w':
            gate('A8', worst < 1e-9, f'{len(pairs)} coprime pairs; max error {worst:.1e}')
        else:
            fixed = all(len(v) == 1 for v in tab.values())
            roots = sorted(set().union(*tab.values())) if tab else []
            gate('A9', bad == 0 and fixed and set(roots) <= {0, 2},
                 f'{len(pairs)} coprime pairs; {bad} not roots of unity; fixed by residues mod 8: {fixed}; exponents {roots}')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
