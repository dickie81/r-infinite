"""The classes at the release's own ray-group primes, 2 and 3 (README round 505).

Round 504 read Xu-Sang's second moment with the release's coefficient chi_s(b_*)/(tau xi(s)) on the classes sigma of
its ray group T. A first Poisson frequency of class (eps, r) enters the complete mean only if
    psi(n) = chi_n(eps e_S(r)) chi_n(b_*) conj(xi(n))
is constant on the fibers of T, and the row condition (m, S) = 1 kills the classes with some r_p = 5. Round 504 did
the primes of S outside T's modulus. Here are the primes over 2 and 3. With pi_2 = 2 and pi_3 = lambda = 1 - omega,
write x = r_2 + 1 and y = r_3 + 1; generator choices and the unit in b_* only relabel eps. The remaining factors of
psi are constant on every class modulo 4: the reciprocity factors R(pi_q, n) of the other primes (periodic mod 4) and
xi_2, a character mod 2. xi_3 is 1 on primary n, which are 1 mod 3. So with T's fibers inside the classes mod 4, a
class (eps, x, y) is kept exactly when n -> chi_n(eps 2^x lambda^y) is constant on the fibers.

How coarse may T be? The release chooses T so that R and G factor through it. G(c) = conj(chi_c(4)) Gamma(c), with
Gamma from its four-term formula, a function of c mod 4, and chi_c(4) "a character of c mod 2". Its proof concludes
that G is a function on the ray group modulo 12.

Units are (1 + omega)^j, with 1 + omega = exp(i pi/3) under omega -> exp(2 pi i/3). Symbols are exponents in Z/6:
chi_n(x) = (1 + omega)^k with k from Euler's criterion x^{(N n - 1)/6} mod n, for primary primes n (n = 1 mod 3), split
(norm q = 1 mod 3) and inert (n = -p, p = 2 mod 3).

Gates (exit status 1 if any fails):
  K1  the coarsest T. On (O/4)^x (12 residues), Gamma from the four-term formula has the release's table (1, 1, i, -i
      on 1, -1, lambda, -lambda), and r(a, b) = Gamma(ab)/(Gamma(a)Gamma(b)) is the release's (-1)^{eh+fg+fh} on
      square classes. chi_c(4) depends only on c mod 2 and takes three values. The largest subgroup of (O/4)^x
      under which every r(a, .) is invariant is the square subgroup {1, omega, omega^2}; with G invariant as well,
      it is {1}. So every T through which R and G factor separates the primary generators mod 4
  K2  the 2- and 3-adic symbols, on the primary primes of norm up to NMAX, with pi_2 = 2 (norm 4) and
      pi_3 = lambda (norm 3) generating the primes over 2 and 3. chi_n(4) depends only on n mod 2 (three
      values); chi_n(-1) and chi_n(lambda)^3 depend only on n mod 4, and neither is constant; chi_n(2)^3 depends only
      on n mod 8 but not on n mod 4; chi_n(omega) and chi_n(lambda)^2 depend only on n mod 9 and together take all
      nine pairs in {0, 2, 4}^2
  K3  T = the classes mod 4 (the coarsest the release allows). Of the 216 classes (j, x, y) in (Z/6)^3, exactly the 12
      with j in {0, 3}, x in {0, 2, 4} and y in {0, 3} are constant on the fibers. Those with r_2, r_3 <= 4 are
      (r_2, r_3) = (1, 2) and (3, 2), each with eps = +-1. A finer T keeps a superset. The kept (r_2, r_3) are the
      same for each of the 36 choices of generators u_2 2 and u_3 lambda (u_2, u_3 units): a generator's unit only
      relabels eps
  K4  for contrast, a partition of the moduli by square classes mod 4 only (it carries R but not G, coarser than the
      release allows), with xi_2 = chi_.(4)^{a_2}: each nonprincipal xi_2 (a_2 = 1, 2) keeps exactly one r_2 <= 4 with
      r_3 = 2; a principal xi_2 (a_2 = 0) keeps none. This is round 504's rule at the prime 2: when the partition does
      not see the cubic character mod 2, xi_2 pins the class
  K5  the factor at 2 and 3 for K3's kept classes, sum of (1 - 1/4) 4^{-r_2/6} (1 - 1/3) 3^{-r_3/6}: positive
"""
import sys
import math
import cmath
import itertools
import numpy as np

NMAX = 60000


def zmul(x, y, m=None):
    a, b = x
    c, d = y
    z = (a * c - b * d, a * d + b * c - b * d)
    return z if m is None else (z[0] % m, z[1] % m)


def znorm(x):
    a, b = x
    return a * a - a * b + b * b


def is_prime(q):
    if q < 2:
        return False
    for d in range(2, int(q ** 0.5) + 1):
        if q % d == 0:
            return False
    return True


def primary_primes(nmax):
    """primary prime elements (n = 1 mod 3) of norm at most nmax, prime to 6."""
    out = []
    for q in range(7, nmax + 1):
        if q % 3 != 1 or not is_prime(q):
            continue
        r = int(2 * (q / 3) ** 0.5) + 2
        for b in range(-r, r + 1):
            if b % 3:
                continue
            disc = 4 * q - 3 * b * b
            if disc < 0:
                continue
            s = math.isqrt(disc)
            if s * s != disc:
                continue
            for a2 in {b + s, b - s}:
                if a2 % 2 == 0 and (a2 // 2 - 1) % 3 == 0:
                    out.append(((a2 // 2, b), q))
    for p in range(5, int(nmax ** 0.5) + 1):
        if p % 3 == 2 and is_prime(p):
            out.append(((-p, 0), p * p))
    return out


ZETA6 = (1, 1)  # 1 + omega = exp(i pi/3)


def chi6(n, N, x):
    """chi_n(x) as k in Z/6 with x^{(N-1)/6} = (1 + omega)^k mod n."""
    if n[1] == 0:  # inert: O/n = F_p[omega], p = -n
        p = -n[0]

        def red(z):
            return (z[0] % p, z[1] % p)

        def mul(u, v):
            return zmul(u, v, p)
    else:
        q = N
        w = (-n[0] * pow(n[1], -1, q)) % q
        assert (w * w + w + 1) % q == 0

        def red(z):
            return ((z[0] + z[1] * w) % q, 0)

        def mul(u, v):
            return ((u[0] * v[0]) % q, 0)
    e, base, acc = (N - 1) // 6, red(x), red((1, 0))
    while e:
        if e & 1:
            acc = mul(acc, base)
        base = mul(base, base)
        e >>= 1
    z = red((1, 0))
    for k in range(6):
        if z == acc:
            return k
        z = mul(z, red(ZETA6))
    raise ValueError('not a sixth root of unity')


def gamma4(c):
    a, b = c
    return (1 + 1j ** (-b % 4) + 1j ** (a % 4) + 1j ** ((b - a) % 4)) / 2


def residues(m):
    return [(a, b) for a in range(m) for b in range(m) if znorm((a, b)) % 2 == 1]


def const_on(groups):
    return all(len(v) == 1 for v in groups.values())


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    P = primary_primes(NMAX)
    LAM, TWO, FOUR, MONE, OMEGA = (1, -1), (2, 0), (4, 0), (-1, 0), (0, 1)
    sym = {}
    for n, N in P:
        sym[n] = {k: chi6(n, N, v) for k, v in
                  (('4', FOUR), ('2', TWO), ('lam', LAM), ('-1', MONE), ('omega', OMEGA), ('zeta', ZETA6))}

    def mod(n, m):
        return (n[0] % m, n[1] % m)

    # K1: the coarsest T, from the release's formulas on (O/4)^x
    U4 = residues(4)
    reps = {(0, 0): (1, 0), (1, 0): (3, 0), (0, 1): (1, 3), (1, 1): (3, 1)}  # (-1)^e lambda^f mod 4
    sq = sorted({zmul(s, s, 4) for s in U4})
    ok = sq == sorted([(1, 0), (0, 1), (3, 3)])
    ok &= [gamma4(reps[k]) for k in ((0, 0), (1, 0), (0, 1), (1, 1))] == [1, 1, 1j, -1j]
    sqclass = {}
    for c in U4:
        hits = [k for k, r in reps.items() if any(zmul(r, s, 4) == c for s in sq)]
        ok &= len(hits) == 1
        sqclass[c] = hits[0]
    r = {}
    for a in U4:
        for b in U4:
            v = gamma4(zmul(a, b, 4)) / (gamma4(a) * gamma4(b))
            (e, f), (g, h) = sqclass[a], sqclass[b]
            ok &= abs(v - (-1) ** (e * h + f * g + f * h)) < 1e-12
            r[(a, b)] = round(v.real)
    by2 = {}
    for n in sym:
        by2.setdefault(mod(n, 2), set()).add(sym[n]['4'])
    ok &= const_on(by2) and len({next(iter(v)) for v in by2.values()}) == 3
    c4 = {c: next(iter(by2[(c[0] % 2, c[1] % 2)])) for c in U4}
    G = {c: cmath.exp(-1j * math.pi * c4[c] / 3) * gamma4(c) for c in U4}
    kR = [k for k in U4 if all(r[(a, zmul(v, k, 4))] == r[(a, v)] for a in U4 for v in U4)]
    kRG = [k for k in kR if all(abs(G[zmul(v, k, 4)] - G[v]) < 1e-12 for v in U4)]
    ok &= sorted(kR) == sq and kRG == [(1, 0)]
    gate('K1', ok, f'Gamma and r match the release\'s table on (O/4)^x; chi_c(4) is a character of c mod 2 with '
                   f'{len({next(iter(v)) for v in by2.values()})} values; invariance group of r: {sorted(kR)} '
                   f'(the squares); of r and G: {kRG}')

    # K2: the 2- and 3-adic symbols
    def depends(key, m, power=1):
        g = {}
        for n in sym:
            g.setdefault(mod(n, m), set()).add(sym[n][key] * power % 6)
        return const_on(g), len({next(iter(v)) for v in g.values()}) if const_on(g) else None

    d = {
        '4 | 2': depends('4', 2), '-1 | 4': depends('-1', 4), 'lam^3 | 4': depends('lam', 4, 3),
        '2^3 | 8': depends('2', 8, 3), '2^3 | 4': depends('2', 4, 3), 'omega | 9': depends('omega', 9),
        'lam^2 | 9': depends('lam', 9, 2), 'omega | 3': depends('omega', 3), 'lam^2 | 3': depends('lam', 3, 2),
    }
    pairs = {(sym[n]['omega'], 2 * sym[n]['lam'] % 6) for n in sym}
    by9 = {}
    for n in sym:
        by9.setdefault(mod(n, 9), set()).add((sym[n]['omega'], 2 * sym[n]['lam'] % 6))
    ok = (znorm(TWO) == 4 and znorm(LAM) == 3 and d['4 | 2'] == (True, 3) and d['-1 | 4'] == (True, 2)
          and d['lam^3 | 4'] == (True, 2)
          and d['2^3 | 8'] == (True, 2) and d['2^3 | 4'][0] is False and d['omega | 9'][0] and d['lam^2 | 9'][0]
          and d['omega | 3'][0] is False and d['lam^2 | 3'][0] is False
          and const_on(by9) and pairs == set(itertools.product((0, 2, 4), repeat=2)))
    ninert = sum(1 for n in sym if n[1] == 0)
    gate('K2', ok, f'{len(sym)} primary primes of norm <= {NMAX} ({ninert} inert): chi(4) on n mod 2, chi(-1) and '
                   f'chi(lambda)^3 on n mod 4, chi(2)^3 on n mod 8 and not mod 4, chi(omega) and chi(lambda)^2 on n mod 9 '
                   f'and not mod 3, with all nine pairs')

    # K3: the classes kept at 2 and 3 for T = the classes mod 4
    def kept(fiber, a2=0):
        out = []
        for j, x, y in itertools.product(range(6), repeat=3):
            g = {}
            for n in sym:
                v = (j * sym[n]['zeta'] + x * sym[n]['2'] + y * sym[n]['lam'] - a2 * sym[n]['4']) % 6
                g.setdefault(fiber(n), set()).add(v)
            if const_on(g):
                out.append((j, x, y))
        return out

    k3 = kept(lambda n: mod(n, 4))
    want = sorted(itertools.product((0, 3), (0, 2, 4), (0, 3)))
    surv = sorted({(x - 1, y - 1) for j, x, y in k3 if x % 6 and y % 6})
    ok = sorted(k3) == want and surv == [(1, 2), (3, 2)]
    ok &= sorted(j for j, x, y in k3 if (x, y) == (2, 3)) == [0, 3]
    # generator choices: u_2 2 and u_3 lambda with u = (1 + omega)^i shift the exponents by i chi_n(1 + omega)
    ns = sorted(sym, key=lambda n: mod(n, 4))
    cls = np.array([U4.index(mod(n, 4)) for n in ns])
    starts = np.flatnonzero(np.r_[True, cls[1:] != cls[:-1]])
    Z, T2, L = (np.array([sym[n][k] for n in ns]) for k in ('zeta', '2', 'lam'))
    gens = set()
    for i2, i3 in itertools.product(range(6), repeat=2):
        sv = set()
        for j, x, y in itertools.product(range(6), repeat=3):
            v = (j * Z + x * (T2 + i2 * Z) + y * (L + i3 * Z)) % 6
            if np.array_equal(np.minimum.reduceat(v, starts), np.maximum.reduceat(v, starts)) and x % 6 and y % 6:
                sv.add((x - 1, y - 1))
        gens.add(tuple(sorted(sv)))
    ok &= len(starts) == 12 and gens == {((1, 2), (3, 2))}
    gate('K3', ok, f'T = classes mod 4: {len(k3)} of 216 classes kept (j in {{0,3}}, x in {{0,2,4}}, y in {{0,3}}); '
                   f'kept with r_2, r_3 <= 4: (r_2, r_3) in {surv}, eps = +-1; the same for all 36 generator choices')

    # K4: a partition by square classes mod 4 only, with xi_2 = chi(4)^{a_2}
    sqc = {}
    for c in U4:
        sqc[c] = sqclass[c]
    res4 = {}
    ok, lines = True, []
    for a2 in (0, 1, 2):
        k4 = kept(lambda n: sqc[mod(n, 4)], a2)
        s4 = sorted({(x - 1, y - 1) for j, x, y in k4 if x % 6 and y % 6})
        res4[a2] = s4
        lines.append(f'a_2 = {a2}: {s4}')
    ok &= res4[0] == [] and len(res4[1]) == 1 and len(res4[2]) == 1 and res4[1] != res4[2]
    ok &= all(len(s) == 1 and s[0][1] == 2 for s in (res4[1], res4[2]))
    gate('K4', ok, 'square classes only, kept with r_2, r_3 <= 4: ' + '; '.join(lines))

    val = sum((1 - 1 / 4) * 4 ** (-(x - 1) / 6) * (1 - 1 / 3) * 3 ** (-(y - 1) / 6)
              for j, x, y in k3 if x % 6 and y % 6)
    gate('K5', val > 0, f'factor at 2 and 3 over K3\'s kept classes: {val:.6f}')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
