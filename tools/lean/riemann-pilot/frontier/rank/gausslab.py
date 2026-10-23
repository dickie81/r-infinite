"""Exact power-residue symbols and Gauss sums over Z[w] (w = e^{2 pi i/3}) and Z[i].

Elements are integer pairs (a, b) meaning a + b*w (field 'w') or a + b*i (field 'i').
Only moduli n that are products of distinct split primes of distinct prime norm are
used, so O/n = Z/N(n) through w -> w0 (or i -> i0) modulo N(n).

Conventions (the companion paper's, as recorded in the pilot's README):
  Z[w]: primary means n = 1 mod 3; additive character  e(Tr(x/(n*sqrt(-3)))).
  Z[i]: primary means n = 1 mod (2+2i);  additive character e(Tr(x/(2n))) = e(Re(x/n)).
The order-N symbol (x/pi)_N is the N-th root of unity congruent to x^{(N(pi)-1)/N} mod pi.
"""
import cmath
import math
from functools import lru_cache

import sympy

W = complex(-0.5, math.sqrt(3) / 2)


def to_c(field, z):
    a, b = z
    return complex(a, 0) + b * (W if field == 'w' else 1j)


def mul(field, z1, z2):
    a, b = z1
    c, d = z2
    if field == 'w':
        return (a * c - b * d, a * d + b * c - b * d)
    return (a * c - b * d, a * d + b * c)


def conj(field, z):
    a, b = z
    return (a - b, -b) if field == 'w' else (a, -b)


def norm(field, z):
    a, b = z
    return a * a - a * b + b * b if field == 'w' else a * a + b * b


def units(field):
    if field == 'w':
        u = [(1, 0), (0, 1), (-1, -1)]          # 1, w, w^2
        return u + [(-a, -b) for a, b in u]
    return [(1, 0), (0, 1), (-1, 0), (0, -1)]


def is_primary(field, z):
    a, b = z
    if field == 'w':
        return a % 3 == 1 and b % 3 == 0
    return (a % 4 == 1 and b % 4 == 0) or (a % 4 == 3 and b % 4 == 2)


def primary_primes(field, pmax):
    """All primary primes pi of degree one with N(pi) = p <= pmax (p split, p not ramified)."""
    out = []
    for p in sympy.primerange(5, pmax + 1):
        if field == 'w' and p % 3 != 1:
            continue
        if field == 'i' and p % 4 != 1:
            continue
        found = set()
        r = int(math.isqrt(4 * p)) + 2
        for b in range(-r, r + 1):
            for a in range(-r, r + 1):
                if norm(field, (a, b)) == p:
                    for u in units(field):
                        z = mul(field, (a, b), u)
                        if is_primary(field, z):
                            found.add(z)
        assert len(found) == 2, (p, found)
        out.extend(sorted(found))
    return out


def root_image(field, z, p):
    """Image of w (resp. i) in Z/p for the prime z of norm p: z = a + b*w = 0 mod z."""
    a, b = z
    return (-a * pow(b, -1, p)) % p


def zeta_order(field, N):
    """The generator of the N-th roots of unity as an element of O, and as a complex number."""
    if field == 'w':
        table = {1: (1, 0), 2: (-1, 0), 3: (0, 1), 6: (1, 1)}          # 1+w = e^{i pi/3}
    else:
        table = {1: (1, 0), 2: (-1, 0), 4: (0, 1)}
    z = table[N]
    return z, cmath.exp(2j * math.pi / N)


@lru_cache(maxsize=None)
def symbol_table(field, pi, N):
    """dict x mod p -> exponent j with (x/pi)_N = zeta_N^j (x != 0 mod p)."""
    p = norm(field, pi)
    r = root_image(field, pi, p)
    zN, _ = zeta_order(field, N)
    zimg = (zN[0] + zN[1] * r) % p
    pows = {}
    cur = 1
    for j in range(N):
        pows[cur] = j
        cur = cur * zimg % p
    e = (p - 1) // N
    return p, r, e, pows


def residue_symbol(field, alpha, pi, N):
    """(alpha/pi)_N as an exponent j in Z/N, or None if pi | alpha."""
    p, r, e, pows = symbol_table(field, pi, N)
    x = (alpha[0] + alpha[1] * r) % p
    if x == 0:
        return None
    return pows[pow(x, e, p)]


def crt_root(field, primes):
    """w0 (or i0) modulo N(n) for n = prod primes (distinct norms)."""
    mods = [norm(field, q) for q in primes]
    rs = [root_image(field, q, norm(field, q)) for q in primes]
    return int(sympy.ntheory.modular.crt(mods, rs)[0]), math.prod(mods)


def prod_elems(field, elems):
    z = (1, 0)
    for e in elems:
        z = mul(field, z, e)
    return z


def trace_int(field, k, n):
    """t with Tr(k/(n*delta)) = t / N(n), delta = sqrt(-3) or 2; returned as an integer."""
    M = norm(field, n)
    kc = to_c(field, k)
    nbar = to_c(field, conj(field, n))
    delta = complex(0, math.sqrt(3)) if field == 'w' else 2.0
    w = kc * nbar / delta
    t = 2 * w.real
    ti = round(t)
    assert abs(t - ti) < 1e-6, (k, n, t)
    return ti


def gauss_brute(field, primes, N, a=1, k=(1, 0)):
    """g(chi_n^a, k) = sum_{x mod n} chi_n(x)^a e(Tr(k x/(n delta))), n = prod primes, by brute force."""
    n = prod_elems(field, primes)
    r, M = crt_root(field, primes)
    t = trace_int(field, k, n)
    _, zc = zeta_order(field, N)
    tabs = [symbol_table(field, q, N) for q in primes]
    total = 0j
    for x in range(M):
        j = 0
        ok = True
        for (p, rr, e, pows) in tabs:
            xm = x % p
            if xm == 0:
                ok = False
                break
            j += pows[pow(xm, e, p)]
        if not ok:
            continue
        total += zc ** ((a * j) % N) * cmath.exp(2j * math.pi * (t * x % M) / M)
    return total, n, M


def alpha(field, n):
    z = to_c(field, n)
    return z / abs(z)


def gauss_brute_pair(field, primes1, primes2, N, a=1):
    """g(chi_{z1}^a conj(chi_{z2})^a) modulo z1 z2, z_j = prod primes_j, by brute force (additive
    character e(Tr(x/(z1 z2 delta)))); the paired Gauss sum of the family's Poisson step."""
    primes = list(primes1) + list(primes2)
    n = prod_elems(field, primes)
    r, M = crt_root(field, primes)
    t = trace_int(field, (1, 0), n)
    _, zc = zeta_order(field, N)
    tabs = [(symbol_table(field, q, N), 1 if i < len(primes1) else -1) for i, q in enumerate(primes)]
    total = 0j
    for x in range(M):
        j = 0
        ok = True
        for (p, rr, e, pows), sgn in tabs:
            xm = x % p
            if xm == 0:
                ok = False
                break
            j += sgn * pows[pow(xm, e, p)]
        if not ok:
            continue
        total += zc ** ((a * j) % N) * cmath.exp(2j * math.pi * (t * x % M) / M)
    return total, n, M
