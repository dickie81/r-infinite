"""Xu-Sang's main term against the release's A_m: the exceptional Gram term and the principal residue (README round 504).

The release's Gram bound (Proposition prop:probe-gram) is for the column average
    A_m = Y'^{-3/2} sum_s c_sigma(s) W_1(r_s) r_s^{-1+i nu} g_{chi_s}(s, -m),
    c_sigma(s) = 1_{s in sigma} chi_s(b_*) / (tau xi(s)),
over the moduli s of one class sigma of its ray group T. Its low estimate (eq. low-separated) carries the row weight
xi(m), which is zero unless (m, S) = 1. Xu-Sang (arXiv 2610.17675, Lemma lem:uniform-gram) evaluate the Gram sum over
m prime to S for their average, whose coefficient carries the twist conj(chi_s(h)), with main term c_* q^{5/6} L^{-2/3}:
the release's (Q/Y') P_a^{1/6} at q = Q, L = Y'. In their complete mean a prime p of S keeps the first Poisson
frequencies k with v_p(k) = r (mod 6) only when n -> chi_n(eps e_S(r)) conj(chi_n(h)) factors through their ray
quotient. The row projector that restores (m, S) = 1 shifts r to r + 1 at p, and the shift kills r = 5. With the
release's coefficient in place of their twist, the character is
    psi(n) = chi_n(eps e_S(r)) chi_n(b_*) conj(xi(n)).
At a prime p of S not over 6 and outside the support of T's modulus, the p-component of psi is chi_{pi_p}^{r+1}
conj(xi_p). Three facts give it: the pilot's Eis.sextic_recip_coords gives chi_n(pi_p) = R(pi_p, n) chi_{pi_p}(n)
with R periodic modulo 4 (quadPhi_add_four); units enter only over 2 and 3 (eq. sextic-sieve-unit-class); and b_* is
pi_p times a unit and primes other than p.

The high side takes its target signal from the principal row u = 1 (eq. probe-high): the residue of zeta_F^S(6z) at
z = 1/6, which comes from the sum over the frequencies H = a^6. At a prime p of b_* the frequency enters through the
Gauss sum of xi_p at H/s. For xi_p nonprincipal this sum vanishes when p divides H, and leaves conj(xi_p(a))^6 on the
row; for xi_p principal it is the Ramanujan sum, P - 1 when p divides H and -1 otherwise.

This script checks the local identities that reading rests on, in the residue fields F_P of such primes, and the
reciprocity step at one prime. It does not compute a Gram sum, a complete mean over Z[omega], or a residue.

Gates (exit status 1 if any fails):
  X1  (exact) Xu-Sang's range A >= B^{16/11}, with A = Q = Z^M and B = Y' = Z^{l_y}, is M >= 16 l_y/11. It is the
      release's absorption of its third Gram term, P_a^2/Y' <= P_a^{1/6} with P_a = Z^{2 l_y - M}, which is also
      where their main term exceeds their error. On Sang's slice it is b <= 3(1 - ell)/8, and their upper end
      A <= B^2 is P_a >= 1. On the slice the supply caps are b < 137 ell/21 - 1 (ell/h > 21/100) and b < 7 ell - 1
      (ell/h > 1/5). The larger lies inside the range exactly when ell <= 11/59, and round 503's ell = 0.16091 is
      below that
  X2  in F_P for P in PRIMES (residue degree one) and P = 25 (degree two), for every character xi_p of F_P^x and
      every r in 0..5: the mean of chi^{r+1-e} conj(xi_p) over F_P^x, with chi of exact order 6 and e = 1 in the
      projector's twisted term, is 0 or of modulus 1 (1e-9). The classes kept are {a - 1} (e = 0) and {a} (e = 1)
      when xi_p = chi^a, and none when xi_p^6 != 1
  X3  (exact, as Laurent polynomials in t = P^{1/6}) Xu-Sang's reindexing t^{-r} - t^{-5} t^{-((r+1) mod 6)} is
      (1 - t^{-6}) t^{-r} for r <= 4 and 0 for r = 5. With X2's classes, the projected factor at p is
      (1 - t^{-6}) t^{-(a-1)} = (1 - P^{-1}) P^{-(a-1)/6} for xi_p = chi^a with a = 1..5; it is 0 when xi_p is
      principal or xi_p^6 != 1
  X4  the high side's factor at p, from W(H) = sum_x xi_p(x) e(Tr(Hx)/p). For principal xi_p, W is P - 1 at H = 0
      and -1 elsewhere (1e-9). The principal row's p-series sum_t w_t V^t (w_0 = -1, w_t = P - 1, V = P^{-6z}),
      times 1 - V, is exactly P V - 1, which vanishes at z = 1/6. The residue factor
      mean_u W(u^6) + W(0)/(P - 1) has modulus sqrt(P) when xi_p is nonprincipal with xi_p^6 = 1, and is 0 otherwise
      (1e-9)
  X5  for every xi_p at every P, X3's projected factor is nonzero exactly when X4's residue factor is, and both are
      nonzero exactly when xi_p is nonprincipal of order dividing 6
  X6  sextic reciprocity at pi = 1 + 3 omega (norm 7), for every primary prime n of Z[omega] of norm up to 3000:
      chi_n(pi)/chi_pi(n) = 2 Phi(pi n)/(Phi(pi) Phi(n)), with Phi the pilot's quadPhi, and it depends only on n mod 4
"""
import sys
import cmath
import math
import random
from fractions import Fraction as Fr
from lowbudget import ELL_087

PRIMES = (7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97)


class Field:
    """F_P as integers 0..P-1: P = p, or P = p^2 as a + b p for a + b theta with theta^2 a nonresidue mod p."""

    def __init__(self, p, deg):
        self.p, self.P = p, p ** deg
        if deg == 1:
            self.mul = lambda x, y: x * y % p
            self.tr = lambda x: x
        else:
            nr = next(c for c in range(2, p) if pow(c, (p - 1) // 2, p) == p - 1)

            def mul(x, y):
                a, b, c, d = x % p, x // p, y % p, y // p
                return (a * c + nr * b * d) % p + p * ((a * d + b * c) % p)
            self.mul = mul
            self.tr = lambda x: 2 * (x % p) % p
        n = self.P - 1
        for g in range(2, self.P):
            pw, x = [1], g
            while x != 1:
                pw.append(x)
                x = self.mul(x, g)
            if len(pw) == n:
                break
        self.log = {x: k for k, x in enumerate(pw)}
        assert len(self.log) == n

    def pow(self, x, k):
        y = 1
        for _ in range(k):
            y = self.mul(y, x)
        return y

    def char(self, c):
        """the character g^k -> exp(2 pi i c k/(P-1)), extended by zero at 0 (c = 0 is the principal character)."""
        n = self.P - 1
        return lambda x: 0 if x == 0 else cmath.exp(2j * math.pi * c * self.log[x] / n)

    def add_char(self, x):
        return cmath.exp(2j * math.pi * self.tr(x) / self.p)


def classes(F, c, e):
    """the classes r in 0..5 whose fiber mean of chi^{r+1-e} conj(xi_c) is nonzero, and the largest gap from {0, 1}."""
    n, six = F.P - 1, (F.P - 1) // 6
    xi, chi = F.char(c), F.char(six)
    kept, gap = [], 0.0
    for r in range(6):
        m = sum(chi(x) ** (r + 1 - e) * xi(x).conjugate() for x in range(1, F.P)) / n
        gap = max(gap, min(abs(m), abs(abs(m) - 1)))
        if abs(m) > 0.5:
            kept.append(r)
    return kept, gap


def laurent(terms):
    """a Laurent polynomial in t as {exponent: coefficient}, zero coefficients dropped."""
    out = {}
    for k, v in terms:
        out[k] = out.get(k, 0) + v
    return {k: v for k, v in out.items() if v != 0}


def projected(F, c):
    """the projected local factor at p: the classes kept by the untwisted term minus t^{-5} times the twisted term's."""
    k0, g0 = classes(F, c, 0)
    k1, g1 = classes(F, c, 1)
    return laurent([(-r, 1) for r in k0] + [(-5 - r, -1) for r in k1]), k0, k1, max(g0, g1)


def residue_factor(F, c):
    """mean_u W(u^6) + W(0)/(P-1), with W(H) = sum_x xi_c(x) e(Tr(Hx)/p): the residue's factor at p."""
    xi = F.char(c)
    W = lambda H: sum(xi(x) * F.add_char(F.mul(H, x)) for x in range(1, F.P))
    n = F.P - 1
    return sum(W(F.pow(u, 6)) for u in range(1, F.P)) / n + W(0) / n, W


# Z[omega]: (a, b) = a + b omega, omega^2 = -1 - omega

def zmul(x, y):
    a, b = x
    c, d = y
    return (a * c - b * d, a * d + b * c - b * d)


def znorm(x):
    a, b = x
    return a * a - a * b + b * b


def primary(x):
    return (x[0] - 1) % 3 == 0 and x[1] % 3 == 0


def reduce_at(n):
    """the map Z[omega] -> F_q, q = N(n) prime: omega -> -a/b mod q for n = a + b omega."""
    q = znorm(n)
    w = (-n[0] * pow(n[1], -1, q)) % q
    assert (w * w + w + 1) % q == 0
    return q, lambda x: (x[0] + x[1] * w) % q


def chi6(n, x):
    """chi_n(x): the k in Z/6 with x^{(q-1)/6} = (1 + omega)^k mod n, (1 + omega) = exp(i pi/3)."""
    q, red = reduce_at(n)
    v = pow(red(x), (q - 1) // 6, q)
    z, k = (1, 0), 0
    while red(z) != v:
        z, k = zmul(z, (1, 1)), k + 1
        assert k < 6
    return k


def quad_phi(x, y):
    return 1 + 1j ** (-y % 4) + 1j ** (x % 4) + 1j ** ((y - x) % 4)


def main():
    fails = 0

    def gate(name, ok, msg):
        nonlocal fails
        print(f'{name} {"PASS" if ok else "FAIL"}  {msg}')
        fails += 0 if ok else 1

    rng, ok, n = random.Random(504), True, 0
    for _ in range(5000):
        lx, ly = Fr(rng.randint(0, 1000), 1000), Fr(rng.randint(1, 1000), 1000)
        M = lx + ly
        b = 2 * ly - M
        ok &= (M >= Fr(16, 11) * ly) == (2 * b - ly <= b / 6)
        ok &= (M <= 2 * ly) == (b >= 0)
        n += 1
    m = 0
    for li in range(1, 101):
        for bi in range(0, 121):
            ell, b = Fr(li, 200), Fr(bi, 400)
            lx, ly = (1 - b - ell) / 2, (1 + b - ell) / 2
            h = (1 + b + 3 * ell) / 2
            ok &= (lx + ly >= Fr(16, 11) * ly) == (b <= Fr(3, 8) * (1 - ell))
            ok &= (ell / h > Fr(21, 100)) == (b < Fr(137, 21) * ell - 1)
            ok &= (ell / h > Fr(1, 5)) == (b < 7 * ell - 1)
            m += 1
    for ell in (Fr(li, 997) for li in range(0, 998)):
        ok &= (Fr(137, 21) * ell - 1 <= 7 * ell - 1)
        ok &= (7 * ell - 1 <= Fr(3, 8) * (1 - ell)) == (ell <= Fr(11, 59))
    ok &= ELL_087 < 11 / 59
    gate('X1', ok, f'at {n} random geometries: M >= 16 l_y/11 <=> P_a^2/Y\' <= P_a^(1/6), and A <= B^2 <=> P_a >= 1; '
                   f'at {m} slice points: <=> b <= 3(1 - ell)/8, supply caps b < 137 ell/21 - 1 and b < 7 ell - 1; '
                   f'the larger cap inside the range iff ell <= 11/59 = {11 / 59:.5f}; round 503\'s ell = {ELL_087}')

    fields = [Field(p, 1) for p in PRIMES] + [Field(5, 2)]
    ok, gaps, alive, census = True, 0.0, {}, []
    rows = {}
    for F in fields:
        six = (F.P - 1) // 6
        for c in range(F.P - 1):
            f, k0, k1, g = projected(F, c)
            gaps = max(gaps, g)
            if c % six == 0:
                a = c // six
                ok &= k0 == [(a - 1) % 6] and k1 == [a % 6]
            else:
                ok &= k0 == [] and k1 == []
            rows[(F.P, c)] = f
        census.append(f'{F.P}: {F.P - 1}')
    ok &= gaps < 1e-9
    gate('X2', ok, f'fiber means 0 or of modulus 1 (largest gap {gaps:.1e}); classes kept {{a-1}} and {{a}} for '
                   f'xi_p = chi^a, none for xi_p^6 != 1; characters per field: ' + ', '.join(census))

    ok = True
    for r in range(6):
        f = laurent([(-r, 1), (-5 - (r + 1) % 6, -1)])
        ok &= f == ({-r: 1, -r - 6: -1} if r <= 4 else {})
    for F in fields:
        six = (F.P - 1) // 6
        for c in range(F.P - 1):
            f = rows[(F.P, c)]
            if c % six == 0 and c != 0:
                a = c // six
                ok &= f == {-(a - 1): 1, -(a - 1) - 6: -1}
                t = F.P ** (1 / 6)
                val = sum(v * t ** k for k, v in f.items())
                ok &= abs(val - (1 - 1 / F.P) * F.P ** (-(a - 1) / 6)) < 1e-12
            else:
                ok &= f == {}
    gate('X3', ok, 'reindexing t^-r - t^-5 t^-((r+1) mod 6) = (1 - t^-6) t^-r for r <= 4, 0 for r = 5; projected '
                   'factor (1 - P^-1) P^(-(a-1)/6) for xi_p = chi^a, a = 1..5, and 0 for xi_p principal or '
                   'xi_p^6 != 1, in every field')

    ok, dev, high = True, 0.0, {}
    for F in fields:
        six = (F.P - 1) // 6
        for c in range(F.P - 1):
            L, W = residue_factor(F, c)
            if c == 0:
                dev = max(dev, abs(W(0) - (F.P - 1)), max(abs(W(H) + 1) for H in range(1, F.P)))
            want = math.sqrt(F.P) if (c % six == 0 and c != 0) else 0.0
            dev = max(dev, abs(abs(L) - want))
            high[(F.P, c)] = abs(L) > 1e-6
        T = 40
        w = [-1] + [F.P - 1] * T
        prod = [w[0]] + [w[i] - w[i - 1] for i in range(1, T + 1)]
        ok &= prod == [-1, F.P] + [0] * (T - 1)
        ok &= F.P * Fr(1, F.P) - 1 == 0
    ok &= dev < 1e-9
    gate('X4', ok, f'Ramanujan values P - 1 and -1 for principal xi_p; (1 - V) sum_t w_t V^t = P V - 1 to degree 40, '
                   f'zero at V = 1/P (z = 1/6); residue factor of modulus sqrt(P) for xi_p nonprincipal with '
                   f'xi_p^6 = 1, 0 otherwise (largest deviation {dev:.1e})')

    ok, per = True, []
    for F in fields:
        six = (F.P - 1) // 6
        live = 0
        for c in range(F.P - 1):
            lo, hi = rows[(F.P, c)] != {}, high[(F.P, c)]
            ok &= lo == hi == (c % six == 0 and c != 0)
            live += lo
        per.append(f'{F.P}: {live}/{F.P - 1}')
    gate('X5', ok, 'projected exceptional factor nonzero <=> residue factor nonzero <=> xi_p nonprincipal of order '
                   'dividing 6; characters with both nonzero per field: ' + ', '.join(per))

    pi = (1, 3)
    ok, groups, cnt = primary(pi) and znorm(pi) == 7, {}, 0
    ns = []
    for q in range(13, 3001):
        if q % 3 != 1 or any(q % d == 0 for d in range(2, int(q ** 0.5) + 1)):
            continue
        r = int(2 * q ** 0.5) + 2
        ns += [(a, b) for a in range(-r, r + 1) for b in range(-r, r + 1)
               if znorm((a, b)) == q and primary((a, b))]
    for nn in ns:
        k = (chi6(nn, pi) - chi6(pi, nn)) % 6
        rho = cmath.exp(1j * math.pi * k / 3)
        pn = zmul(pi, nn)
        R = 2 * quad_phi(*pn) / (quad_phi(*pi) * quad_phi(*nn))
        ok &= abs(rho - R) < 1e-12 and k in (0, 3)
        key = (nn[0] % 4, nn[1] % 4)
        groups.setdefault(key, set()).add(k)
        cnt += 1
    ok &= all(len(v) == 1 for v in groups.values()) and cnt > 300
    gate('X6', ok, f'{cnt} primary primes n of norm 13..3000: chi_n(pi)/chi_pi(n) = 2 Phi(pi n)/(Phi(pi) Phi(n)) '
                   f'= +-1, constant on each of the {len(groups)} classes of n mod 4 met')
    return 1 if fails else 0


if __name__ == '__main__':
    sys.exit(main())
