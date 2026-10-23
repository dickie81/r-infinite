"""Normalized Gauss sums of order-N residue characters at all squarefree primary moduli of
norm <= X, over Z[w] (N = 6, so orders 6, 3, 2 are available) or Z[i] (N = 4, orders 4, 2).

Prime data: split primes from the C program `periods` (Gauss periods), inert primes by
direct enumeration of F_{q^2}.  Composite moduli by twisted multiplicativity:
    g(chi_{m1 m2}^a) = chi_{m1}(m2)^a chi_{m2}(m1)^a g(chi_{m1}^a) g(chi_{m2}^a),
with chi_m = (./m)_N and the additive character e(Tr(x/(m*delta))) for each factor.
"""
import cmath
import math
import sys

import numpy as np
from sympy import primerange

TWO_PI = 2 * math.pi


class Field:
    def __init__(self, name):
        self.name = name
        self.N = 6 if name == 'w' else 4
        self.zeta = cmath.exp(2j * math.pi / self.N)
        # generator of the N-th roots of unity, as an element of O
        self.zeta_el = (1, 1) if name == 'w' else (0, 1)

    def mul(self, z1, z2):
        a, b = z1
        c, d = z2
        if self.name == 'w':
            return (a * c - b * d, a * d + b * c - b * d)
        return (a * c - b * d, a * d + b * c)

    def norm(self, z):
        a, b = z
        return a * a - a * b + b * b if self.name == 'w' else a * a + b * b

    def to_c(self, z):
        a, b = z
        r = complex(-0.5, math.sqrt(3) / 2) if self.name == 'w' else 1j
        return a + b * r

    def units(self):
        if self.name == 'w':
            u = [(1, 0), (0, 1), (-1, -1)]
            return u + [(-a, -b) for a, b in u]
        return [(1, 0), (0, 1), (-1, 0), (0, -1)]

    def is_primary(self, z):
        a, b = z
        if self.name == 'w':
            return a % 3 == 1 and b % 3 == 0
        return (a % 4 == 1 and b % 4 == 0) or (a % 4 == 3 and b % 4 == 2)

    def inert_primes(self, X):
        out = []
        for q in primerange(2, int(math.isqrt(X)) + 1):
            if self.name == 'w' and q % 3 == 2 and q != 2:
                out.append(q)
            if self.name == 'w' and q == 2:
                continue            # 2 | 6: excluded, as in the companion's family
            if self.name == 'i' and q % 4 == 3:
                out.append(q)
        return out


class SplitPrime:
    def __init__(self, F, row):
        p, a, b, r, j0, c, S = row
        self.F, self.p, self.el, self.r = F, p, (a, b), r
        self.norm = p
        N = F.N
        zimg = (F.zeta_el[0] + F.zeta_el[1] * r) % p
        self.pow_index = {}
        cur = 1
        for j in range(N):
            self.pow_index[cur] = j
            cur = cur * zimg % p
        self.e = (p - 1) // N
        # g(chi^a) = sum_j zeta^{a j0 j} S_j
        self.G = {}
        for aa in range(N):
            g = sum(F.zeta ** ((aa * j0 * j) % N) * S[j] for j in range(N))
            self.G[aa] = g / math.sqrt(p)

    def sym(self, z):
        """exponent j with (z/pi)_N = zeta^j, or None if pi | z."""
        x = (z[0] + z[1] * self.r) % self.p
        if x == 0:
            return None
        return self.pow_index[pow(x, self.e, self.p)]

    def sym_vec(self, ks, kt):
        """vectorized: exponents for arrays of elements k = ks + kt*root; -1 where pi | k."""
        p = self.p
        x = (ks + kt * self.r) % p
        y = np.ones_like(x)
        base = x.copy()
        e = self.e
        while e:
            if e & 1:
                y = (y * base) % p
            base = (base * base) % p
            e >>= 1
        out = np.full(x.shape, -1, dtype=np.int64)
        for val, j in self.pow_index.items():
            out[y == val] = j
        out[x == 0] = -1
        return out


class InertPrime:
    """q inert (q = 2 mod 3 in Z[w], q = 3 mod 4 in Z[i]); primary generator -q (Z[w]) or q or -q (Z[i])."""

    def __init__(self, F, q):
        self.F, self.q = F, q
        cand = [(-q, 0), (q, 0)]
        self.el = [z for z in cand if F.is_primary(z)][0]
        self.norm = q * q
        N = F.N
        self.e = (q * q - 1) // N
        # roots of unity in F_{q^2}: zeta_el^j
        self.pow_index = {}
        cur = (1, 0)
        for j in range(N):
            self.pow_index[(cur[0] % q, cur[1] % q)] = j
            cur = self.fmul(cur, F.zeta_el)
        self.G = self._gauss()

    def fmul(self, x, y):
        q = self.q
        a, b = self.F.mul(x, y)
        return (a % q, b % q)

    def fpow_vec(self, s, t, e):
        q = self.q
        ys, yt = np.ones_like(s), np.zeros_like(s)
        bs, bt = s.copy(), t.copy()
        w = self.F.name == 'w'
        while e:
            if e & 1:
                if w:
                    ys, yt = (ys * bs - yt * bt) % q, (ys * bt + yt * bs - yt * bt) % q
                else:
                    ys, yt = (ys * bs - yt * bt) % q, (ys * bt + yt * bs) % q
            if w:
                bs, bt = (bs * bs - bt * bt) % q, (2 * bs * bt - bt * bt) % q
            else:
                bs, bt = (bs * bs - bt * bt) % q, (2 * bs * bt) % q
            e >>= 1
        return ys, yt

    def sym_arrays(self, s, t):
        ys, yt = self.fpow_vec(s % self.q, t % self.q, self.e)
        out = np.full(s.shape, -1, dtype=np.int64)
        for (u, v), j in self.pow_index.items():
            out[(ys == u) & (yt == v)] = j
        out[(s % self.q == 0) & (t % self.q == 0)] = -1
        return out

    def _gauss(self):
        q, F = self.q, self.F
        s, t = np.meshgrid(np.arange(q), np.arange(q), indexing='ij')
        s, t = s.ravel(), t.ravel()
        j = self.sym_arrays(s, t)
        # additive character e(Tr(x/(n*delta))), n = el = (+-q, 0)
        sign = 1 if self.el[0] > 0 else -1
        if F.name == 'w':
            phase = np.exp(1j * TWO_PI * (sign * t % q) / q)      # Tr(x/(sqrt(-3)*(+-q))) = +-t/q
        else:
            phase = np.exp(1j * TWO_PI * (sign * s % q) / q)      # Tr(x/(2*(+-q))) = +-s/q
        mask = j >= 0
        G = {}
        for aa in range(F.N):
            vals = F.zeta ** ((aa * j[mask]) % F.N)
            G[aa] = complex(np.sum(vals * phase[mask])) / q
        return G

    def sym(self, z):
        j = self.sym_arrays(np.array([z[0]]), np.array([z[1]]))[0]
        return None if j < 0 else int(j)

    def sym_vec(self, ks, kt):
        return self.sym_arrays(ks, kt)


def load_primes(F, path, X):
    primes = []
    for line in open(path):
        v = line.split()
        p = int(v[0])
        if p > X:
            break
        a, b, r, j0, c = map(int, v[1:6])
        S = [complex(float(v[6 + 2 * j]), float(v[7 + 2 * j])) for j in range(F.N)]
        primes.append(SplitPrime(F, (p, a, b, r, j0, c, S)))
    for q in F.inert_primes(X):
        primes.append(InertPrime(F, q))
    primes.sort(key=lambda P: P.norm)
    return primes


def squarefree_moduli(F, primes, X):
    """DFS over squarefree products of the given primes with norm <= X.
    Returns arrays: norm, omega, element (a,b), and G_a for all a (normalized Gauss sums),
    plus the list of prime indices of each modulus."""
    N = F.N
    out_norm, out_omega, out_el, out_G, out_pr = [], [], [], [], []
    stack = [((1, 0), 1, [], {aa: 1.0 + 0j for aa in range(N)}, 0)]
    while stack:
        el, nm, pr, G, start = stack.pop()
        if pr:
            out_norm.append(nm)
            out_omega.append(len(pr))
            out_el.append(el)
            out_G.append([G[aa] for aa in range(N)])
            out_pr.append(pr)
        for idx in range(start, len(primes)):
            P = primes[idx]
            if nm * P.norm > X:
                break
            # cross exponent: chi_{n'}(P)^a chi_P(n')^a
            e1 = 0
            for i in pr:
                e1 += primes[i].sym(P.el)
            e2 = P.sym(el) if pr else 0
            cross = (e1 + e2) % N
            G2 = {aa: G[aa] * P.G[aa] * F.zeta ** ((aa * cross) % N) for aa in range(N)}
            stack.append((F.mul(el, P.el), nm * P.norm, pr + [idx], G2, idx + 1))
    order = np.argsort(out_norm, kind='stable')
    return (np.array(out_norm)[order], np.array(out_omega)[order],
            [out_el[i] for i in order], np.array(out_G)[order], [out_pr[i] for i in order])


if __name__ == '__main__':
    F = Field(sys.argv[1])
    X = int(sys.argv[2])
    primes = load_primes(F, sys.argv[3], X)
    nm, om, el, G, pr = squarefree_moduli(F, primes, X)
    print(len(primes), 'primes;', len(nm), 'squarefree moduli; max |G| dev',
          float(np.max(np.abs(np.abs(G[:, 1:]) - 1))))
