"""Is -F'/F = sum c(n) n^{-s} nonnegative (a 'Markov' prime side) for functions with a functional
equation but no Euler product? c from a_n log n = sum_{d|n} c(d) a_{n/d}, a_1 = 1."""
import numpy as np, math, sys
N = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
def cvec(a):
    c = np.zeros(N + 1)
    for n in range(2, N + 1):
        s = a[n] * math.log(n)
        d = 2
        # subtract sum over proper divisors d>=2, d<n of c(d) a(n/d)
        # use a divisor sieve: precomputed below
        c[n] = s
    return c
def cvec_sieve(a):
    c = np.zeros(N + 1)
    acc = np.array([a[n] * math.log(n) if n >= 1 else 0.0 for n in range(N + 1)])
    for d in range(2, N + 1):
        c[d] = acc[d]                       # all divisors < d already subtracted
        if c[d] != 0.0:
            for m in range(2, N // d + 1):  # n = d*m, m >= 2
                acc[d * m] -= c[d] * a[m]
    return c
def report(name, a):
    c = cvec_sieve(a)
    neg = [(n, c[n]) for n in range(2, N + 1) if c[n] < -1e-9]
    nz = [n for n in range(2, N + 1) if abs(c[n]) > 1e-9]
    npp = [n for n in nz if len(set(pf(n))) > 1]
    print(f"{name}: #c<0 = {len(neg)}, first negatives {[(n, round(v, 4)) for n, v in neg[:6]]}, "
          f"#support off prime powers = {len(npp)} (first {npp[:6]})")
def pf(n):
    out, p = [], 2
    while p * p <= n:
        while n % p == 0: out.append(p); n //= p
        p += 1
    if n > 1: out.append(n)
    return out
def epstein(A, B, C):
    r = np.zeros(N + 1); L = int(math.isqrt(4 * N)) + 2
    for x in range(-L, L + 1):
        for y in range(-L, L + 1):
            v = A * x * x + B * x * y + C * y * y
            if 1 <= v <= N: r[v] += 1
    return r / r[1]
# zeta, the Dedekind zeta of Q(sqrt(-5)) (= zeta*L(chi_-20)), and the Epstein zeta of the principal form of
# disc -20 (class number 2; off-line zeros, Davenport-Heilbronn 1936). The non-principal form 2x^2+2xy+3y^2 does
# not represent 1, so its series cannot be normalised to a_1 = 1 and is omitted.
one = np.ones(N + 1)
report("zeta", one)
chi20 = lambda n: 0 if math.gcd(n, 20) > 1 else (1 if n % 20 in (1, 3, 7, 9) else -1)
aL = np.array([0.0] + [chi20(n) for n in range(1, N + 1)])
aK = np.zeros(N + 1)
for d in range(1, N + 1):
    for m in range(1, N // d + 1): aK[d * m] += aL[d]
report("Dedekind Q(sqrt-5)", aK)
report("Epstein x^2+5y^2", epstein(1, 0, 5))
# Davenport-Heilbronn (chi mod 5 with chi(2) = i), kappa from DH
chi5 = {1: 1, 2: 1j, 4: -1, 3: -1j}
kap = (math.sqrt(10 - 2 * math.sqrt(5)) - 2) / (math.sqrt(5) - 1)
aDH = np.array([0.0] + [0.0 if n % 5 == 0 else ((1 - 1j * kap) * chi5[n % 5]).real for n in range(1, N + 1)])
report("Davenport-Heilbronn", aDH)
