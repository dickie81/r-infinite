#!/usr/bin/env python3
"""The Weil form of the Davenport-Heilbronn function against that of its channel L(s, chi5), on the pilot's
certificate packet g = cos(w u) 1_[-a, a] at (a, w) = (12/5, 169/2) (round 259), and on a scan of w.

Both forms share the archimedean part exactly (both functions have the gamma factor of an odd character of
conductor 5):  Q(g) = (psi(3/4) + log 5 - log pi) f(0) + E(g) - 2 sum_n b(n) n^{-1/2} f(log n),  f = g*g the
autocorrelation, E the archimedean integral (as in frontier/dh/qdhu_hp.py).  For dh, b(n) = c(n), the coefficients
of -dh'/dh; for L(s, chi5) with an even test function, b(n) = Lambda(n) Re chi5(n).  Under GRH for chi5 the second
form is a sum of squares, hence >= 0.  The difference Q_dh - Q_chi = -2 sum_n (c(n) - Lambda(n) Re chi5(n)) ...
is supported on the integers all of whose prime factors are = +-2 mod 5; the script checks that identity term by
term and reports the largest contributions.
"""
import mpmath as mp
mp.mp.dps = 40
chi = {0: 0, 1: 1, 2: 1j, 3: -1j, 4: -1}
kappa = (mp.sqrt(10 - 2*mp.sqrt(5)) - 2)/(mp.sqrt(5) - 1)
uval = {0: mp.mpf(0), 1: mp.mpf(1), 2: kappa, 3: -kappa, 4: mp.mpf(-1)}
N = 700
u = [mp.mpf(0)]*(N + 1)
for n in range(2, N + 1): u[n] = uval[n % 5]
dinv = [mp.mpf(0)]*(N + 1); dinv[1] = mp.mpf(1)
for n in range(2, N + 1): dinv[n] = -sum(u[d]*dinv[n//d] for d in range(2, n + 1) if n % d == 0)
lm = lambda n: mp.log(n)*((1 if n == 1 else 0) + u[n])
c = [mp.mpf(0)]*(N + 1)
for n in range(1, N + 1): c[n] = sum(lm(d)*dinv[n//d] for d in range(1, n + 1) if n % d == 0)
def factor(n):
    f, p = {}, 2
    while p*p <= n:
        while n % p == 0: f[p] = f.get(p, 0) + 1; n //= p
        p += 1
    if n > 1: f[n] = f.get(n, 0) + 1
    return f
def Lam(n):
    f = factor(n); return mp.log(list(f)[0]) if len(f) == 1 else mp.mpf(0)
inert = lambda n: all(p % 5 in (2, 3) for p in factor(n))
b_chi = [mp.mpf(0)]*(N + 1)
for n in range(2, N + 1): b_chi[n] = Lam(n)*mp.re(chi[n % 5])
psi34 = mp.digamma(mp.mpf(3)/4); const = psi34 + mp.log(5) - mp.log(mp.pi)
def forms(a, w):
    a = mp.mpf(a); w = mp.mpf(w)
    f0 = a + mp.sin(2*w*a)/(2*w)
    f = lambda x: mp.mpf(1)/2*(2*a - x)*mp.cos(w*x) + mp.sin(w*(2*a - x))/(2*w) if x < 2*a else mp.mpf(0)
    K = lambda x: mp.exp(-x/2)/mp.sinh(x)
    E = mp.quad(lambda x: (f0 - f(x))*K(x), mp.linspace(0, 2*a, 200)) + f0*mp.quad(K, [2*a, mp.inf])
    Nmax = int(mp.floor(mp.exp(2*a)))
    terms = [(n, (c[n] - b_chi[n])/mp.sqrt(n)*f(mp.log(n))) for n in range(2, Nmax + 1)]
    S_dh = sum(c[n]/mp.sqrt(n)*f(mp.log(n)) for n in range(2, Nmax + 1))
    S_chi = sum(b_chi[n]/mp.sqrt(n)*f(mp.log(n)) for n in range(2, Nmax + 1))
    arch = const*f0 + E
    return dict(f0=f0, arch=arch, S_dh=S_dh, S_chi=S_chi, Q_dh=arch - 2*S_dh, Q_chi=arch - 2*S_chi, terms=terms, Nmax=Nmax)
if __name__ == '__main__':
    r = forms(mp.mpf(12)/5, mp.mpf(169)/2)
    off = [(n, d) for n, d in r['terms'] if not inert(n) and abs(d) > mp.mpf(10)**-30]
    print(f"packet (a, w) = (12/5, 169/2): ||g||^2 = {mp.nstr(r['f0'], 12)}, n <= {r['Nmax']}")
    print(f"  archimedean part (shared)  = {mp.nstr(r['arch'], 15)}")
    print(f"  prime sum, dh             S = {mp.nstr(r['S_dh'], 15)}")
    print(f"  prime sum, L(s,chi5)      S = {mp.nstr(r['S_chi'], 15)}")
    print(f"  Q_dh  = {mp.nstr(r['Q_dh'], 15)}")
    print(f"  Q_chi = {mp.nstr(r['Q_chi'], 15)}")
    print(f"  difference terms at integers with a prime factor not = +-2 mod 5: {len(off)} (must be 0)")
    tot = sum(d for n, d in r['terms'])
    print(f"  Q_dh - Q_chi = -2 * {mp.nstr(tot, 15)} = {mp.nstr(-2*tot, 15)}; check {mp.nstr(r['Q_dh'] - r['Q_chi'] + 2*tot, 3)}")
    top = sorted(r['terms'], key=lambda nd: -abs(nd[1]))[:12]
    print("  largest inert-smooth contributions to Q_dh - Q_chi (n: -2 (c(n) - Lambda(n) Re chi(n)) f(log n)/sqrt(n)):")
    for n, d in top: print(f"    n = {n:4d} {factor(n)}: {mp.nstr(-2*d, 8)}")
