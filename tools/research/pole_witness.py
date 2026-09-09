#!/usr/bin/env python3
"""The pole-free form is indefinite (Theorem 1bt's substrate). With
Q(g) = sum_rho ghat(t_rho)^2, t_rho = (rho - 1/2)/i (Weil's explicit formula
for the autocorrelation of an even real g, unconditional), and the pole term
2 ghat(i/2)^2 removed, Q_0(g) = Q(g) - 2 ghat(i/2)^2. For the witness
    g_a(u) = cosh(u/2) on [-a, a], 0 outside,
    ghat(i/2) = int cosh^2(u/2) du = a + sinh a,
    ghat(r) = 2 [ (1/2) sinh(a/2) cos(ra) + r cosh(a/2) sin(ra) ] / (1/4 + r^2),
and for complex t with |Im t| <= 1/2, one integration by parts gives
    |ghat(t)| <= V(a) e^{a |Im t|} / |t|,   V(a) = 4 cosh(a/2) - 2
(the jumps 2 cosh(a/2) plus the variation 2 (cosh(a/2) - 1)). Hence
    |Q(g_a)| <= V(a)^2 e^a sum_rho 1/|t_rho|^2 <= V(a)^2 e^a K',
K' = 0.0465: sum_rho 1/|t_rho|^2 <= sum_rho 1/gamma_rho^2 <= K (1 + 5/(4 gamma_1^2))
with K = sum_rho 1/(rho (1 - rho)) = 2 + gamma_E - ln(4 pi) = 0.046191... (Hadamard)
and gamma_1 = 14.13... (no zero below 14). So Q_0(g_a) < 0 whenever
    V(a)^2 e^a K' < 2 (a + sinh a)^2,
which holds for every a >= 0.2 (the ratio of the two sides is monotone). All
unconditional. Functions: the closed forms, the bound's two sides, the
zero-side value of Q_0(g_a) on a zero list with the smooth tail (floating
point, a check of the witness at the cells), the Hadamard constant against the
list's partial sum plus the density tail.
"""
import math, json, os
import numpy as np
from scipy.integrate import quad

HERE = os.path.dirname(os.path.abspath(__file__))
CK = os.path.join(HERE, "checkpoints")
EULER = 0.57721566490153286060651209
K_HADAMARD = 2 + EULER - math.log(4*math.pi)          # sum_rho 1/(rho(1-rho))
GAMMA1_LOWER = 14.0                                    # no zero with |gamma| < 14
K_PRIME = K_HADAMARD*(1 + 1.25/GAMMA1_LOWER**2)         # sum_rho 1/gamma^2 <= K (1 + 5/(4 gamma_1^2))

def V(a): return 4*math.cosh(a/2) - 2
def ghat_pole(a): return a + math.sinh(a)
def ghat(r, a):
    r = np.asarray(r, dtype=float)
    return 2*(0.5*math.sinh(a/2)*np.cos(r*a) + r*math.cosh(a/2)*np.sin(r*a))/(0.25 + r*r)
def ghat_quad(r, a):
    """the transform by quadrature (a check of the closed form)."""
    return quad(lambda u: math.cosh(u/2)*math.cos(r*u), -a, a, limit=200)[0]
def bound_lhs(a): return V(a)**2*math.exp(a)*K_PRIME      # >= |Q(g_a)|
def bound_rhs(a): return 2*ghat_pole(a)**2                 # the pole term
def margin(a): return bound_rhs(a) - bound_lhs(a)          # > 0  =>  Q_0(g_a) < 0 (unconditionally)

def Q0_zero_side(a, zs):
    """Q_0(g_a) = 2 sum_{gamma > 0} ghat(gamma)^2 + tail - 2 ghat(i/2)^2 on a zero list (zeta), the tail beyond the last zero by the
    smooth density with sin^2, cos^2 -> 1/2 (their oscillation integrates out at the 1/T level)."""
    s = 2*float(np.sum(ghat(zs, a)**2)); T = float(zs[-1])
    dens = lambda r: math.log(r/(2*math.pi))/(2*math.pi)
    env = lambda r: 4*(0.25*math.sinh(a/2)**2 + r*r*math.cosh(a/2)**2)/(0.25 + r*r)**2     # 2 <ghat^2> = 4 (A^2 + B^2)/D^2 with sin^2, cos^2 -> 1/2, the cross term -> 0 (round 317 F317-4)
    tail = quad(lambda r: env(r)*dens(r), T, np.inf, limit=400)[0]
    return s + tail - bound_rhs(a), s, tail

def autocorr(u, a):
    """f(u) = int cosh(v/2) cosh((v+u)/2) dv over the overlap = sinh(a - u/2) + (a - u/2) cosh(u/2) for 0 <= u <= 2a, 0 beyond."""
    if u >= 2*a: return 0.0
    return math.sinh(a - u/2) + (a - u/2)*math.cosh(u/2)

def Q_prime_side(a, nmax=None):
    """Q(g_a) from Theorem 1bn's prime side: 2 ghat(i/2)^2 + (psi(1/4) - ln pi) f(0) + int_0^inf [f(0) - f(u)] e^{u/2}/sinh u du
    - 2 sum_{n < e^{2a}} Lambda(n) n^{-1/2} f(ln n). Returns (Q, pole, archimedean constant term, archimedean integral, prime side)."""
    import mpmath as mp
    f0 = autocorr(0.0, a)
    const = (float(mp.digamma(0.25)) - math.log(math.pi))*f0
    kern = lambda u: 2*math.exp(-u/2)/(1 - math.exp(-2*u))       # e^{u/2}/sinh u without overflow
    integ = quad(lambda u: (f0 - autocorr(u, a))*kern(u), 0, 2*a, limit=400)[0] + quad(lambda u: f0*kern(u), 2*a, np.inf, limit=400)[0]
    primes = 0.0; n = 2
    while math.log(n) < 2*a:
        m = n; p = 2
        while p*p <= m and m % p: p += 1
        if p*p > m: p = m                                # n prime
        q = m
        while q % p == 0: q //= p
        if q == 1: primes += 2*math.log(p)/math.sqrt(n)*autocorr(math.log(n), a)     # n = p^k: Lambda(n) = ln p
        n += 1
    pole = bound_rhs(a)
    return pole + const + integ - primes, pole, const, integ, -primes

def hadamard_check(zs):
    """sum over the list of 2/(1/4 + gamma^2) plus the density tail against K."""
    s = float(np.sum(2/(0.25 + zs*zs))); T = float(zs[-1])
    tail = quad(lambda r: 2/(0.25 + r*r)*math.log(r/(2*math.pi))/(2*math.pi), T, np.inf)[0]
    return s + tail, s, tail

if __name__ == "__main__":
    zs = np.array(json.load(open(os.path.join(CK, "zeta_zeros_6700.json"))), dtype=float)
    tot, s, tail = hadamard_check(zs)
    print(f"Hadamard K = {K_HADAMARD:.6f}; list + tail = {tot:.6f} (list {s:.6f}, tail {tail:.2e}); K' = {K_PRIME:.6f}")
    for a in (0.15, 0.2, 0.25, 0.5, 0.6914, 1.0, 1.75, 3.0, 10.0):
        q0, s, tail = Q0_zero_side(a, zs)
        Qp, pole, const, integ, pr = Q_prime_side(a) if a <= 2 else (float('nan'),)*5     # the prime side by trial division: a <= 2 only
        print(f"a = {a:<6}: bound lhs {bound_lhs(a):.4f} < rhs {bound_rhs(a):.4f}? margin {margin(a):+.4f} | zero side Q_0(g_a) = {q0:+.4f} (sum {s:.4f}, tail {tail:.2e}) | prime side Q_0 = {Qp - pole:+.4f} (const {const:+.3f}, integral {integ:+.3f}, primes {pr:+.3f}) | ghat check {abs(ghat(3.0, a) - ghat_quad(3.0, a)):.1e}")
