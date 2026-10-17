"""Test B: does turning non-real zeros real lower the Rayleigh quotient Q/||g||^2?

Probes: g = sum_{k<K} c_k cos(k pi t/a) on [-a, a], with sum (-1)^k c_k = 0 (g(+-a) = 0, so
ghat = O(r^-3)). ghat(r) = 2 sin(ra) r P(s)/prod_j (r^2 - w_j^2), s = (ra/pi)^2, where
P(s) = sum_k (-1)^k c_k prod_{j != k} (s - j^2). The zeros of ghat other than j pi/a (j >= K)
are the roots of P. A complex pair sigma, conj(sigma) is four zeros +-rho, +-conj(rho); a
negative root is an imaginary pair.

Realification maps, applied to every non-real root. Each keeps the degree, so the new function
is still even, real, of exponential type a and L^2, i.e. a probe on [-a, a] (Paley-Wiener):
  R1: (s - sigma)(s - conj sigma) -> (s - Re sigma)^2                      [Re sigma > 0]
  R2: -> (s - Re sigma - |Im sigma|)(s - Re sigma + |Im sigma|)   (|.| smaller pointwise)
  R3: -> (s - |sigma|)^2
  imaginary pair: (s - sigma), sigma < 0 -> (s + sigma).
The Rayleigh quotient is computed on the Fourier side:
  Q = 2 ghat(i/2)^2 + (1/pi) int_0^inf |ghat|^2 Phi,  ||g||^2 = (1/pi) int_0^inf |ghat|^2,
  Phi(r) = Re psi(1/4 + ir/2) - log pi - 2 sum_{n <= e^{2a}} Lambda(n) n^{-1/2} cos(r log n),
checked against the Gram matrix of tools/research/weil_prime_gram.py.
Usage: realify.py <tools/research> delta K trials seed"""
import sys, math, json
import numpy as np
from scipy.special import digamma
sys.path.insert(0, sys.argv[1])
delta, K, trials, seed = float(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
a = delta / 2; sc = math.pi / a
rng = np.random.default_rng(seed)
def vm(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0
PP = [(n, vm(n)) for n in range(2, int(math.exp(2 * a)) + 1) if vm(n) > 0]
R = float(__import__("os").environ.get("RMAX", "400")); rs = np.arange(1e-9, R, float(__import__("os").environ.get("STEP", "0.005")))
Phi = digamma(0.25 + 0.5j * rs).real - math.log(math.pi)
for n, L in PP: Phi -= 2 * L / math.sqrt(n) * np.cos(rs * math.log(n))
w2 = (np.arange(K) * sc) ** 2
def ghat(c, z):
    sg = c * (-1.0) ** np.arange(K)
    return 2 * np.sin(z * a) * np.sum(sg[None, :] * z[:, None] / (z[:, None] ** 2 - w2[None, :]), axis=1)
def P_coeffs(c):
    sg = c * (-1.0) ** np.arange(K); P = np.zeros(1)
    for k in range(K):
        term = np.array([1.0])
        for j in range(K):
            if j != k: term = np.polymul(term, [1.0, -float(j * j)])
        P = np.polyadd(P, sg[k] * term)
    return np.trim_zeros(P, 'f')
def rq(gr, gi2):
    num = 2 * gi2 ** 2 + np.trapezoid(np.abs(gr) ** 2 * Phi, rs) / math.pi
    den = np.trapezoid(np.abs(gr) ** 2, rs) / math.pi
    return num / den
def factor(roots, s):
    f = np.ones_like(s, dtype=complex)
    for r in roots: f = f * (s - r)
    return f
def analyse(c):
    roots = np.roots(P_coeffs(c))
    bad_c = [r for r in roots if abs(r.imag) > 1e-9 * max(1, abs(r)) and r.imag > 0]
    bad_n = [r.real for r in roots if abs(r.imag) <= 1e-9 * max(1, abs(r)) and r.real < 0]
    gr = ghat(c, rs.astype(complex)); gi = ghat(c, np.array([0.5j]))[0].real
    base = rq(gr, gi)
    if not bad_c and not bad_n: return base, None
    s = (rs / sc) ** 2; si = (-0.25) / sc ** 2
    old = [r for r in bad_c] + [np.conj(r) for r in bad_c] + bad_n
    out = {}
    for name in ('R1', 'R2', 'R3'):
        new = []; ok = True
        for r in bad_c:
            if name == 'R1': new += [r.real, r.real]; ok &= r.real > 0
            if name == 'R2': new += [r.real + abs(r.imag), r.real - abs(r.imag)]; ok &= r.real - abs(r.imag) > 0
            if name == 'R3': new += [abs(r), abs(r)]
        new += [-x for x in bad_n]
        ratio_r = factor(new, s) / factor(old, s)
        ratio_i = (factor(new, np.array([si])) / factor(old, np.array([si])))[0].real
        out[name] = (rq(gr * ratio_r, gi * ratio_i) - base, bool(ok))
    return base, out
if __name__ == "__main__":
    # validation against the Gram
    from weil_prime_gram import gram
    from flint import arb, ctx
    G, N, pp = gram(delta, K, 128)
    errs = []
    for _ in range(5):
        c = rng.normal(size=K) / (1 + np.arange(K)); c[-1] -= np.sum(c * (-1.0) ** np.arange(K)) * (-1.0) ** (K - 1)
        num = sum(float(G[i, j].mid()) * c[i] * c[j] for i in range(K) for j in range(K))
        den = sum(float(N[i].mid()) * c[i] ** 2 for i in range(K))
        errs.append(abs(num / den - analyse(c)[0]))
    # the constrained ground state (sum (-1)^k c_k = 0) in the K-space, for the local mode
    import os, scipy.linalg
    Gf = np.array([[float(G[i, j].mid()) for j in range(K)] for i in range(K)])
    Nf = np.diag([float(N[i].mid()) for i in range(K)])
    alt = (-1.0) ** np.arange(K)
    V = scipy.linalg.null_space(alt[None, :])
    ev, vec = scipy.linalg.eigh(V.T @ Gf @ V, V.T @ Nf @ V)
    cgs = V @ vec[:, 0]; cgs /= np.sqrt(cgs @ Nf @ cgs)
    eps = float(os.environ.get("LOCAL", "0"))
    stats = {m: [0, 0, [], 0] for m in ('R1', 'R2', 'R3')}   # lowered, raised, deltas, all-real results
    nonreal = 0
    for t in range(trials):
        if eps > 0:
            c = cgs + eps * (V @ rng.normal(size=K - 1))
        else:
            c = rng.normal(size=K) / (1 + np.arange(K)); c[-1] -= np.sum(c * alt) * alt[-1]
        base, out = analyse(c)
        if out is None: continue
        nonreal += 1
        for m, (d, ok) in out.items():
            st = stats[m]; st[0 if d < 0 else 1] += 1; st[2].append(d); st[3] += ok
    res = dict(delta=delta, K=K, trials=trials, local_eps=eps, gs_rq=float(ev[0]), gs_real_rooted=analyse(cgs)[1] is None,
               gram_check_max_err=max(errs), with_nonreal_zeros=nonreal)
    for m, st in stats.items():
        ds = np.array(st[2]) if st[2] else np.array([0.0])
        res[m] = dict(lowered=st[0], raised=st[1], all_real_after=st[3], median=float(np.median(ds)),
                      min=float(ds.min()), max=float(ds.max()))
    print(json.dumps(res))
