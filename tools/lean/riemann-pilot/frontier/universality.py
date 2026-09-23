"""Round 30: is the zero flow specific to zeta's symbol?

Ground states of Q(g) = (1/pi) int_0^inf |ghat|^2 Phi(r) dr [+ 2 ghat(i/2)^2] on even L^2(-a, a),
in the cosine basis cos(k pi t/a), k < K. Gram by Fourier quadrature on (0, R], plus the tail
2(-1)^{j+k} int_R^inf Phi(r)/r^2 dr (from sin^2 -> 1/2), in double precision. For each symbol
and delta: ground states at delta and delta +- h; zeros of ghat in (0, 60); their velocities;
the Wronskian W = ghat d_x d_delta ghat - d_delta ghat d_x ghat on a grid.
Usage: universality.py <symbol> delta [delta ...]"""
import sys, math, json
import numpy as np
from scipy.special import digamma
from scipy.linalg import eigh

def vm(n):
    for p in range(2, n + 1):
        if n % p == 0:
            m = n
            while m % p == 0: m //= p
            return math.log(p) if m == 1 else 0.0
    return 0.0

import os
rng = np.random.default_rng(int(os.environ.get("SEED", "12345")))
JIT = float(os.environ.get("JITTER", "0.08"))     # full width of the log n jitter
WJ = float(os.environ.get("WJITTER", "1.0"))      # full width of the weight jitter
FAKE_SHIFT = {n: 1 + JIT * (rng.random() - 0.5) for n in range(2, 400)}
FAKE_W = {n: 1 + WJ * (rng.random() - 0.5) for n in range(2, 400)}

def make_phi(name, a):
    arch = lambda r: digamma(0.25 + 0.5j * r).real - math.log(math.pi)
    PP = [(n, vm(n)) for n in range(2, int(math.exp(2 * a)) + 1) if vm(n) > 0]
    if name == 'zeta':
        def f(r):
            v = arch(r)
            for n, L in PP: v = v - 2 * L / math.sqrt(n) * np.cos(r * math.log(n))
            return v
        return f, True
    if name == 'arch':          # no primes, with pole
        return arch, True
    if name == 'arch_nopole':
        return arch, False
    if name == 'log':           # scale-invariant up to the +1
        return (lambda r: np.log(1 + r)), False
    if name == 'fake_log_n':    # the primes' frequencies jittered by +-4%
        def f(r):
            v = arch(r)
            for n, L in PP: v = v - 2 * L / math.sqrt(n) * np.cos(r * math.log(n) * FAKE_SHIFT[n])
            return v
        return f, True
    if name == 'fake_weights':  # prime weights multiplied by U(0.5, 1.5)
        def f(r):
            v = arch(r)
            for n, L in PP: v = v - 2 * L * FAKE_W[n] / math.sqrt(n) * np.cos(r * math.log(n))
            return v
        return f, True
    if name == 'all_n':         # every integer n >= 2 with weight log n (Lambda replaced by log)
        NN = list(range(2, int(math.exp(2 * a)) + 1))
        def f(r):
            v = arch(r)
            for n in NN: v = v - 2 * math.log(n) / math.sqrt(n) * np.cos(r * math.log(n))
            return v
        return f, True
    if name == 'prolate':       # energy outside the band |r| < 12
        return (lambda r: (np.abs(r) > 12).astype(float)), False
    if name == 'abs':           # |r| (Cauchy-type)
        return (lambda r: np.abs(r)), False
    raise ValueError(name)

K, R, STEP = 60, 3000.0, 0.01
def ground(name, delta):
    a = delta / 2
    phi, pole = make_phi(name, a)
    rs = np.arange(STEP / 2, R, STEP)
    ph = phi(rs)
    w = (np.arange(K) * math.pi / a)
    B = np.empty((K, len(rs)))
    for k in range(K):
        B[k] = 2 * np.sin(rs * a) * (-1) ** k * rs / (rs ** 2 - w[k] ** 2)
    G = (B * ph) @ B.T * STEP / math.pi
    # tail: int_R^inf Phi/r^2, with Phi evaluated on a log grid
    tr = np.exp(np.linspace(math.log(R), math.log(R) + 12, 4000))
    tail = np.trapezoid(phi(tr) / tr ** 2, tr)
    sgn = (-1.0) ** (np.arange(K)[:, None] + np.arange(K)[None, :])
    G += 2 * sgn * tail / math.pi
    if pole:
        p = np.array([(2 * np.sinh(0.5 * a) * 0.5 / (0.25 + x * x) * math.cos(0) if False else 0) for x in w])
        # pole vector p_k = int cos(w_k t) e^{t/2} dt over [-a, a] = Re[2 sinh((1/2 + i w_k) a)/(1/2 + i w_k)]
        p = np.array([(2 * np.sinh((0.5 + 1j * x) * a) / (0.5 + 1j * x)).real for x in w])
        G += 2 * np.outer(p, p)
    N = np.diag([2 * a] + [a] * (K - 1))
    ev, V = eigh(G, N)
    c = V[:, 0]
    c = c / c.sum() if abs(c.sum()) > 1e-300 else c    # g(0) = 1
    return c, ev[0], a

def gh(c, a, x):
    w = np.arange(K) * math.pi / a
    s = np.sin(x * a); co = np.cos(x * a)
    S = np.sum(c * (-1.0) ** np.arange(K) * x / (x * x - w ** 2))
    D = np.sum(c * (-1.0) ** np.arange(K) * (-(x * x + w ** 2)) / (x * x - w ** 2) ** 2)
    return 2 * s * S, 2 * (a * co * S + s * D)

def zeros(c, a, Rz=60.0):
    xs = np.arange(0.00731, Rz, 0.005); v = np.array([gh(c, a, x)[0] for x in xs]); out = []
    for i in np.nonzero(v[:-1] * v[1:] < 0)[0]:
        lo, hi = xs[i], xs[i + 1]; flo = v[i]
        for _ in range(60):
            m = (lo + hi) / 2; fm = gh(c, a, m)[0]
            if (fm < 0) == (flo < 0): lo, flo = m, fm
            else: hi = m
        out.append((lo + hi) / 2)
    return out

if __name__ == "__main__":
    name = sys.argv[1]; h = 1e-3
    for d in map(float, sys.argv[2:]):
        c0, l0, a = ground(name, d); cp, _, ap = ground(name, d + h); cm, _, am = ground(name, d - h)
        z0, zp, zm = zeros(c0, a), zeros(cp, ap), zeros(cm, am)
        vel = []
        for x in z0:
            xp = min(zp, key=lambda y: abs(y - x)) if zp else float('nan')
            xm = min(zm, key=lambda y: abs(y - x)) if zm else float('nan')
            vel.append((xp - xm) / (2 * h))
        npos = nneg = 0
        for x in np.arange(0.00731, 60, 0.01):
            f, fx = gh(c0, a, x); fp, fpx = gh(cp, ap, x); fm, fmx = gh(cm, am, x)
            W = f * (fpx - fmx) / (2 * h) - (fp - fm) / (2 * h) * fx
            npos += W > 0; nneg += W < 0
        print(json.dumps(dict(symbol=name, seed=os.environ.get('SEED', '12345'), jitter=JIT, wjitter=WJ, delta=d, lam=float(l0), n_zeros=len(z0),
            zeros=[round(x, 4) for x in z0[:12]], velocities=['%.3g' % v for v in vel[:12]],
            n_up=int(sum(v > 0 for v in vel)), n_down=int(sum(v < 0 for v in vel)),
            W_pos=int(npos), W_neg=int(nneg))))
        sys.stdout.flush()
