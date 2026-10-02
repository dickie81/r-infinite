"""Round 31, widened family: L = -d/dt(p dt) + q with p = (a^2 - t^2)(1 + sum_{m=1..3} p_m t^{2m}),
q = sum_{m=1..8} q_m t^{2m}; least squares for all 11 coefficients (L is linear in them)."""
import sys, math, json
import numpy as np
from numpy.polynomial.legendre import leggauss
from scipy.linalg import eigh
sys.path.insert(0, 'debr')
import universality as U
U.RETURN_GRAM = True
K = U.K; Ks = 30
def run(name, delta):
    G, N, a = U.ground(name, delta)
    x, w = leggauss(6000); t = a * x; w = a * w
    om = np.arange(K) * math.pi / a
    C = np.cos(np.outer(om, t)); S = np.sin(np.outer(om, t)) * om[:, None]
    Nih = np.diag(1 / np.sqrt(np.diag(N)))
    base = Nih @ ((S * ((a * a - t * t) * w)) @ S.T) @ Nih
    terms = [Nih @ ((S * ((a * a - t * t) * t ** (2 * m) * w)) @ S.T) @ Nih for m in (1, 2, 3)] + \
            [Nih @ ((C * (t ** (2 * m) * w)) @ C.T) @ Nih for m in range(1, 9)]
    Gh = Nih @ G @ Nih
    sub = slice(0, Ks)
    comm = lambda A, B: (A @ B - B @ A)[sub, sub].ravel()
    A = np.stack([comm(Gh, T) for T in terms], axis=1); b = -comm(Gh, base)
    sc = np.linalg.norm(A, axis=0); cs, *_ = np.linalg.lstsq(A / sc, b, rcond=None); cv = cs / sc
    Lh = base + sum(c * T for c, T in zip(cv, terms))
    res = np.linalg.norm(A @ cv - b) / np.linalg.norm(b)
    ev, V = eigh(Lh); Vs = V[:, :Ks]; Gt = Vs.T @ Gh @ Vs
    off = np.linalg.norm(Gt - np.diag(np.diag(Gt))) / np.linalg.norm(Gt - np.mean(np.diag(Gt)) * np.eye(Ks))
    g0 = eigh(Gh)[1][:, 0]; ov = np.abs(V.T @ g0)
    return dict(symbol=name, delta=delta, rel_residual=float(res), offdiag=float(off), overlap=float(ov.max()))
for name in sys.argv[1].split(','):
    for d in map(float, sys.argv[2:]):
        print(json.dumps(run(name, d))); sys.stdout.flush()
