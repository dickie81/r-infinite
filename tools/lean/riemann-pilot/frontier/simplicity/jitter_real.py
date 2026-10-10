"""Round 42 check: when jittered primes break the monotone zero flow (round 30), are the ground states still
simple, and are their transforms still real-rooted? Argument principle on |z| = R (complex zero count) against
sign changes on (0, R) (real zeros). Uses universality.py's Gram (double precision; |lambda| >= 1e-5 there)."""
import sys, os, json, math, importlib
import numpy as np
from scipy.linalg import eigh
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
name, delta = sys.argv[1], float(sys.argv[2])
U = importlib.import_module("universality")
U.RETURN_GRAM = True
G, N, a = U.ground(name, delta)
ev, V = eigh(G, N)
c = V[:, 0]
K = len(c)
w = np.arange(K) * math.pi / a
def ghc(z):
    return 2 * np.sin(z * a) * np.sum(c * (-1.0) ** np.arange(K) * z / (z * z - w ** 2))
R = 35.3
th = np.linspace(0, 2 * np.pi, 40001)
vals = np.array([ghc(R * np.exp(1j * t)) for t in th])
ntot = int(round(np.sum(np.diff(np.unwrap(np.angle(vals)))) / (2 * np.pi)))
real_pos = [z for z in U.zeros(c, a, Rz=R)]
print(json.dumps(dict(symbol=name, seed=os.environ.get("SEED"), delta=delta, lam1=float(ev[0]), lam2=float(ev[1]),
    gap_ratio=float((ev[1] - ev[0]) / abs(ev[0])), zeros_in_disc=ntot, real_zeros=2 * len(real_pos),
    nonreal=ntot - 2 * len(real_pos))))
