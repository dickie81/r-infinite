import sys, os, math, importlib, json
import numpy as np
from scipy.linalg import eigh
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
name, delta, K = sys.argv[1], float(sys.argv[2]), int(sys.argv[3])
U = importlib.import_module("universality"); U.K = K; U.RETURN_GRAM = True
G, N, a = U.ground(name, delta); ev, V = eigh(G, N); c = V[:, 0]
w = np.arange(K) * math.pi / a
ghc = lambda z: 2 * np.sin(z * a) * np.sum(c * (-1.0) ** np.arange(K) * z / (z * z - w ** 2))
ys = np.linspace(0.01, 60, 60000); v = np.array([ghc(1j * y).real for y in ys])
imag_zeros = [float(ys[i]) for i in np.nonzero(v[:-1] * v[1:] < 0)[0]]
gv = [sum(c[k] * math.cos(k * math.pi * u / a) for k in range(K)) for u in np.linspace(0, a, 400)]
print(json.dumps(dict(symbol=name, seed=os.environ.get("SEED"), delta=delta, K=K, lam1=float(ev[0]),
     imaginary_zeros=imag_zeros, g_changes_sign=bool(min(gv) * max(gv) < 0))))
