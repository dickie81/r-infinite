import sys, os, math, importlib, json
import numpy as np
from scipy.linalg import eigh
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."))
U = importlib.import_module("universality"); U.RETURN_GRAM = True
name = sys.argv[1]
for delta in np.arange(float(sys.argv[2]), float(sys.argv[3]) + 1e-9, float(sys.argv[4])):
    G, N, a = U.ground(name, delta); ev, V = eigh(G, N); c = V[:, 0]; K = len(c)
    g = lambda u: sum(c[k] * math.cos(k * math.pi * u / a) for k in range(K))
    g0 = g(0.0); c = c / g0                                   # sign: g(0) = 1
    w = np.arange(K) * math.pi / a
    ghc = lambda z: 2 * np.sin(z * a) * np.sum(c * (-1.0) ** np.arange(K) * z / (z * z - w ** 2))
    ys = np.linspace(0.01, 40, 8000); v = np.array([ghc(1j * y).real for y in ys])
    nim = int(np.sum(v[:-1] * v[1:] < 0))
    print(json.dumps(dict(delta=round(float(delta), 3), gap=float((ev[1] - ev[0]) / abs(ev[0])), ghat0=float(2 * a * c[0]),
          g_edge=float(sum(c[k] * (-1) ** k for k in range(K))), imaginary_zero_pairs=nim)), flush=True)
