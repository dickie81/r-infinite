import numpy as np, sys
from numpy.polynomial import legendre as Lg
from numpy.polynomial.legendre import leggauss
from slweak import report
def legfuncs(M, a, t, gen):
    """eigenfunctions (sorted) of a symmetric matrix gen(Mmat) in normalized Legendre basis on s=t/a"""
    xs, ws = leggauss(200)
    P = np.array([Lg.legval(xs, np.eye(M)[n])*np.sqrt((2*n+1)/2) for n in range(M)])
    H = gen(P, xs, ws)
    E, V = np.linalg.eigh(H)
    return E, V
a, M = 0.8, 60; c = float(sys.argv[1]) if len(sys.argv) > 1 else 6.0; cp = c*a
def gen(P, xs, ws):
    S = (P*ws*xs**2) @ P.T
    return np.diag([n*(n+1) for n in range(M)]) + cp**2*S
E, V = legfuncs(M, a, None, gen)
x, _ = leggauss(4000); t = a*x
funcs = []
for j in range(6):
    d = V[:, j]*np.array([np.sqrt((2*n+1)/2) for n in range(M)])
    v = Lg.legval(x, d)/np.sqrt(a); dv = Lg.legval(x, Lg.legder(d))/np.sqrt(a)/a
    kind = "even" if j % 2 == 0 else "odd"
    funcs.append((kind, v, dv))
report(f"prolate(Legendre) c={c}", funcs, a, 60, 2)
