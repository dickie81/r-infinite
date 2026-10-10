import numpy as np, sys
from numpy.polynomial import legendre as Lg
from numpy.polynomial.legendre import leggauss
from slweak import report
a, M = 0.8, 50; sig = float(sys.argv[1])
xs, ws = leggauss(300)
P = np.array([Lg.legval(xs, np.eye(M)[n])*np.sqrt((2*n+1)/2) for n in range(M)])
Kk = np.exp(-(a*(xs[:, None] - xs[None, :]))**2/(2*sig**2))*a
H = (P*ws) @ Kk @ (P*ws).T
E, V = np.linalg.eigh(H); order = np.argsort(-E)
x, _ = leggauss(4000); t = a*x; funcs = []
for j in order[:6]:
    d = V[:, j]*np.array([np.sqrt((2*n+1)/2) for n in range(M)])
    v = Lg.legval(x, d)/np.sqrt(a); dv = Lg.legval(x, Lg.legder(d))/np.sqrt(a)/a
    kind = "even" if abs(Lg.legval(0.3, d) - Lg.legval(-0.3, d)) < 1e-8*abs(Lg.legval(0.3, d)) + 1e-14 else "odd"
    funcs.append((kind, v, dv))
print([f[0] for f in funcs])
report(f"gauss sigma={sig}", funcs, a, 60, 3)
