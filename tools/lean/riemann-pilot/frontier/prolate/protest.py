"""Optimal jet in the Hermite variable x = sqrt(2 pi) e^u versus the Slepian prolate psi_0 at c = xi^2 = 2X."""
import pickle, sys, mpmath as mp, numpy as np
from scipy.special import pro_ang1
S = pickle.load(open(sys.argv[1], "rb")); mp.mp.dps = S["dps"]
A = mp.matrix([[mp.mpf(x) for x in r] for r in S["A"]]); B = mp.matrix([[mp.mpf(x) for x in r] for r in S["B"]])
J = A.rows; a = mp.mpf(S["delta"])/2; X = mp.pi*mp.e**(2*a); xi = mp.sqrt(2*X); c = float(2*X)
L = mp.cholesky(B); Li = mp.inverse(L); E, V = mp.eigsy((Li*A*Li.T + (Li*A*Li.T).T)/2)
i0 = min(range(J), key=lambda i: E[i]); p = Li.T*V[:, i0]
polys = [[mp.mpf(0), mp.mpf(-3), mp.mpf(2)]]
for _ in range(2*J):
    cc = polys[-1]; new = [mp.mpf(0)]*(len(cc)+1)
    for j, cj in enumerate(cc):
        if j > 0: new[j] += 2*j*cj
        new[j] += cj/2; new[j+1] += -2*cj
    polys.append(new)
def f(x):  # n=1 piece, up to a constant: sum_k p_k poly_{2k}(x^2/2) e^{-x^2/2}
    q = x*x/2
    return mp.fsum(p[k]*mp.polyval(polys[2*k][::-1], q) for k in range(J))*mp.e**(-q)
xs = np.linspace(0.0, float(xi), 400)
fv = np.array([float(f(mp.mpf(x))) for x in xs])
pv = np.array([pro_ang1(0, 0, c, min(x/float(xi), 1-1e-12))[0] for x in xs])
fv /= np.sqrt(np.trapezoid(fv**2, xs)); pv /= np.sqrt(np.trapezoid(pv**2, xs))
if np.dot(fv, pv) < 0: pv = -pv
print(f"delta={S['delta']} X={float(X):.2f} xi={float(xi):.3f} c={c:.1f}")
print("  L2[0,xi] cosine(opt jet, prolate psi_0) =", round(float(np.trapezoid(fv*pv, xs)), 6))
g = np.array([np.exp(-x*x/2) for x in xs]); g /= np.sqrt(np.trapezoid(g**2, xs))
print("  cosine(opt jet, Gaussian e^{-x^2/2})     =", round(float(np.trapezoid(fv*g, xs)), 6))
print("  cosine(prolate, Gaussian)                =", round(float(np.trapezoid(pv*g, xs)), 6))
for x in [0, 0.25, 0.5, 0.75, 0.9, 1.0]:
    i = min(int(x*399), 399); print(f"   x/xi={x:4.2f}  jet {fv[i]:+.4e}  prolate {pv[i]:+.4e}")
