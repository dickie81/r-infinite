"""Continuum (delta -> infinity) LP with the in-band constraint made exact:
maximise phi(x0) - s  s.t.  phi(x_j) <= s (x_j beyond X),  phi(x_i) <= phi(x0) (x_i inside),
d rho >= ln y dy on [0, X] (extra zeros e >= 0), free density beyond X (>= -dmin), net count <= 0.
Scans x0 and X; reports f = 2 (phi(x0) - s) against 4 pi."""
import sys, math, numpy as np
from scipy.optimize import linprog
from lw_lp import Kcell, G

def solve(X, x0, Ymax=60.0, ny_in=400, ny_out=800, dmin=50.0):
    yi = np.linspace(0, X, ny_in + 1); yo = X*np.geomspace(1, Ymax/X, ny_out + 1)
    edges = np.concatenate([yi, yo[1:]]); y1, y2 = edges[:-1], edges[1:]; nc = len(y1); dy = y2 - y1
    inside = y2 <= X + 1e-12
    base = np.where(inside, (G(y2) - G(y1))/dy, 0.0)
    lb = np.where(inside, 0.0, -dmin)
    xo = np.unique(np.concatenate([yo[1:], 0.5*(yo[1:] + yo[:-1]), 0.25*yo[1:] + 0.75*yo[:-1], 0.75*yo[1:] + 0.25*yo[:-1], X*(1 + np.geomspace(1e-6, 1e-2, 60)), np.geomspace(Ymax, 50*Ymax, 80)]))
    xi = np.linspace(0, X, 400)
    Kout = np.array([Kcell(x, y1, y2) for x in xo]); Kin = np.array([Kcell(x, y1, y2) for x in xi]); K0 = Kcell(x0, y1, y2)
    c = np.concatenate([-K0, [1.0]])
    A1 = np.hstack([Kout, -np.ones((len(xo), 1))]); b1 = -(Kout @ base)
    A2 = np.hstack([Kin - K0[None, :], np.zeros((len(xi), 1))]); b2 = -((Kin - K0[None, :]) @ base)
    A3 = np.concatenate([dy, [0.0]])[None, :]; b3 = np.array([-(base*dy).sum()])
    A = np.vstack([A1, A2, A3]); b = np.concatenate([b1, b2, b3])
    bounds = [(lb[k], None) for k in range(nc)] + [(None, None)]
    res = linprog(c, A_ub=A, b_ub=b, bounds=bounds, method="highs")
    if res.status != 0: return None
    e = res.x[:nc]; s = res.x[-1]; phi0 = K0 @ (base + e)
    return 2*(phi0 - s), base + e, y1, y2

if __name__ == "__main__":
    print("4 pi =", 4*math.pi)
    for X in (1.9, 1.95, 2.0, 2.05, 2.1):
        row = []
        for x0 in (0.0, 0.1, 0.2, 0.4):
            r = solve(X, x0); row.append(f"x0 {x0}: {r[0]:.4f}" if r else f"x0 {x0}: fail")
        print(f"X {X:4.2f} | " + " | ".join(row), flush=True)
