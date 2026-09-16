"""LP optimisation (variables are DENSITIES per cell; phi(x) = sum_k Kcell(x, cell_k) * density_k)
 of the reduced (potential-theory) problem: maximise
   f = 2 [ phi(x0) - s ],  phi(x_j) <= s for every x_j beyond the band,
over the probe's zero-deviation measure d rho on a y-grid, with
   d rho >= ln y dy on [0, X]  (must contain the zeta zeros), free beyond X,
   rho(Y_max) <= 0            (no net zero excess at infinity -> decaying envelope).
Cell-integrated kernel: int_{y1}^{y2} ln|1 - x^2/y^2| dy = [G(y-x) + G(y+x) - 2G(y)],
G(z) = z ln|z| - z.  Exact per cell, no singularity handling needed.
"""
import math, sys, numpy as np
from scipy.optimize import linprog

def G(z):
    z = np.asarray(z, dtype=float); out = np.zeros_like(z); nz = z != 0
    out[nz] = z[nz]*np.log(np.abs(z[nz])) - z[nz]; return out

def Kcell(x, y1, y2):
    return (G(y2 - x) + G(y2 + x) - 2*G(y2)) - (G(y1 - x) + G(y1 + x) - 2*G(y1))

def solve(X, x0, Ymax=40.0, ny_in=300, ny_out=300, nx_out=600, extra_inside=True, free_outside=True, verbose=False, dmin=50.0):
    # y cells: inside [0, X] and outside (X, Ymax] (log-spaced outside)
    yi = np.linspace(0, X, ny_in + 1)
    yo = X*np.geomspace(1, Ymax/X, ny_out + 1)
    edges = np.concatenate([yi, yo[1:]])
    y1, y2 = edges[:-1], edges[1:]; nc = len(y1)
    inside = y2 <= X + 1e-12
    # baseline (zeta) deviation per inside cell: int ln y dy
    dy = y2 - y1
    base = np.where(inside, (G(y2) - G(y1))/dy, 0.0)       # zeta deviation DENSITY per cell: (1/dy) int ln y dy
    # variables: e_k (extra measure per cell), s.  rho cell mass = base_k + e_k
    # bounds: inside e_k >= 0 (only extra zeros; or 0 if not extra_inside); outside e_k free (>= -BIG) or 0
    lb = np.where(inside, 0.0, -dmin if free_outside else 0.0)
    ub = np.where(inside, (np.inf if extra_inside else 0.0), (np.inf if free_outside else 0.0))
    # x points beyond the band where phi <= s
    yo_mid = 0.5*(yo[1:] + yo[:-1])
    xo = np.unique(np.concatenate([yo[1:], yo_mid, 0.25*yo[1:] + 0.75*yo[:-1], 0.75*yo[1:] + 0.25*yo[:-1], X*(1 + np.geomspace(1e-5, 1e-2, 40)), np.geomspace(Ymax, 20*Ymax, 60)]))
    Kout = np.array([Kcell(x, y1, y2) for x in xo])            # nx_out x nc
    K0 = Kcell(x0, y1, y2)                                      # phi(x0) coefficients
    # objective: maximise K0.e - s  (constant K0.base dropped, added back)  -> minimise -K0.e + s
    c = np.concatenate([-K0, [1.0]])
    A = np.hstack([Kout, -np.ones((len(xo), 1))]); b = -(Kout @ base)     # Kout.(base+e) - s <= 0
    # net count: sum(base + e) <= 0
    A = np.vstack([A, np.concatenate([dy, [0.0]])]); b = np.concatenate([b, [-(base*dy).sum()]])
    bounds = [(lb[k], None if np.isinf(ub[k]) else ub[k]) for k in range(nc)] + [(None, None)]
    res = linprog(c, A_ub=A, b_ub=b, bounds=bounds, method="highs")
    if res.status != 0: return None
    e = res.x[:nc]; s = res.x[-1]
    phi0 = K0 @ (base + e)
    return 2*(phi0 - s), e, base, y1, y2, s, phi0

def report(X, dmin, ny_out=300):
    r = solve(X, 0.0, ny_out=ny_out, extra_inside=True, free_outside=True, dmin=dmin)
    f, e, base, y1, y2, s_, phi0 = r
    dens = base + e; out = y2 > X
    # summarise the outside density profile: where the LP put deficits / excesses
    seg = [(y1[k], y2[k], dens[k]) for k in range(len(y1)) if out[k] and abs(dens[k]) > 1e-6]
    return f, seg

if __name__ == "__main__" and len(sys.argv) > 1 and sys.argv[1] == "refined":
    for X in (2.0, 2.35, 2.5):
        for dmin in (2.0, 3.0, 4.0, 8.0, 50.0):
            for ny_out in (300, 600):
                f, seg = report(X, dmin, ny_out)
                neg = sum((b - a)*d for a, b, d in seg if d < 0); pos = sum((b - a)*d for a, b, d in seg if d > 0)
                print(f"X {X:4.2f} deficit-density bound {dmin:4.1f} ny_out {ny_out}: f = {f:8.4f}   outside deficit total {neg:7.3f}, excess total {pos:7.3f}; first cells: " + ", ".join(f"[{a:.2f},{b:.2f}]:{d:+.2f}" for a, b, d in seg[:4]), flush=True)
    sys.exit()

if __name__ == "__main__":
    Xs = [float(v) for v in sys.argv[1:]] or [1.8, 2.0, 2.2, 2.35, 2.5]
    for X in Xs:
        for x0 in (0.0, 0.3*X, 0.6*X, 0.9*X):
            r0 = solve(X, x0, extra_inside=False, free_outside=False)
            r1 = solve(X, x0, extra_inside=True, free_outside=False)
            r2 = solve(X, x0, extra_inside=False, free_outside=True)
            r3 = solve(X, x0, extra_inside=True, free_outside=True)
            print(f"X {X:5.2f} x0 {x0:5.2f} | simple {r0[0]:8.4f} | +extra inside {r1[0]:8.4f} | +free outside {r2[0]:8.4f} | both {r3[0]:8.4f}", flush=True)
