"""Landau-Widom / potential-theory reduction of the slack law's constant.

For a real even probe ghat of exponential type a with real zeros (Laguerre-Polya
class, as the prolate is), Hadamard gives ln|ghat(r)| = const + int ln|1 - r^2/t^2| dM(t)
with M the probe's zero count on (0, t).  A uniform density a/pi contributes a flat
envelope (int_0^inf ln|1 - r^2/t^2| dt = 0), so with D = M - (a/pi) t the envelope is
u(r) = int ln|1 - r^2/t^2| dD(t) + O(log).  In horizon units r = T0 x, t = T0 y, and
with D = e^delta rho, u = e^delta phi(x), phi(x) = int ln|1 - x^2/y^2| d rho(y):
scale-free.  The zeta zeros force d rho >= d rho_N = ln y dy on the dodging band
[0, X] (N(T0 y) = e^delta y (delta + ln y - 1) against Nyquist e^delta delta y);
beyond X the probe's zeros are its own.  Then, at exponential accuracy,
    -ln lambda_1 / e^delta  ->  f_inf = 2 [ max_{x<=X} phi - sup_{x>X} phi ]
(norm from the envelope's peak inside the band, the residual from its supremum
over the zero region beyond the band).  This script evaluates the simplest
admissible probe -- exactly the zeta zeros on [0, X], Nyquist density beyond --
and optimises X; then adds freedom beyond X (a deficit ramp) and inside (extra zeros).
"""
import math, numpy as np
from scipy.integrate import quad
from scipy.optimize import minimize_scalar, minimize

def phi_N(x, X):
    """int_0^X ln|1 - x^2/y^2| ln y dy  (the zeta-zero deviation on [0, X])."""
    f = lambda y: math.log(abs(1 - x*x/(y*y)))*math.log(y)
    pts = [x] if 0 < x < X else []
    return quad(f, 1e-12, X, points=pts, limit=400)[0]

def f_simple(X, grid=400):
    xs_in = np.linspace(1e-3, X, grid)
    xs_out = np.concatenate([X*(1 + np.geomspace(1e-4, 1, grid)), X*np.geomspace(2, 1e4, grid)])
    pin = max(phi_N(x, X) for x in xs_in)
    pout = max(phi_N(x, X) for x in xs_out)
    return 2*(pin - pout), pin, pout

if __name__ == "__main__":
    print("simplest probe: zeta zeros on [0, X], Nyquist beyond")
    for X in (0.6, 0.8, 1.0, 1.2, 1.5, 1.8, 2.0, 2.2, 2.5, 2.7):
        f, pin, pout = f_simple(X)
        print(f"  X {X:4.2f}: f = {f:8.4f}   (phi_in max {pin:8.4f}, phi_out sup {pout:8.4f})", flush=True)
