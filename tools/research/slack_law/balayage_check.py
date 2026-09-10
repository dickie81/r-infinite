"""Closed form of the slack-law constant (the equilibrium problem solved by balayage).
Scaled problem: sigma_0 = ln|y| dy on [-X, X] (the zeta-zero deviation from Nyquist), tau >= 0 on
E = {|x| >= X} with tau(E) <= -sigma_0(R); phi = U^{sigma_0+tau}(x) - U^{sigma_0+tau}(0),
f = -2 sup_E phi.  Candidate optimum: tau = -(balayage of sigma_0 onto E), which makes phi constant
on E, equal to s = int g_Omega(t, 0) d sigma_0(t), g the Green function of Omega = C \\ E with pole 0.
With the disk map w = z/(1 + sqrt(1 - z^2)) (z = t/X):  g(t, 0) = ln[(1 + sqrt(1 - t^2/X^2)) X / t],
s(X) = 2 int_0^X g ln t dt = X (pi ln X + 2B),  B = int_0^1 ln((1+sqrt(1-u^2))/u) ln u du = -(pi/2)(1 + ln 2),
so f(X) = -2 s(X) = -2X(pi ln X - pi(1 + ln 2)) = 2 pi X (1 + ln 2 - ln X), maximal at X = 2 with f = 4 pi.
This script checks every step numerically: B, the balayage density (positivity), the constancy of phi on E,
phi <= 0 inside, and f(X)."""
import math, numpy as np
from scipy.integrate import quad

def B_num():
    return quad(lambda u: math.log((1 + math.sqrt(1 - u*u))/u)*math.log(u), 0, 1, limit=400)[0]

def bal_density(x, X, n=4001):
    """density of -(balayage of sigma_0) at x in E (x > X), via the harmonic measure of the doubly slit plane:
    boundary point x = X / cos(theta); from w0 = w(t) the harmonic measure of d theta (both sides of the slit)
    is P(w0, theta)/pi d theta, P the Poisson kernel; dx = X sin(theta)/cos^2(theta) d theta."""
    th = math.acos(X/x); dx_dth = X*math.sin(th)/math.cos(th)**2
    ts = np.linspace(-X, X, n + 1)[1:-1]; zeta = ts/X
    w0 = zeta/(1 + np.sqrt(1 - zeta*zeta))
    P = (1 - w0*w0)/(1 - 2*w0*math.cos(th) + w0*w0)
    dens_theta = -np.trapezoid(P/math.pi*np.log(np.abs(ts)), ts)     # -(sigma_0 hat) per d theta
    return dens_theta/dx_dth                                        # per dx

def phi_of(x, X, tau_x, tau_w):
    """phi(x) = int ln|1 - x^2/y^2| [ln y dy on (0,X)] + sum tau_w ln|1 - x^2/tau_x^2|."""
    f = lambda y: math.log(abs(1 - x*x/(y*y)))*math.log(y)
    pts = [x] if 0 < x < X else []
    v = quad(f, 1e-12, X, points=pts, limit=400)[0]
    return v + float(np.sum(tau_w*np.log(np.abs(1 - x*x/(tau_x*tau_x)))))

if __name__ == "__main__":
    B = B_num(); print(f"B = {B:.10f}   -(pi/2)(1+ln2) = {-(math.pi/2)*(1 + math.log(2)):.10f}")
    for X in (1.5, 2.0, 2.5):
        # tau on (X, Ymax): quadrature nodes (log-spaced) with the balayage density
        Ymax = 2000*X
        edges = X*np.geomspace(1, Ymax/X, 3001); mids = 0.5*(edges[1:] + edges[:-1]); widths = np.diff(edges)
        dens = np.array([bal_density(m, X) for m in mids]); tau_w = dens*widths
        M = -2*(X*math.log(X) - X)                 # -sigma_0(R): the mass tau must carry
        print(f"X {X}: tau mass (one side, to {Ymax:.0f}) = {tau_w.sum():.5f} vs M/2 = {M/2:.5f}; min density on E = {dens.min():.4e} at x = {mids[dens.argmin()]:.3f}; density at edge {dens[0]:.4f}, at 2X {dens[np.searchsorted(mids, 2*X)]:.4f}")
        s_pred = X*(math.pi*math.log(X) + 2*B); f_pred = -2*s_pred; f_closed = 2*math.pi*X*(1 + math.log(2) - math.log(X))
        vals = [(x, phi_of(x, X, mids, tau_w)) for x in (X*1.001, X*1.05, X*1.3, 2*X, 4*X, 10*X, 100*X)]
        print(f"   phi on E: " + ", ".join(f"{v:.4f}" for _, v in vals) + f"   | predicted s = {s_pred:.4f}; f = {f_pred:.4f} (closed form {f_closed:.4f})")
        ins = [(x, phi_of(x, X, mids, tau_w)) for x in (0.01, 0.2, 0.5, 0.8, 1.0, 1.3, 1.6, 1.9, X*0.999)]
        print(f"   phi inside (must be <= 0): " + ", ".join(f"{v:.3f}" for _, v in ins))
    print(f"4 pi = {4*math.pi:.6f}")
