"""Semi-discrete potential-theory model at a physical delta.
Probe: ghat(r) = prod_{zeta<T}(1 - r^2/gamma^2) * prod_{own}(1 - r^2/z^2) * prod_{k>=K0}(1 - r^2/(k pi/a)^2).
Envelope: u(r) = sum_{zeta<T} ln|1 - r^2/gamma^2|  [exact, discrete]
              + int ln|1 - r^2/t^2| m(t) dt        [own zeros, density m >= 0, continuum]
              - (a/pi) int_0^{Y T0} ln|1 - r^2/t^2| dt   [the Nyquist grid removed below Y T0]
              + ln|sin(ar)/(ar)|                   [O(log), dropped].
LP: maximise u(x0) - s subject to u(x_j) <= s for x_j beyond the band, m >= 0,
    K_zeta + int m <= K0 - 1 (net deficit >= 1 so the probe is L^2).
Reports f = -(ln lambda_1)/e^delta predicted = 2 (u(x0) - s)/e^delta (norm ~ e^{2u(x0)}, residual ~ e^{2s}).
Usage: lw_semidiscrete.py <delta> [X ...]
"""
import sys, os, json, math, numpy as np
from scipy.optimize import linprog
from lw_lp import Kcell, G
ZEROS = np.array(json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkpoints", "zeta_zeros_2000.json"))))

def model(delta, X, Ymax=40.0, ny_out=400, ny_in=150, allow_inside=True, x0=0.0):
    a = delta/2; T0 = 2*math.pi*math.exp(delta); T = X*T0; Y = Ymax*T0
    zin = ZEROS[ZEROS < T]; Kz = len(zin)
    K0 = int(a*Y/math.pi) + 1
    # cells for own-zero density (in r units): inside [0, T] linear, outside (T, Y] geometric
    ei = np.linspace(0, T, ny_in + 1); eo = T*np.geomspace(1, Y/T, ny_out + 1)
    edges = np.concatenate([ei, eo[1:]]); r1, r2 = edges[:-1], edges[1:]; nc = len(r1); dr = r2 - r1
    inside = r2 <= T + 1e-9
    # constraint points beyond the band: edges, mid, quarter points of outside cells + near-edge + far
    xo = np.unique(np.concatenate([eo[1:], 0.5*(eo[1:] + eo[:-1]), 0.25*eo[1:] + 0.75*eo[:-1], 0.75*eo[1:] + 0.25*eo[:-1], T*(1 + np.geomspace(1e-5, 1e-2, 40)), np.geomspace(Y, 20*Y, 60)]))
    def fixed(x):   # discrete zeta sum minus the Nyquist-grid integral on [0, Y]
        return float(np.sum(np.log(np.abs(1 - x*x/(zin*zin))))) - (a/math.pi)*float(Kcell(x, np.array([0.0]), np.array([Y]))[0])
    Kout = np.array([Kcell(x, r1, r2) for x in xo]); fo = np.array([fixed(x) for x in xo])
    K0v = Kcell(x0, r1, r2); f0 = fixed(x0)
    c = np.concatenate([-K0v, [1.0]])
    A = np.hstack([Kout, -np.ones((len(xo), 1))]); b = -fo
    A = np.vstack([A, np.concatenate([dr, [0.0]])]); b = np.concatenate([b, [K0 - 1 - Kz]])
    bounds = [(0.0, None if (allow_inside or not inside[k]) else 0.0) for k in range(nc)] + [(None, None)]
    res = linprog(c, A_ub=A, b_ub=b, bounds=bounds, method="highs")
    if res.status != 0: return None
    m = res.x[:nc]; s = res.x[-1]; u0 = f0 + K0v @ m
    return dict(f=2*(u0 - s)/math.exp(delta), lnlam=-2*(u0 - s), u0=u0, s=s, m=m, r1=r1, r2=r2, Kz=Kz, K0=K0, a=a, T0=T0, T=T, Y=Y, fixed=fixed)

def envelope_of(delta, X, dens_cells):
    """u(x) for a prescribed own-zero density given as (r1, r2, m) cells -- used to validate against a constructed probe."""
    pass

if __name__ == "__main__":
    delta = float(sys.argv[1]); Xs = [float(v) for v in sys.argv[2:]] or [1.6, 1.8, 2.0, 2.2, 2.4]
    for X in Xs:
        r = model(delta, X)
        if r is None: print(f"X {X}: LP failed"); continue
        mo = r["m"][r["r2"] > r["T"] + 1e-9]; ro = r["r1"][r["r2"] > r["T"] + 1e-9]
        nyq = r["a"]/math.pi
        print(f"delta {delta} X {X:4.2f}: predicted ln lambda_1 = {r['lnlam']:9.3f}  f = {r['f']:7.3f}   (K_zeta {r['Kz']}, K0 {r['K0']}, own zeros {float(np.sum(r['m']*(r['r2']-r['r1']))):.1f}; own density just beyond the edge / Nyquist: " + ", ".join(f"{m_/nyq:.2f}" for m_ in mo[:6]) + ")", flush=True)
