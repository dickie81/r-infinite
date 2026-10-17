# WARNING (round 23): double precision. Weil-form eigenvalues fall below 1e-5 from delta ~ 0.9
# (9.4e-7 at delta = 1, 6.3e-30 at delta = 2), which this discretisation cannot resolve: its
# "ground states" there are wrong states and its low eigenvalues a numerical floor. Use the paper's
# Gram at >= 500 bits (frontier/gap_hp.py, frontier/rerun_paper.py) for delta >~ 0.9.
import numpy as np, json, sys
from scipy.optimize import brentq
exec(open('hrr_test.py').read().split('if __name__')[0])
def full(a, n, R=60):
    t, g, h, ev = ground_state(a, n)
    if g.sum() < 0: g = -g
    xs = np.linspace(1e-6, R, 120000); Gr = G(xs, t, g).real
    sc = np.where(np.sign(Gr[:-1]) != np.sign(Gr[1:]))[0]
    rz = np.array([brentq(lambda x: G(x, t, g).real[0], xs[i], xs[i+1], xtol=1e-12) for i in sc])
    th = np.linspace(0, 2*np.pi, 400001)
    wind = int(np.round(np.sum(np.diff(np.unwrap(np.angle(G(R*np.exp(1j*th), t, g)))))/(2*np.pi)))
    gam = GAM[GAM < R - 5]
    near = np.array([rz[np.argmin(np.abs(rz - gm))] for gm in gam])
    err = near - gam
    kap = ((t**2 + h*h/12)*g).sum()/(2*g.sum())
    return dict(a=a, n=n, lam=ev[:2].tolist(), all_real=(wind == 2*len(rz)), n_zeros=len(rz),
                n_gamma=len(gam), max_abs_err=float(np.abs(err).max()),
                errs=err.round(5).tolist(), eta=float(np.abs(near**-2 - gam**-2).sum()),
                kappa=kap, S2=S2)
for spec in sys.argv[2:]:
    a, n = spec.split(':'); r = full(float(a), int(n))
    print(json.dumps(r)); sys.stdout.flush()
