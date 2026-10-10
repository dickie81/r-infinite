"""Pointwise check of the envelope reduction: the constructed probe's actual
2 ln|ghat(r)| (envelope: max over a Nyquist period) against 2 e^delta phi(r/T0)
from the cell-integrated potential of the prescribed zero density.
Usage: probe_profile.py <delta> <dps> <lp json>"""
import sys, os, json, math, numpy as np
from mpmath import mp, mpf, sin, pi as mpi, log, mpmathify
from lw_lp import Kcell
delta = float(sys.argv[1]); mp.dps = int(sys.argv[2]); LP = json.load(open(sys.argv[3]))
X = LP["X"]; dens = np.array(LP["dens"]); y1 = np.array(LP["y1"]); y2 = np.array(LP["y2"])
ZEROS = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkpoints", "zeta_zeros_2000.json"))); a = delta/2; T0 = 2*math.pi*math.exp(delta); ed = math.exp(delta); Tc = X*T0
zeta_in = [g for g in ZEROS if g < Tc]
out = y2 > X + 1e-12; ys = []; cum = 0.0; k = 1
for lo, hi, d in zip(y1[out], y2[out], dens[out]):
    rate = ed*(delta + d)
    while rate > 0 and cum + rate*(hi - lo) >= k - 0.5: ys.append(lo + (k - 0.5 - cum)/rate); k += 1
    cum += rate*(hi - lo)
Y = float(y2[-1]); own = [y*T0 for y in ys]; K0 = int(a*Y*T0/math.pi) + 1
deficit = (K0 - 1) - len(zeta_in) - len(own)
while deficit < 1: own.pop(); deficit += 1
zm = [mpf(g) for g in zeta_in] + [mpmathify(z) for z in own]; gm = [mpf(k)*mpi/mpf(a) for k in range(1, K0)]; am = mpf(a)
def ghat(r):
    r = mpmathify(r); r2 = r*r; p = mpf(1)
    for z in zm: p *= (1 - r2/(z*z))
    q = mpf(1)
    for z in gm: q *= (1 - r2/(z*z))
    return p*(sin(am*r)/(am*r))/q
def env(x):
    r0 = x*T0; best = None
    for r in np.linspace(r0, r0 + math.pi/a, 25):
        v = abs(ghat(r))
        if v > 0 and (best is None or v > best): best = v
    return 2*float(log(best))
def phi(x): return float(np.dot(Kcell(x, y1, y2), dens))
print(f"delta {delta}, X {X}: actual 2ln|ghat| envelope vs 2 e^delta phi(x) [the reduction]; zeta part alone: 2 e^delta * int_0^X ln|1-x^2/y^2| ln y dy")
from lw_variational import phi_N
for x in (0.1, 0.3, 0.5, 0.8, 1.0, 1.3, 1.6, 1.9, 2.05, 2.2, 2.5, 2.8, 3.2, 4.0, 6.0, 10.0):
    print(f"  x {x:5.2f}: actual {env(x):9.2f}   reduction {2*ed*phi(x):9.2f}   zeta-only {2*ed*phi_N(x, X):9.2f}", flush=True)
