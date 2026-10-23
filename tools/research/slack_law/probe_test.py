"""Decisive test of the potential-theory reduction: build the explicit real-zero
probe prescribed by the LP's optimal zero distribution (zeta zeros below X T0,
the LP's own-zero density beyond, a Nyquist grid past Y), evaluate its exact
Rayleigh quotient 2 pi Q / int|ghat|^2 at a physical delta, and compare with the
exact lambda_1 and with the reduction's prediction exp(-f e^delta).
Usage: probe_test.py <delta> <dps>
"""
import sys, os, json, math, time
import numpy as np
from mpmath import mp, mpf, sin, pi as mpi, log, exp, mpmathify

delta = float(sys.argv[1]); mp.dps = int(sys.argv[2])
LP = json.load(open(sys.argv[3] if len(sys.argv) > 3 else "lp_best.json")); X = LP["X"]; dens = np.array(LP["dens"]); y1 = np.array(LP["y1"]); y2 = np.array(LP["y2"])
ZEROS = json.load(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "checkpoints", "zeta_zeros_2000.json")))
a = delta/2; T0 = 2*math.pi*math.exp(delta); ed = math.exp(delta)
Tc = X*T0
zeta_in = [g for g in ZEROS if g < Tc]; K_zeta = len(zeta_in)
# own zeros beyond X: density per unit y = e^delta (delta + dens(y)); place at half-integers of the cumulative count
out = y2 > X + 1e-12
ys = []; cum = 0.0; k = 1
for lo, hi, d in zip(y1[out], y2[out], dens[out]):
    rate = ed*(delta + d)                      # zeros per unit y in this cell (>= 0 by the LP's bound)
    while cum + rate*(hi - lo) >= k - 0.5 and rate > 0:
        ys.append(lo + (k - 0.5 - cum)/rate); k += 1
    cum += rate*(hi - lo)
Y = float(y2[-1]); own = [y*T0 for y in ys]
# Nyquist continuation past Y: S(r) = prod_{k>=K0}(1 - r^2/(k pi/a)^2) = [sin(ar)/(ar)] / prod_{k<K0}(...), K0 pi/a ~ Y T0
K0 = int(a*Y*T0/math.pi) + 1
deficit = (K0 - 1) - K_zeta - len(own)         # net zero deficit below Y T0: need >= 1 for L^2
while deficit < 1: own.pop(); deficit += 1
print(f"delta {delta}: T0 {T0:.2f}, X {X}, zeta zeros dodged {K_zeta}, own zeros {len(own)} up to {Y:.0f} T0, Nyquist grid from K0 = {K0}; net deficit {deficit}", flush=True)
zeta_m = [mpf(g) for g in zeta_in]; own_m = [mpmathify(z) for z in own]
grid_m = [mpf(k)*mpi/mpf(a) for k in range(1, K0)]
am = mpf(a)
def ghat(r):
    r = mpmathify(r); r2 = r*r
    p = mpf(1)
    for z in zeta_m: p *= (1 - r2/(z*z))
    for z in own_m: p *= (1 - r2/(z*z))
    s = sin(am*r)/(am*r) if r != 0 else mpf(1)
    q = mpf(1)
    for z in grid_m: q *= (1 - r2/(z*z))
    return p*s/q
# Q over the listed zeros beyond the band
t0 = time.time()
Q = mpf(0)
for g in ZEROS:
    if g >= Tc: Q += ghat(g)**2
print(f"  zero sum done ({time.time()-t0:.0f}s): ln Q_list = {float(log(Q)):.3f}", flush=True)
# quadrature: |ghat|^2 on [0, 3 Tc] (dense) and log panels beyond to 200 gamma_max, with the density tail for Q
xg, wg = np.polynomial.legendre.leggauss(32)
def panel_int(lo, hi, weight=None):
    tot = mpf(0)
    for xx, ww in zip(xg, wg):
        r = (hi - lo)/2*xx + (hi + lo)/2; v = ghat(r)**2*mpf((hi - lo)/2*ww)
        tot += v*weight(r) if weight else v
    return tot
period = math.pi/a; npan = int(3*Tc/period*1.5) + 10
norm = mpf(0)
edges = np.linspace(0, 3*Tc, npan + 1)
for lo, hi in zip(edges[:-1], edges[1:]): norm += panel_int(lo, hi)
gmax = ZEROS[-1]
edges2 = np.geomspace(3*Tc, 200*gmax, 200)
tail_norm = mpf(0); tail_Q = mpf(0)
for lo, hi in zip(edges2[:-1], edges2[1:]):
    tail_norm += panel_int(lo, hi)
    if hi > gmax: tail_Q += panel_int(max(lo, gmax), hi, weight=lambda r: log(r/(2*mpi))/(2*mpi))
norm_tot = 2*(norm + tail_norm)                      # even: both half-lines
Qtot = Q + tail_Q
ray = 2*mpi*Qtot/norm_tot
print(f"  int|ghat|^2: band part {float(log(2*norm)):.3f}, tail part {float(log(2*tail_norm)):.3f} (ln); Q tail beyond gamma_2000: ln {float(log(tail_Q)) if tail_Q > 0 else float('-inf'):.3f}", flush=True)
print(f"  RAYLEIGH QUOTIENT ln(2 pi Q / int|ghat|^2) = {float(log(ray)):.3f}   | reduction's prediction -f e^delta = {-LP['f']*ed:.3f}   | exact lambda_1: see table", flush=True)
