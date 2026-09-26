#!/usr/bin/env python3
"""Round 93 (E8 = the integral octonions; theta_E8 = (theta2^8 + theta3^8 + theta4^8)/2, zeta = 240 2^-s zeta(s) zeta(s-3)). Adapted from round 92: zeros of the discretised-d-ball zeta Xi_d(s) = s(s - d/2) Lambda_d(s), Lambda_d = pi^-s Gamma(s) sum' |m|^-2s over Z^d,
Lambda_d(s) = int_1^inf (theta^d - 1)(x^s + x^{d/2-s}) dx/x - 1/s - 1/(d/2 - s)  (theta(x) = sum_n e^{-pi n^2 x}).
Counts: N_line(T) = sign changes of Xi_d(d/4 + it), 0 < t <= T; N(T) = Delta_P arg Xi / pi - N_real/2 on the half contour
sigma1 -> sigma1 + iT -> d/4 + iT (sigma1 = d/2 + 2), N_real = real zeros in (d/2 - sigma1, sigma1).
Usage: klatticeball.py d T [check]"""
import sys, json, mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre
d, T = 8, float(sys.argv[2]); mp.mp.dps = int(25 + 0.75*T)
E8theta = lambda q: (mp.jtheta(2, 0, q)**8 + mp.jtheta(3, 0, q)**8 + mp.jtheta(4, 0, q)**8)/2
U, NP = mp.log(40), 16
gl = GaussLegendre(mp.mp); nodes = []
for p in range(NP):
    nodes += gl.get_nodes(U*p/NP, U*(p + 1)/NP, 6, mp.mp.prec)
W = [(u, w*(E8theta(mp.exp(-mp.pi*mp.exp(u))) - 1)) for u, w in nodes]
h = mp.mpf(d)/2
def Lam(s):
    return mp.fsum(w*(mp.exp(u*s) + mp.exp(u*(h - s))) for u, w in W) - 1/s - 1/(h - s)
def Xi(s): return s*(s - h)*Lam(s)
if len(sys.argv) > 3:   # validation against closed forms
    for s in (mp.mpc(0.7, 3), mp.mpc(h/2, 14), mp.mpc(h + 0.3, 25)):
        pre = mp.pi**(-s)*mp.gamma(s)
        ref = {1: 2*mp.zeta(2*s), 2: 4*mp.zeta(s)*mp.dirichlet(s, [0, 1, 0, -1]),
               4: 8*(1 - mp.power(4, 1 - s))*mp.zeta(s)*mp.zeta(s - 1),
               8: 240*mp.power(2, -s)*mp.zeta(s)*mp.zeta(s - 3)}[d]*pre
        print(d, s, mp.nstr(abs(Lam(s)/ref - 1), 3))
    sys.exit()
c = h/2; s1 = h + 2
# sign changes on the critical line
ts = [mp.mpf(i)/50 for i in range(1, int(50*T) + 1)]; v = [mp.re(Xi(mp.mpc(c, t))) for t in ts]
line = [float((ts[i] + ts[i + 1])/2) for i in range(len(v) - 1) if v[i]*v[i + 1] < 0]
# real zeros
xs = [h - s1 + (2*s1 - h)*(mp.mpf(i) + mp.mpf("0.371"))/2001 for i in range(2001)]; rv = [Xi(mp.mpf(x)) for x in xs]
nreal = sum(1 for i in range(2000) if rv[i]*rv[i + 1] < 0) + sum(1 for r in rv if r == 0)
# argument along the half contour, adaptive
def track(path):
    tot = mp.mpf(0); a = path(mp.mpf(0)); fa = Xi(a); tpos = mp.mpf(0); step = mp.mpf(1)/200
    while tpos < 1:
        nt = min(tpos + step, mp.mpf(1)); fb = Xi(path(nt)); da = mp.arg(fb/fa)
        if abs(da) > mp.pi/6 and step > mp.mpf(1)/200000: step /= 2; continue
        tot += da; fa = fb; tpos = nt; step = min(step*1.5, mp.mpf(1)/200)
    return tot
dv = track(lambda q: mp.mpc(s1, q*T)); dh = track(lambda q: mp.mpc(s1 - q*(s1 - c), T))
N = (dv + dh)/mp.pi - mp.mpf(nreal)/2
out = dict(d=d, T=T, N_total=float(N), N_line=len(line), N_real=nreal, line_zeros=[round(z, 3) for z in line],
           passes=bool(abs(float(N) - len(line)) < 0.25))
print(json.dumps(out))
