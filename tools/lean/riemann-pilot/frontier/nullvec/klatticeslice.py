#!/usr/bin/env python3
"""Round 168: isodual discretisations of the ball's d-slices (PREREG_isodual.md).
Lattice = '+'-joined blocks from Z, A2, D4, E8 (covolume 1 each), e.g. 'Z+A2+A2'.
Xi_L(s) = s(s-d/2) Lambda_L(s), Lambda_L = int_1^inf (theta_L - 1)(x^s + x^{d/2-s}) dx/x - 1/s - 1/(d/2-s).
Counts as round 92 (klatticeball.py). Usage: klatticeslice.py LATTICE T [check]"""
import sys, json, mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre
name, T = sys.argv[1], float(sys.argv[2]); mp.mp.dps = int(25 + 0.75*T)
j = lambda k, q: mp.jtheta(k, 0, q)
def blk(b, x):
    if b == 'Z': return j(3, mp.exp(-mp.pi*x))
    if b == 'A2':
        q = mp.exp(-mp.pi*x*2/mp.sqrt(3)); return j(3, q)*j(3, q**3) + j(2, q)*j(2, q**3)
    if b == 'D4':
        q = mp.exp(-mp.pi*x/mp.sqrt(2)); return (j(3, q)**4 + j(4, q)**4)/2
    if b == 'E8':
        q = mp.exp(-mp.pi*x); return (j(2, q)**8 + j(3, q)**8 + j(4, q)**8)/2
dims = {'Z': 1, 'A2': 2, 'D4': 4, 'E8': 8}
blocks = name.split('+'); d = sum(dims[b] for b in blocks)
def theta(x):
    p = mp.mpf(1)
    for b in blocks: p *= blk(b, x)
    return p
U, NP = mp.log(40), 16
gl = GaussLegendre(mp.mp); nodes = []
for p in range(NP): nodes += gl.get_nodes(U*p/NP, U*(p + 1)/NP, 6, mp.mp.prec)
W = [(u, w*(theta(mp.exp(u)) - 1)) for u, w in nodes]
h = mp.mpf(d)/2
def Lam(s): return mp.fsum(w*(mp.exp(u*s) + mp.exp(u*(h - s))) for u, w in W) - 1/s - 1/(h - s)
def Xi(s): return s*(s - h)*Lam(s)
if len(sys.argv) > 3:
    x = mp.mpf('1.7'); print(name, 'isodual defect', mp.nstr(abs(theta(1/x)/(x**h*theta(x)) - 1), 3))
    for s in (mp.mpc(0.7, 3), mp.mpc(h/2, 14), mp.mpc(h + 0.3, 25)):
        pre = mp.pi**(-s)*mp.gamma(s); ref = None
        if name == 'A2': ref = 6*(2/mp.sqrt(3))**(-s)*mp.zeta(s)*mp.dirichlet(s, [0, 1, -1])
        if name == 'E8': ref = 240*mp.power(2, -s)*mp.zeta(s)*mp.zeta(s - 3)
        if ref is not None: print(name, s, 'closed-form defect', mp.nstr(abs(Lam(s)/(ref*pre) - 1), 3))
        print(name, s, 'FE defect', mp.nstr(abs(Lam(s)/Lam(h - s) - 1), 3))
    sys.exit()
c = h/2; s1 = h + 2
ts = [mp.mpf(i)/50 for i in range(1, int(50*T) + 1)]; v = [mp.re(Xi(mp.mpc(c, t))) for t in ts]
line = [float((ts[i] + ts[i + 1])/2) for i in range(len(v) - 1) if v[i]*v[i + 1] < 0]
xs = [h - s1 + (2*s1 - h)*(mp.mpf(i) + mp.mpf("0.371"))/2001 for i in range(2001)]; rv = [Xi(mp.mpf(x)) for x in xs]
nreal = sum(1 for i in range(2000) if rv[i]*rv[i + 1] < 0) + sum(1 for r in rv if r == 0)
def track(path):
    tot = mp.mpf(0); a = path(mp.mpf(0)); fa = Xi(a); tpos = mp.mpf(0); step = mp.mpf(1)/200
    while tpos < 1:
        nt = min(tpos + step, mp.mpf(1)); fb = Xi(path(nt)); da = mp.arg(fb/fa)
        if abs(da) > mp.pi/6 and step > mp.mpf(1)/200000: step /= 2; continue
        tot += da; fa = fb; tpos = nt; step = min(step*1.5, mp.mpf(1)/200)
    return tot
dv = track(lambda q: mp.mpc(s1, q*T)); dh = track(lambda q: mp.mpc(s1 - q*(s1 - c), T))
N = (dv + dh)/mp.pi - mp.mpf(nreal)/2
print(json.dumps(dict(lattice=name, d=d, T=T, N_total=round(float(N), 3), N_line=len(line), N_real=nreal,
      line_zeros=[round(z, 3) for z in line], passes=bool(abs(float(N) - len(line)) < 0.25))), flush=True)
