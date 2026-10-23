"""(a)-probe: compare the Weil ground state g_a on [-a,a] with Riemann's kernel Phi truncated to [-a,a].
Phi(u) = sum_n (2 pi^2 n^4 e^{9u/2} - 3 pi n^2 e^{5u/2}) exp(-pi n^2 e^{2u}),  Xi(z) = 2 int_0^inf Phi(u) cos(zu) du (up to a constant).
Outputs: lambda_1, Rayleigh(Phi_a), sin of the L^2 angle between g_a and Phi_a, and sup_{|z|<=R} |ghat/ghat(0) - Xi/Xi(0)|."""
import sys, json, math
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram, minimiser, rayleigh
from flint import arb, ctx
import mpmath as mp
d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
a = d / 2
mp.mp.dps = int(p * 0.3)
def Phi(u):
    s = mp.mpf(0); n = 1
    while True:
        t = (2 * mp.pi**2 * n**4 * mp.e**(4.5*u) - 3 * mp.pi * n**2 * mp.e**(2.5*u)) * mp.e**(-mp.pi * n**2 * mp.e**(2*u))
        s += t
        if abs(t) < mp.mpf(10)**(-mp.mp.dps - 10) * abs(s) and n > 2: break
        n += 1
    return s
G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
Nf = [mp.mpf(float(N[k])) if False else (2*mp.mpf(a) if k == 0 else mp.mpf(a)) for k in range(K)]
b = []
from mpmath.calculus.quadrature import GaussLegendre
nodes = GaussLegendre(mp.mp).calc_nodes(7, mp.mp.prec)   # 192-node rule on [-1, 1]
pan = 12
pts = []
for j in range(pan):
    lo, hi = mp.mpf(a) * j / pan, mp.mpf(a) * (j + 1) / pan
    for x, w in nodes:
        pts.append(((hi + lo) / 2 + (hi - lo) / 2 * x, (hi - lo) / 2 * w))
phv = [(u, w * Phi(u)) for u, w in pts]
for k in range(K):
    wk = k * mp.pi / a
    b.append(2 * sum(pw * mp.cos(wk * u) for u, pw in phv) / Nf[k])
with ctx.workprec(p):
    bb = [arb(mp.nstr(x, mp.mp.dps)) for x in b]
    nb = sum(arb(float(1)) * 0 + (2 * arb(a) if k == 0 else arb(a)) * bb[k] ** 2 for k in range(K)).sqrt()
    bb = [x / nb for x in bb]
    rphi = rayleigh(G, N, bb, p)
    cc = [arb(x) for x in c]
    nc = sum((2 * arb(a) if k == 0 else arb(a)) * cc[k] ** 2 for k in range(K)).sqrt(); cc = [x / nc for x in cc]
    lam = rayleigh(G, N, cc, p)
cm = [mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1]))) for x in cc]
bm = [mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1]))) for x in bb]
ip = sum(Nf[k] * cm[k] * bm[k] for k in range(K))
if ip < 0: cm = [-x for x in cm]; ip = -ip
sin2 = max(mp.mpf(0), 1 - ip**2)
# the projection error of Phi_a onto K cosine modes
proj_err2 = 2 * mp.quad(lambda u: Phi(u)**2, [0, a]) / nb.mid().__float__()**2 if False else None
def ghat(cv, z):
    s = mp.mpf(0)
    for k in range(K):
        w = k * mp.pi / a
        if k == 0: s += cv[0] * 2 * mp.sin(z * a) / z if z != 0 else cv[0] * 2 * a
        else: s += cv[k] * (-1)**k * 2 * z * mp.sin(z * a) / (z**2 - w**2)
    return s
def Xi(z):
    s = mp.mpf(0.5) + 1j * z
    return 0.5 * s * (s - 1) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)
g0 = ghat(cm, mp.mpf('1e-30')); X0 = Xi(0)
res = {}
for R in [5, 10, 20, 30]:
    m = 0
    for j in range(24):
        th = 2 * mp.pi * j / 24
        z = R * mp.expj(th)
        m = max(m, abs(ghat(cm, z) / g0 - Xi(z) / X0) / max(1, abs(Xi(z) / X0)))
    res[R] = float(m)
print(json.dumps(dict(delta=d, K=K, lam1=float(lam.mid()), rayleigh_Phi=float(rphi.mid()),
      sin_angle=float(mp.sqrt(sin2)), ghat0_over_norm=float(g0), rel_err_disc=res)), flush=True)
