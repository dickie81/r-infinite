"""Validate the generalised Gram (z0 = 3/4, log(q/pi), no pole, weights c(n)) on L(s, chi_4)
against the zero sum sum_gamma ghat(gamma)^2 (all zeros on the line; sign changes of Z)."""
import sys, math, json
sys.path.insert(0, '.')
import mpmath as mp, dh_gram as D
from flint import arb, ctx
mp.mp.dps = 20
chi4 = [0, 1, 0, -1]
def Lam(s): return (4/mp.pi)**(s/2)*mp.gamma((s + 1)/2)*mp.dirichlet(s, chi4)
print("FE chi4", mp.nstr(abs(Lam(0.3+5j) - Lam(0.7-5j))/abs(Lam(0.3+5j)), 3))
T = float(sys.argv[1]); delta = float(sys.argv[2]); K = 24; prec = 300
Z = lambda t: mp.re(Lam(0.5 + 1j*t))
zs = []; t = 0.3; h = 0.05; zp = Z(t)
while t < T:
    z2 = Z(t + h)
    if zp*z2 < 0: zs.append(float(mp.findroot(Z, (t, t + h), solver='anderson')))
    t += h; zp = z2
print("zeros", len(zs), zs[:4])
a = delta/2
# a smooth probe: g(u) = exp(-1/(1-(u/a)^2)) expanded in cos(k pi u/a)
import numpy as np
from scipy.integrate import quad
bump = lambda u: math.exp(-1/(1 - (u/a)**2)) if abs(u) < a else 0.0
cf = [quad(lambda u: bump(u)*math.cos(k*math.pi*u/a), -a, a, limit=200)[0]/(2*a if k == 0 else a) for k in range(K)]
def ghat(r):
    s = 0.0
    for k, c in enumerate(cf):
        w = k*math.pi/a
        # int_{-a}^{a} cos(w u) cos(r u) du
        if abs(r - w) < 1e-12: I = a + (math.sin(2*w*a)/(2*w) if w else a)
        else: I = (math.sin((r - w)*a)/(r - w) + (math.sin((r + w)*a)/(r + w) if r + w else 2*a)) if True else 0
        s += c*I
    return s
Qz = 2*sum(ghat(g)**2 for g in zs)
# Gram
with ctx.workprec(prec + 40):
    lam = lambda n: None
    N = int(math.exp(delta)) + 1
    w = []
    for n in range(2, N + 1):
        # Lambda(n) chi4(n)
        p = next(q for q in range(2, n + 1) if n % q == 0); m = n
        while m % p == 0: m //= p
        if m == 1 and chi4[n % 4] != 0: w.append((n, arb(p).log()*chi4[n % 4]))
    G, Nn, pp = D.gram(delta, K, prec, dict(z0=0.75, logq=(arb(4)/arb.pi()).log(), pole=False, weights=w))
    Qg = sum(cf[i]*cf[j]*float(G[i, j].mid()) for i in range(K) for j in range(K))
print(json.dumps({"delta": delta, "Q_gram": Qg, "Q_zeros": Qz, "rel": abs(Qg - Qz)/abs(Qg)}))
