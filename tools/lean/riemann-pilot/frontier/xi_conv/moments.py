"""Check kappa(a) = (M2(Phi) - m2(g_a))/2 with m2 = int u^2 g / int g, and ground-state positivity."""
import sys, json
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram, minimiser
import mpmath as mp
mp.mp.dps = 50
def Phi(u):
    return sum((2*mp.pi**2*n**4*mp.e**(4.5*u) - 3*mp.pi*n**2*mp.e**(2.5*u)) * mp.e**(-mp.pi*n**2*mp.e**(2*u)) for n in range(1, 30))
M2 = mp.quad(lambda u: u**2 * Phi(u), [0, 1, 3]) / mp.quad(Phi, [0, 1, 3])
out = dict(M2_half=float(M2 / 2))
for d, K, p in [(1.4, 90, 500), (2.2, 160, 900)]:
    a = d / 2
    G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
    cm = [mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1]))) if hasattr(x, 'mid') else mp.mpf(x) for x in c]
    g = lambda u: sum(cm[k] * mp.cos(k * mp.pi * u / a) for k in range(K))
    m0 = 2 * a * cm[0]
    m2 = sum(cm[k] * 2 * mp.quad(lambda u: u**2 * mp.cos(k * mp.pi * u / a), [0, a]) for k in range(K))
    if m0 < 0: m0, m2 = -m0, -m2; cm = [-x for x in cm]
    gmin = min(g(mp.mpf(a) * j / 400) for j in range(401))
    out[str(d)] = dict(kappa_from_moments=float((M2 - m2 / m0) / 2), g_min_over_g0=float(gmin / g(0)))
print(json.dumps(out))
