"""Measure kappa(a) in  ghat_a(z)/ghat_a(0) = Xi(z)/Xi(0) (1 + kappa z^2 + O(z^4)), and compare with the
edge-model prediction kappa = (1 + log 2)/(8 pi^2) e^{-2a} (pre-registered for delta = 2.6, 3.0)."""
import sys, json, math
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram, minimiser
import mpmath as mp
d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
a = d / 2
G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
mp.mp.dps = 60
cm = [mp.mpf(str(x)) if isinstance(x, float) else mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1]))) if hasattr(x, 'mid') else mp.mpf(x) for x in c]
def ghat(z):
    s = mp.mpc(0)
    for k in range(K):
        w = k * mp.pi / a
        s += cm[k] * ((2 * mp.sin(z * a) / z) if k == 0 else (-1)**k * 2 * z * mp.sin(z * a) / (z**2 - w**2))
    return s
def Xi(z):
    s = mp.mpf(0.5) + 1j * z
    return 0.5 * s * (s - 1) * mp.pi**(-s/2) * mp.gamma(s/2) * mp.zeta(s)
g0 = ghat(mp.mpf('1e-40')); X0 = Xi(0)
rows = {}
for z in [0.5, 1, 2, 3, 4, 2j, 4j]:
    z = mp.mpc(z)
    r = (ghat(z) / g0) / (Xi(z) / X0) - 1
    rows[str(complex(z))] = [float((r / z**2).real), float((r / z**2).imag)]
pred = (1 + math.log(2)) / (8 * math.pi**2) * math.exp(-2 * a)
print(json.dumps(dict(delta=d, K=K, kappa_pred=pred, r_over_z2=rows)), flush=True)
