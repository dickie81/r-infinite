"""Round 24: is the ground state of Weil's form in Polya's class (even, concave on (-a, a))?

Ground state from the paper's Gram (tools/research/weil_prime_gram.py: even cosine basis
cos(k pi t/a), every prime power, `prec` bits). Concavity is tested by second differences at step
a/40 on [0, a - 1.5 a/40]. That scale is coarse against the Gibbs ripple of the truncated cosine
series (wavelength ~ 2a/K), which at fine scale shows spurious convex patches. Also reported: the
first positive zero of ghat, and the bound 2 pi/a that every member of Polya's class satisfies
(Phi(x) = beta x sin(xa) + int (cos xc - cos xa) dmu is > 0 for small x > 0 and <= 0 at
x = 2 pi/a, so ghat has a zero in (0, 2 pi/a]). A first zero above 2 pi/a rules concavity out.

Usage: polya_shape.py <tools/research> delta:K [delta:K ...]      (prec 256 bits)"""
import sys, math, json, numpy as np
sys.path.insert(0, sys.argv[1])
from weil_prime_gram import gram, minimiser
from scipy.optimize import brentq
for spec in sys.argv[2:]:
    delta, K = float(spec.split(':')[0]), int(spec.split(':')[1]); prec = 256
    G, N, pp = gram(delta, K, prec)
    c, ev = minimiser(G, N, prec)
    cm = np.array([float(x) for x in c]); cm = cm if cm[0] > 0 else -cm
    a = delta/2
    h = a/40; t = np.arange(0, a - 1.5*h, h)
    g = lambda s: sum(cm[k]*np.cos(k*math.pi*s/a) for k in range(K))
    d2 = g(t+h) - 2*g(t) + g(np.abs(t-h))
    g0 = g(np.array([0.0]))[0]
    om = np.array([k*math.pi/a for k in range(K)]); sg = np.array([cm[k]*(-1)**k for k in range(K)])
    gh = lambda r: 2*math.sin(r*a)*np.sum(sg*r/(r*r-om*om))
    xs = np.arange(0.05, 60, 0.013); v = [gh(x) for x in xs]
    z1 = next(brentq(gh, xs[i], xs[i+1]) for i in range(len(xs)-1) if v[i]*v[i+1] < 0)
    print(json.dumps(dict(delta=delta, K=K, lam=float(ev.mid()), max_d2_over_g0=float(d2.max()/g0),
        where=float(t[np.argmax(d2)]/a), concave_coarse=bool(d2.max() < 0),
        g_edge=float(g(np.array([a]))[0]/g0), first_zero=z1, polya_first_zero_max=2*math.pi/a)))
    sys.stdout.flush()
