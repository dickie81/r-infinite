"""Locate the zeros of Et (see debranges.py) in the upper half-plane, 0 < Re z < R, 0 < Im z < Y."""
import sys, math, json
sys.path.insert(0, sys.argv[1])
from weil_prime_gram import gram, minimiser
from flint import arb, acb, ctx
import numpy as np
def run(delta, K, prec, R=60.0, Y=float(__import__("os").environ.get("YMAX", "4"))):
    G, N, pp = gram(delta, K, prec)
    c, ev = minimiser(G, N, prec)
    with ctx.workprec(prec):
        a = arb(delta) / 2
        c = [arb(x) for x in c]
        if c[0] < 0: c = [-x for x in c]
        om2 = [(arb(k) * arb.pi() / a) ** 2 for k in range(K)]
        sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
        g0 = sum(c)
        def Et(z):
            z = acb(z); S0 = acb(0); S1 = acb(0)
            for k in range(K):
                q = z / (z * z - om2[k]); S0 += c[k] * q; S1 += sg[k] * q
            s, co = (z * a).sin(), (z * a).cos()
            A = 2 * s * S1; B = 2 * (S0 - co * S1)
            At, Bt = g0 - z * B / 2, z * A / 2
            return At - acb(0, 1) * Bt
        xs = np.arange(0.013, R, 0.1); ys = np.arange(0.02, Y, 0.1 if Y <= 4 else 0.2)
        V = np.array([[abs(complex(Et(complex(x, y)).mid())) for x in xs] for y in ys])
        cands = []
        for i in range(1, len(ys) - 1):
            for j in range(1, len(xs) - 1):
                if V[i, j] <= V[i-1:i+2, j-1:j+2].min(): cands.append(complex(xs[j], ys[i]))
        roots = []
        for z in cands:
            for _ in range(60):
                f = Et(z); h = 1e-7
                fp = (Et(z + h) - Et(z - h)) / (2 * h)
                dz = complex((f / fp).mid()); z = z - dz
                if abs(dz) < 1e-12: break
            if 0 < z.imag and 0 < z.real < R and abs(complex(Et(z).mid())) < 1e-8 * float(abs(g0.mid())) \
               and all(abs(z - r) > 1e-6 for r in roots):
                roots.append(z)
    return sorted(roots, key=lambda z: z.real)
for spec in sys.argv[2:]:
    d, K, p = spec.split(':')
    r = run(float(d), int(K), int(p))
    print(json.dumps(dict(delta=float(d), roots=[[round(z.real, 4), round(z.imag, 5)] for z in r])))
    sys.stdout.flush()
