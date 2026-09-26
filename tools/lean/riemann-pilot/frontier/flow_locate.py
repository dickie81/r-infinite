"""Locate zeros of the chain function E = ghat + i d_delta ghat in the first quadrant (see flow.py)."""
import sys, json, math
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, 'debr')
import flow
from flint import acb, ctx
import numpy as np
for spec in sys.argv[2:]:
    d, K, p, h = spec.split(':'); d, K, p, h = float(d), int(K), int(p), float(h)
    g0, _ = flow.state(d, K, p); gp, _ = flow.state(d + h, K, p); gm, _ = flow.state(d - h, K, p)
    def E(z):
        with ctx.workprec(p):
            return g0.c(z) + acb(0, 1) * (gp.c(z) - gm.c(z)) / (2 * h)
    xs = np.arange(0.5, 60, 0.25); ys = np.arange(0.05, 30, 0.25)
    V = np.array([[abs(complex(E(complex(x, y)).mid())) for x in xs] for y in ys])
    roots = []
    for i in range(1, len(ys) - 1):
        for j in range(1, len(xs) - 1):
            if V[i, j] <= V[i-1:i+2, j-1:j+2].min():
                z = complex(xs[j], ys[i])
                for _ in range(60):
                    f = E(z); fp = (E(z + 1e-7) - E(z - 1e-7)) / 2e-7
                    dz = complex((f / fp).mid()); z -= dz
                    if abs(dz) < 1e-12: break
                if z.real > 0 and z.imag > 0 and abs(z) < 60 and all(abs(z - r) > 1e-6 for r in roots) \
                   and abs(complex(E(z).mid())) < 1e-6 * abs(complex(E(complex(1, 0)).mid())):
                    roots.append(z)
    print(json.dumps(dict(delta=d, h=h, roots=sorted([[round(z.real, 4), round(z.imag, 4)] for z in roots])))); sys.stdout.flush()
