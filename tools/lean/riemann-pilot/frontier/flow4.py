"""Test A, resolved: zero velocities at full precision, and the chain function's zeros off the axis.

Near a real zero x_j of ghat, E = ghat + i d_delta ghat has a zero at x_j + i v_j + O(v_j^2),
v_j = dx_j/d delta. When a zero is pinned at a zeta zero, v_j is ~1e-11 or smaller, and a
contour along the real axis passes within |v_j| of that zero. So (i) the real zeros are
refined by Newton in arb at the working precision and the v_j are taken from those; (ii) the
zeros of E with Im z > eta are counted on the first-quadrant contour lifted to Im z = eta.
Hermite-Biehler in s = z^2 <=> all v_j < 0 and no zeros counted in (ii).
Usage: flow4.py <tools/research> delta:K:prec:h [...]"""
import sys, json, math
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, 'debr')
import flow
from flint import arb, acb, ctx
import numpy as np

def refine(gh, x, prec):
    with ctx.workprec(prec):
        z = arb(x)
        for _ in range(80):
            f, fx = gh(z, True)
            dz = f / fx
            z = (z - dz).mid()
            if abs(float(dz.mid())) < 2.0 ** (-prec + 40): break
        return z

if __name__ == "__main__":
    for spec in sys.argv[2:]:
        d, K, p, h = spec.split(':'); d, K, p, h = float(d), int(K), int(p), float(h)
        g0, lam = flow.state(d, K, p); gp, _ = flow.state(d + h, K, p); gm, _ = flow.state(d - h, K, p)
        z0 = flow.zeros(g0, 60.0)
        vel = []
        with ctx.workprec(p):
            for x in z0:
                r0, rp, rm = refine(g0, x, p), refine(gp, x, p), refine(gm, x, p)
                vel.append(float(((rp - rm) / (2 * h)).mid()))
            eta = float(__import__("os").environ.get("ETA", "1e-3"))
            def E(z):
                return complex((g0.c(z) + acb(0, 1) * (gp.c(z) - gm.c(z)) / (2 * h)).mid())
            R = 60.0
            path = [complex(x, eta) for x in np.linspace(eta, R, int(__import__("os").environ.get("NREAL", "24001")))] + \
                   [R * complex(math.cos(t), math.sin(t)) for t in np.linspace(eta / R, math.pi / 2, 20001)[1:]] + \
                   [complex(eta, y) for y in np.linspace(R, eta, 12001)[1:]]
            ang = np.unwrap(np.angle(np.array([E(z) for z in path])))
            wind = (ang[-1] - ang[0]) / (2 * math.pi)
            maxstep = float(np.max(np.abs(np.diff(ang))))
        print(json.dumps(dict(delta=d, K=K, prec=p, h=h, zeros=[round(x, 5) for x in z0],
            velocities=['%.3e' % v for v in vel], n_pos=int(sum(v > 0 for v in vel)), n_neg=int(sum(v < 0 for v in vel)),
            zeros_E_above_eta=round(wind, 3), max_phase_step=maxstep)))
        sys.stdout.flush()
