"""Test A: the zero flow of the ground-state transforms in delta.

For each delta: ground states at delta - h, delta, delta + h (paper's Gram, full-precision
coefficients, normalised by c_0 > 0). Real zeros of ghat_delta in (0, R) by sign changes plus
bisection; each zero's velocity dx/d delta by central difference of the matched zeros; and the
Wronskian W(x) = ghat * d_x(d_delta ghat) - d_delta ghat * d_x ghat on a real grid. W is invariant
under d_delta ghat -> d_delta ghat + c ghat, so the normalisation does not matter. A one-signed W
means ghat and d_delta ghat interlace, and all zeros move in the same direction.
Usage: flow.py <tools/research> delta:K:prec [...]"""
import sys, math, json, time
sys.path.insert(0, sys.argv[1])
from weil_prime_gram import gram, minimiser
from flint import arb, acb, ctx
import numpy as np

def state(delta, K, prec):
    G, N, pp = gram(delta, K, prec)
    c, ev = minimiser(G, N, prec)
    with ctx.workprec(prec):
        c = [arb(x) for x in c]
        if c[0] < 0: c = [-x for x in c]
        n0 = sum(c)                      # normalise g(0) = 1
        c = [x / n0 for x in c]
        a = arb(delta) / 2
        om2 = [(arb(k) * arb.pi() / a) ** 2 for k in range(K)]
        sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
    def gh(x, deriv=False):
        with ctx.workprec(prec):
            r = arb(x); S = arb(0); D = arb(0)
            for k in range(K):
                d = r * r - om2[k]; S += sg[k] * r / d
                if deriv: D += sg[k] * (-(r * r + om2[k])) / (d * d)
            s, co = (r * a).sin(), (r * a).cos()
            if not deriv: return 2 * s * S
            return 2 * s * S, 2 * (a * co * S + s * D)
    def ghc(z):
        with ctx.workprec(prec):
            z = acb(z); S = acb(0)
            for k in range(K): S += sg[k] * z / (z * z - om2[k])
            return 2 * (z * a).sin() * S
    gh.c = ghc
    return gh, float(ev.mid()) if hasattr(ev, 'mid') else float(ev)

def zeros(gh, R, step=0.01):
    xs = np.arange(0.00731, R, step); v = [float(gh(x).mid()) for x in xs]; out = []
    for i in range(len(xs) - 1):
        if v[i] * v[i + 1] < 0:
            lo, hi, flo = xs[i], xs[i + 1], v[i]
            for _ in range(50):
                m = (lo + hi) / 2; fm = float(gh(m).mid())
                if (fm < 0) == (flo < 0): lo, flo = m, fm
                else: hi = m
            out.append((lo + hi) / 2)
    return out

def run(delta, K, prec, h=1e-3, R=60.0, count=True):
    t0 = time.time()
    g0, lam = state(delta, K, prec); gm, _ = state(delta - h, K, prec); gp, _ = state(delta + h, K, prec)
    z0, zm, zp = zeros(g0, R), zeros(gm, R), zeros(gp, R)
    g0c, gpc, gmc = g0.c, gp.c, gm.c
    gz = lambda f, z: f(z)
    vel = []
    for x in z0:
        xm = min(zm, key=lambda y: abs(y - x)); xp = min(zp, key=lambda y: abs(y - x))
        vel.append((xp - xm) / (2 * h))
    # Wronskian on the grid
    xs = np.arange(0.00731, R, 0.01); npos = nneg = 0
    for x in xs:
        f, fx = g0(x, True); fpp, fpx = gp(x, True); fmm, fmx = gm(x, True)
        fd = (fpp - fmm) / (2 * h); fdx = (fpx - fmx) / (2 * h)
        W = float((f * fdx - fd * fx).mid())
        if W > 0: npos += 1
        elif W < 0: nneg += 1
    # zeros of the chain function E = ghat + i d_delta ghat in the upper half-disc |z| < R
    wind = None
    if count:
        def gc(z, gfun_prec=prec):
            return z
        def E(z):
            with ctx.workprec(prec):
                f0, fp, fm = gz(g0c, z), gz(gpc, z), gz(gmc, z)
                return complex((f0 + acb(0, 1) * (fp - fm) / (2 * h)).mid())
        # E is even in z, so the right variable is s = z^2: Hermite-Biehler in s means no zeros
        # with Im s > 0, i.e. none in the first quadrant of z. Contour: [0, R], arc, [iR, 0].
        e0 = 1e-3   # E(0) = ghat(0) != 0; a small quarter circle avoids the 0/0 of the formula
        path = [complex(x, 0) for x in np.linspace(e0, R, 12001)] + \
               [R * complex(math.cos(t), math.sin(t)) for t in np.linspace(0, math.pi / 2, 20001)[1:]] + \
               [complex(0, y) for y in np.linspace(R, e0, 12001)[1:]] + \
               [e0 * complex(math.cos(t), math.sin(t)) for t in np.linspace(math.pi / 2, 0, 51)[1:]]
        ang = np.unwrap(np.angle(np.array([E(z) for z in path])))
        wind = round(float((ang[-1] - ang[0]) / (2 * math.pi)), 3)
    return dict(delta=delta, K=K, prec=prec, h=h, lam1=lam, zeros_E_first_quadrant=wind, zeros=[round(float(x), 5) for x in z0],
                velocities=['%.3e' % float(v) for v in vel],
                n_up=int(sum(v > 0 for v in vel)), n_down=int(sum(v < 0 for v in vel)),
                W_pos=npos, W_neg=nneg, secs=round(time.time() - t0))

if __name__ == "__main__":
    for spec in sys.argv[2:]:
        parts = spec.split(':')
        d, K, p = parts[:3]; h = float(parts[3]) if len(parts) > 3 else 1e-3
        print(json.dumps(run(float(d), int(K), int(p), h=h))); sys.stdout.flush()
