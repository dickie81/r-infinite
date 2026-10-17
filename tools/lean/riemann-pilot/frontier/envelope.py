"""Round 36b: the envelope U(x) = log|ghat(x)/ghat(0)| inside the pinned region, model against
measurement. Measured at each gamma_j: log|ghat'(gamma_j)| - log(pi sigma(gamma_j)) - log ghat(0),
since ghat ~ e^U sin(pi N(x)) gives |ghat'| = e^U pi sigma at a zero. Model: U(x) = U(0) + int_0^x U',
with U' from transition.model and U(0) = 0."""
import sys, json, math
import numpy as np
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
sys.path.insert(0, __import__("os").path.join(__import__("os").path.dirname(__import__("os").path.abspath(__file__)), "../../../research"))
import transition as TR, edge_model as E
from weil_prime_gram import gram, minimiser
from flint import arb, ctx
import mpmath
mpmath.mp.dps = 50
GAM = [mpmath.zetazero(n).imag for n in range(1, 31)]
for spec in sys.argv[1:]:
    d, K, p = spec.split(':'); d, K, p = float(d), int(K), int(p)
    a = d / 2
    T, Delta, ys, up = TR.model(a)
    cumU = np.concatenate([[0], np.cumsum((up[1:] + up[:-1]) / 2 * np.diff(ys))])
    G, N, pp = gram(d, K, p); c, ev = minimiser(G, N, p)
    with ctx.workprec(p):
        c = [arb(x) for x in c]
        if c[0] < 0: c = [-x for x in c]
        aa = arb(d) / 2
        om2 = [(arb(k) * arb.pi() / aa) ** 2 for k in range(K)]
        sg = [c[k] if k % 2 == 0 else -c[k] for k in range(K)]
        g0 = 2 * aa * c[0]
        def dgh(r):
            S = arb(0); D = arb(0)
            for k in range(K):
                dd = r * r - om2[k]; S += sg[k] * r / dd; D += sg[k] * (-(r * r + om2[k])) / (dd * dd)
            return 2 * (aa * (r * aa).cos() * S + (r * aa).sin() * D)
        rows = []
        for j, gm in enumerate(GAM):
            if gm > T: break
            r = arb(mpmath.nstr(gm, 45))
            meas = math.log(abs(float(dgh(r).mid()))) - math.log(math.pi * E.sig(float(gm))) - math.log(float(g0.mid()))
            model = float(np.interp(float(gm), ys, cumU))
            rows.append([j + 1, round(float(gm), 2), round(meas, 2), round(model, 2), round(meas - model, 2)])
    diffs = np.array([r[4] for r in rows])
    print(json.dumps(dict(delta=d, T_edge=T, rows=rows, mean_diff=float(diffs.mean()), sd_diff=float(diffs.std()),
                          slope_meas_vs_model=float(np.polyfit([r[3] for r in rows], [r[2] for r in rows], 1)[0]))))
    sys.stdout.flush()
