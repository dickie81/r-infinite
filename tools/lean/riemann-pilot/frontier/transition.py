"""Round 34: the transition zone. Envelope U inside the saturated region from the round-33 model.

f = sigma - a/pi on (-T, T) (sigma = smoothed zeta-zero density, 0 below T0), T = T_edge(a).
U'(x) = sqrt(T^2 - x^2) * Hu(x),  Hu(x) = pv int_{-pi/2}^{pi/2} f(T sin th)/(x - T sin th) d th
(using pv int d th/(x - T sin th) = 0 inside, the integrand is regularised by subtracting f(x)).
Delta(x) = U(x) - U(T) = -int_x^T U'(y) dy. Prediction: eps_j ~ A exp(-2 Delta(gamma_j)), and
2 Delta(0) ~ -log lam1 (the band level is ~ (1/2) log lam1 below U(0) = 0).
Usage: transition.py <zeros.json>"""
import math, json, sys
import numpy as np
from scipy.integrate import quad
sys.path.insert(0, __import__("os").path.dirname(__import__("os").path.abspath(__file__)))
import edge_model as E
def model(a):
    T = E.t_edge(a); T0 = E.T0
    f = lambda t: (E.sig(abs(t)) if abs(t) > T0 else 0.0) - a / math.pi
    th0 = math.asin(T0 / T)
    def Hu(x):
        fx = f(x)
        g = lambda th: (f(T * math.sin(th)) - fx) / (x - T * math.sin(th))
        pts = sorted({-th0, th0, math.asin(max(-1, min(1, x / T)))})
        return quad(g, -math.pi / 2, math.pi / 2, points=pts, limit=400)[0]
    Up = lambda y: math.sqrt(max(T * T - y * y, 0)) * Hu(y)
    ys = np.linspace(0, T, 801)
    up = np.array([Up(y) for y in ys])
    # Delta(x) = -int_x^T U'
    cum = np.concatenate([[0], np.cumsum((up[1:] + up[:-1]) / 2 * np.diff(ys))])   # int_0^x U'
    Delta = lambda x: -(cum[-1] - np.interp(x, ys, cum))
    return T, Delta, ys, up
if __name__ == "__main__":
    import os
    here = os.path.dirname(os.path.abspath(__file__))
    G = json.load(open(sys.argv[1]))          # a JSON list of zeta-zero ordinates (>= 20 of them)
    rows = {json.loads(l)['delta']: json.loads(l) for l in open(os.path.join(here, 'pinned_results.jsonl'))}
    fronts = {json.loads(l)['delta']: json.loads(l) for l in open(os.path.join(here, 'front_results.jsonl'))}
    for d in [1.0, 1.2, 1.3828125, 1.6, 2.0]:
        a = d / 2; T, Delta, ys, up = model(a)
        lam = rows[d]['lam1'] if d in rows else fronts[d]['lam1']
        out = dict(delta=d, T_edge=T, two_Delta0=2 * Delta(0.0), minus_log_lam=-math.log(lam),
                   Uprime_at_20=float(np.interp(20, ys, up)), minus_a_over_2=-a / 2)
        if d in rows:
            js = [p[0] for p in rows[d]['pinned']]; eps = np.array([float(p[1]) for p in rows[d]['pinned']])
            D2 = np.array([2 * Delta(G[j - 1]) for j in js])
            if len(js) >= 2:
                k, c = np.polyfit(-D2, np.log(eps), 1)
                out.update(slope_vs_minus2Delta=k, logA_fit=c)
            out['logeps_plus_2Delta'] = [round(float(x), 2) for x in np.log(eps) + D2]
        print(json.dumps(out)); sys.stdout.flush()
