#!/usr/bin/env python3
"""Round 71: Hamilton–Jacobi (characteristics) form of the backward heat flow e^{-tau d^2} Phi.
With W = log g: W_tau = -(W_t)^2 (dropping W_tt). Characteristics from t0: p = S'(t0), S = log Phi,
t = t0 + 2 p tau, W = S(t0) + tau p^2. Caustic where dt/dt0 = 1 + 2 tau S''(t0) = 0.
Compares log(g/Phi) (oscillator.py output) with the HJ prediction on the main branch.
Usage: hj.py <osc_json> <tau>"""
import sys, json, math
import mpmath as mp
mp.mp.dps = 60
def Phi(t):
    s = mp.mpf(0); n = 1
    while True:
        c = mp.pi*n*n; X = mp.exp(2*t)
        term = (2*c*c*X*X - 3*c*X)*mp.exp(t/2 - c*X); s += term
        if abs(term) < abs(s)*mp.mpf(10)**(-50) and n > 1: return s
        n += 1
S = lambda t: mp.log(Phi(t))
S1 = lambda t: mp.diff(S, t, 1)
S2 = lambda t: mp.diff(S, t, 2)
r = json.load(open(sys.argv[1])); tau = mp.mpf(sys.argv[2]); a = r['delta']/2
# caustic: 1 + 2 tau S''(t0) = 0 (S'' < 0 on the tail)
t0c = mp.findroot(lambda t0: 1 + 2*tau*S2(t0), a)
tc = t0c + 2*tau*S1(t0c)
print(json.dumps({"delta": r['delta'], "tau": float(tau), "t0_caustic": float(t0c), "t_caustic": float(tc),
                  "a - t_caustic": float(a - tc), "pred a - t_c (X-limit)": 0.5*math.log(math.e/2)}))
def hj_at(t):
    # solve t0 + 2 tau S'(t0) = t on the main branch t0 < t0c
    t0 = mp.findroot(lambda u: u + 2*tau*S1(u) - t, t*0.999)
    return S(t0) + tau*S1(t0)**2 - S(t)
rows = r['rows']; g0 = rows[0]['log_g_over_Phi']; h0 = float(hj_at(mp.mpf(0)))
for w in rows[::3]:
    t = w['t']
    if t >= float(tc) - 1e-9 or w['log_g_over_Phi'] is None:
        print(f"t={t:.3f}  beyond caustic / no data"); continue
    hj = float(hj_at(mp.mpf(t))) - h0
    print(f"t={t:.3f} g:{w['log_g_over_Phi']-g0:+.4f} heat:{(w['log_heat_over_Phi'] or float('nan'))-rows[0]['log_heat_over_Phi']:+.4f} HJ:{hj:+.4f}")
