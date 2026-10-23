#!/usr/bin/env python3
"""Round 72: which edge condition fixes tau? Candidates, all giving tau -> e^{-delta}/(16 pi) at leading
order, evaluated with the exact S = log Phi to expose their finite-delta corrections:
 P1  W(caustic) = S(a)                       (amplitude at the caustic = Phi at the edge)
 P2  caustic fed from t0 = a + (1/2) log 2   (1 + 2 tau S''(t0) = 0 there)
 P3  edge characteristic lands at a - 1/4     (a + 2 tau S'(a) = a - 1/4)
 P4  caustic at a - (1/2) log(e/2)           (position of the caustic)
Compared with the measured tau (beta_fit: tau = -beta)."""
import json, math
import mpmath as mp
mp.mp.dps = 30
def Phi(t):
    s = mp.mpf(0); n = 1
    while True:
        c = mp.pi*n*n; X = mp.exp(2*t)
        term = (2*c*c*X*X - 3*c*X)*mp.exp(t/2 - c*X); s += term
        if abs(term) < abs(s)*mp.mpf(10)**(-45) and n > 1: return s
        n += 1
def Phid(t, m):
    s = mp.mpf(0); n = 1; X = mp.exp(2*t)
    while True:
        c = mp.pi*n*n; p = {1: -3*c, 2: 2*c*c}
        for _ in range(m):
            q = {}
            for k, v in p.items():
                q[k] = q.get(k, 0) + 2*k*v + v/2; q[k + 1] = q.get(k + 1, 0) - 2*c*v
            p = q
        term = sum(v*X**k for k, v in p.items())*mp.exp(t/2 - c*X); s += term
        if n > 2 and abs(term) < abs(s)*mp.mpf(10)**(-45): return s
        n += 1
S = lambda t: mp.log(Phid(t, 0))
S1 = lambda t: Phid(t, 1)/Phid(t, 0)
S2 = lambda t: Phid(t, 2)/Phid(t, 0) - S1(t)**2
def bisect(f, lo, hi, n=160):
    flo = f(lo)
    for _ in range(n):
        mid = (lo + hi)/2; fm = f(mid)
        if (fm > 0) == (flo > 0): lo, flo = mid, fm
        else: hi = mid
    return (lo + hi)/2
def caustic(tau):
    # 1 + 2 tau S''(t0) = 0 with S'' < 0 decreasing on the tail: bracket
    t0 = bisect(lambda u: 1 + 2*tau*S2(u), mp.mpf(0.2), mp.mpf(6))
    return t0, t0 + 2*tau*S1(t0), S(t0) + tau*S1(t0)**2
meas = {json.loads(l)['delta']: -float(json.loads(l)['beta']) for l in open('beta_fit_results.jsonl')}
rows = []
for d in sorted(meas):
    a = mp.mpf(d)/2; X = mp.e**d
    g = lambda c: c/X
    p1 = bisect(lambda c: caustic(g(c))[2] - S(a), mp.mpf(0.005), mp.mpf(0.06), 60)
    p2 = -X/(2*S2(a + mp.log(2)/2))
    p3 = -X/(8*S1(a))
    p4 = bisect(lambda c: caustic(g(c))[1] - (a - mp.log(mp.e/2)/2), mp.mpf(0.005), mp.mpf(0.06), 60)
    m = meas[d]*math.exp(d)
    rows.append((d, m, float(p1), float(p2), float(p3), float(p4)))
print("| δ | measured τe^δ | P1 caustic amp = Φ(a) | P2 source a+½log2 | P3 edge lands a−¼ | P4 caustic pos |")
for r in rows:
    print("| %.1f | %.6f | %.6f | %.6f | %.6f | %.6f |" % r)
print("1/(16 pi) =", 1/(16*math.pi))
