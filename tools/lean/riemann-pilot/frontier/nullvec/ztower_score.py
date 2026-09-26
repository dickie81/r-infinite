#!/usr/bin/env python3
"""Score the pre-registered test PREREG_tower_layers.md exactly as registered.
P1: pred = ln[xi(d+1)/xi(1/2)] + T0[sqrt(1+eta^2) - 1 - eta asinh eta], eta = (d+1/2)/(2 T0), T0 = 2 pi e^delta.
Pass iff |meas/pred - 1| <= 3 e^{-delta} for all d <= 2 T0 (here d = 0..60).
Null: the multiplier replaced by the Gaussian e^{tau z^2}, tau = e^{-delta}/(16 pi) (round 70).
Usage: ztower_score.py runs/tower/d*.json"""
import sys, json
from mpmath import mp, mpf, zeta, gamma, pi, exp, sqrt, asinh, log
mp.dps = 40
xi = lambda s: mpf(1)/2 if s == 1 else s*(s - 1)/2*pi**(-s/2)*gamma(s/2)*zeta(s)   # xi(1) = 1/2 (removable)
for f in sys.argv[1:]:
    try: o = json.load(open(f))
    except Exception: print(f, "not ready"); continue
    dl = mpf(o["delta"]); T0 = 2*pi*exp(dl); tau = exp(-dl)/(16*pi); tol = 3*exp(-dl)
    worst = (0, None); worstN = (0, None); rows = []
    for k, v in o["layers"].items():
        L = int(k); z = mpf(L) + mpf(1)/2; eta = z/(2*T0); meas = mpf(v)
        base = log(xi(L + 1)/xi(mpf(1)/2))
        pred = base + T0*(sqrt(1 + eta**2) - 1 - eta*asinh(eta))
        null = base - tau*z**2
        r = abs(meas/pred - 1); rn = abs(meas/null - 1)
        rows.append((L, float(meas), float(pred), float(meas - pred), float(r), float(rn)))
        if r > worst[0]: worst = (r, L)
        if rn > worstN[0]: worstN = (rn, L)
    print(f"delta {float(dl)}: K {o['K']}  tolerance 3e^-delta = {float(tol):.4g}")
    print(f"   P1   max |ratio-1| = {float(worst[0]):.3e} at d = {worst[1]}   -> {'PASS' if worst[0] <= tol else 'FAIL'}")
    print(f"   null max |ratio-1| = {float(worstN[0]):.3e} at d = {worstN[1]}   -> {'passes too' if worstN[0] <= tol else 'fails'}")
    for L, m, p, dif, r, rn in rows:
        if L in (0, 1, 2, 5, 10, 20, 30, 45, 60):
            print(f"      d={L:2d}  meas {m:12.6f}  pred {p:12.6f}  diff {dif: .2e}  |ratio-1| {r:.2e}  null {rn:.2e}")
