#!/usr/bin/env python3
"""Round 111: zeros of Z(t) = e^{i theta_chi(t)} L(1/2+it, chi_-4) (real), theta_chi = (t/2) ln(4/pi) + Im logGamma(3/4 + it/2).
Usage: kLzeros.py t0 t1 out.json   (grid step 0.05, sign changes refined by Illinois/secant to 1e-12)."""
import sys, json, mpmath as mp
mp.mp.dps = 20; q = 4
def theta(t): return t/2*mp.log(q/mp.pi) + mp.im(mp.loggamma(mp.mpf(3)/4 + 1j*t/2))
def Z(t):
    t = mp.mpf(t); v = mp.exp(1j*theta(t))*mp.dirichlet(mp.mpc(0.5, t), [0, 1, 0, -1])
    return v
t0, t1 = float(sys.argv[1]), float(sys.argv[2]); out = []; h = 0.05
prev_t, prev = t0, Z(t0); maxim = 0.0
n = int(round((t1 - t0)/h))
for i in range(1, n + 1):
    t = t0 + i*h; v = Z(t); maxim = max(maxim, float(abs(mp.im(v))/(abs(v) + 1e-30)))
    if mp.re(v)*mp.re(prev) < 0:
        r = mp.findroot(lambda s: mp.re(Z(s)), (prev_t, t), solver="illinois", tol=1e-24); out.append(float(r))
    prev_t, prev = t, v
json.dump({"zeros": out, "max_rel_imag": maxim}, open(sys.argv[3], "w")); print(len(out), "zeros in", t0, t1, "max |Im Z|/|Z|", maxim)
