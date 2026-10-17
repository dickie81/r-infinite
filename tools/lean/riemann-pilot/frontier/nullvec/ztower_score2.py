#!/usr/bin/env python3
"""Score PREREG_tower_horizon.md (round 87) exactly as registered.
Validity: the two bases agree to <= 1e-3 relative for d <= 500 (else void at those layers).
(A) |meas/P1 - 1| <= 3e-3 for all d <= 500.
(B) |meas/N - 1| > 3e-3 for all 300 <= d <= 500 (Gaussian null fails).
(C) meas - P1 = -c z^2 with c within +-30% of 0.0058 e^{-2 delta}.
Usage: ztower_score2.py small_basis.json large_basis.json"""
import sys, json
import numpy as np
from mpmath import mp, mpf, zeta, pi, exp, sqrt, asinh, log, loggamma
mp.dps = 40
def lnxi(s):
    s = mpf(s)
    if s == 1: return log(mpf(1)/2)
    return log(abs(s*(s - 1)/2)) - s/2*log(pi) + loggamma(s/2) + log(abs(zeta(s)))
A = json.load(open(sys.argv[1])); B = json.load(open(sys.argv[2]))
dl = mpf(B["delta"]); T0 = 2*pi*exp(dl); tau = exp(-dl)/(16*pi); c_ref = 0.0058*float(exp(-2*dl))
ok_valid = True; okA = True; okB = True; zs = []; res = []
print(f"delta {float(dl)}  K {A['K']} / {B['K']}   T0 {float(T0):.2f}  2T0 {float(2*T0):.1f}")
print("   d    small-K        large-K        K-agree   |m/P1-1|   |m/N-1|")
for k in sorted(B["layers"], key=int):
    d = int(k); z = mpf(d) + mpf(1)/2; eta = z/(2*T0)
    base = lnxi(d + 1) - lnxi(mpf(1)/2)
    P1 = base + T0*(sqrt(1 + eta**2) - 1 - eta*asinh(eta)); N = base - tau*z**2
    mA = mpf(A["layers"][k]); mB = mpf(B["layers"][k])
    agree = abs(mA/mB - 1) if mB != 0 else abs(mA - mB)
    valid = agree <= 1e-3
    rA = abs(mB/P1 - 1); rN = abs(mB/N - 1)
    if not valid: ok_valid = False
    if valid and rA > 3e-3: okA = False
    if valid and 300 <= d <= 500 and rN <= 3e-3: okB = False
    if valid and d > 0: zs.append(float(z)); res.append(float(mB - P1))
    print(f"{d:4d}  {float(mA):13.6f}  {float(mB):13.6f}   {float(agree):.1e}{'' if valid else ' VOID'}   {float(rA):.2e}   {float(rN):.2e}")
zs = np.array(zs); res = np.array(res)
c = -np.sum(res*zs**2)/np.sum(zs**4)
okC = abs(c/c_ref - 1) <= 0.3
print(f"validity (bases agree <= 1e-3): {'yes' if ok_valid else 'NO (void layers marked)'}")
print(f"(A) P1 within 3e-3 for all valid d <= 500: {'PASS' if okA else 'FAIL'}")
print(f"(B) Gaussian null off by > 3e-3 for all valid 300 <= d <= 500: {'PASS (null fails)' if okB else 'FAIL (null survives)'}")
print(f"(C) residual coefficient c = {c:.3e} vs 0.0058 e^(-2 delta) = {c_ref:.3e} (ratio {c/c_ref:.3f}): {'PASS' if okC else 'FAIL'}")
