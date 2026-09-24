#!/usr/bin/env python3
"""Round 77: compare the measured multiplier M = (ghat/ghat(0))/(Xi/Xi(0)) (explain.py output) with the
reduced problem's closed form. At the wall X = 2 the exterior zero deficit is ln x - tau(x) = arccosh(x/2)
(SixteenPi.lean, tauBal_two), so log M(z) = -(1/2pi) int_{2T0}^inf ln(1 - z^2/r^2) arccosh(r/2T0) dr
= T0 [w arcsin w + sqrt(1 - w^2) - 1], w = z/(2 T0), T0 = 2 pi e^delta.
Usage: multiplier_closed.py explain_results_dX.json"""
import sys, json
from mpmath import mpf, asinh, asin, sqrt, pi, exp, log
d = json.load(open(sys.argv[1])); T0 = 2*pi*exp(d["delta"])
print("delta", d["delta"], " tau_fit*e^delta/(1/16pi) =", d["tau_fit"]*float(exp(d["delta"]))*16*float(pi))
for p in d["imag"]:
    eta = mpf(p["y"])/(2*T0); F = T0*(sqrt(1 + eta**2) - 1 - eta*asinh(eta))
    print(f"imag y/y0={p['y/y0']:<6} logM={p['logM']:<12.5g} closed={float(F):<12.5g} ratio={p['logM']/float(F):.5f} gauss={p['-tau_fit*y^2']:.5g}")
for p in d["real"]:
    w = mpf(p["x"])/(2*T0); F = T0*(w*asin(w) + sqrt(1 - w**2) - 1)
    print(f"real x={p['x']:<5} logM={float(log(p['M'])):<10.5g} closed={float(F):<10.5g} ratio={float(log(p['M'])/F):.4f}")
