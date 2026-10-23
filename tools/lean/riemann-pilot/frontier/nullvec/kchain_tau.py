#!/usr/bin/env python3
"""Round 80: det H = 1 turns into a law for the multiplier time. With c' = 1/(4 l') (d/d delta) and
c -> kappa_Xi, tau(delta) = kappa_Xi - r = int_delta^inf du/(4 l'(u)) + r'/l'.
Compares tau_meas = kappa_Xi - r with tau_pred (data to the last window, then the tail with
l' ~ 4 pi e^u + off, off fitted on the last windows). Usage: kchain_tau.py file.jsonl"""
import sys, json
from mpmath import mp, mpf, exp, pi, quad, inf
mp.dps = 30
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
d = [mpf(x["delta"]) for x in rows]; l = [mpf(x["lnK00"]) for x in rows]; r = [mpf(x["r"]) for x in rows]
kXi = mpf("0.0231049931")      # sum over zeros of 1/gamma^2
n = len(d)
lp = {i: (l[i + 1] - l[i - 1])/(d[i + 1] - d[i - 1]) for i in range(1, n - 1)}
rp = {i: (r[i + 1] - r[i - 1])/(d[i + 1] - d[i - 1]) for i in range(1, n - 1)}
last = sorted(lp)[-6:]
off = sum(lp[i] - 4*pi*exp(d[i]) for i in last)/len(last)
print("offset l' - 4 pi e^delta on the last windows:", float(off))
tail = quad(lambda u: 1/(4*(4*pi*exp(u) + off)), [d[max(lp)], inf])
print(" delta   tau_meas     tau_pred     ratio    (tau-e^-d/16pi)e^2d meas / pred")
for i in sorted(lp):
    if i < 4 or i > max(lp) - 1: continue
    js = [j for j in sorted(lp) if j >= i]
    integ = sum((d[j + 1] - d[j])*(1/(4*lp[j]) + 1/(4*lp[j + 1]))/2 for j in js[:-1])
    tp = integ + tail + rp[i]/lp[i]
    tm = kXi - r[i]
    g = exp(-d[i])/(16*pi)
    print(f"{float(d[i]):5.2f}  {float(tm):.6e}  {float(tp):.6e}  {float(tm/tp):.4f}   {float((tm-g)*exp(2*d[i])):8.5f} / {float((tp-g)*exp(2*d[i])):8.5f}")
