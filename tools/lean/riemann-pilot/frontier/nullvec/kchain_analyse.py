#!/usr/bin/env python3
"""Round 80: extract the diagonal Hamiltonian of the window chain from kchain.py output.
With X = K00 (= int h1), c = dK02/dK00, window variable a = delta/2:
  h1 = dK00/da,  h2 = (dc/da)/K00,  det H = h1 h2 = 4 l' c'   (primes: d/d delta, l = ln K00).
Rank-one test (canonical-system structure): (s - r^2) l'^2 + (s' - 2 r r') l' - r'^2 = 0.
Prediction from the clues: l ~ 4 pi e^delta, c ~ kappa_Xi - e^{-delta}/(16 pi), det H -> 1.
Usage: kchain_analyse.py file.jsonl"""
import sys, json
from mpmath import mp, mpf, exp, pi, log
mp.dps = 30
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
d = [mpf(x["delta"]) for x in rows]; l = [mpf(x["lnK00"]) for x in rows]
r = [mpf(x["r"]) for x in rows]; s = [mpf(x["s"]) for x in rows]
kXi = mpf("0.023105")
def der(y, i):
    return (y[i + 1] - y[i - 1])/(d[i + 1] - d[i - 1])
c = [None]*len(d)
for i in range(1, len(d) - 1):
    c[i] = r[i] + der(r, i)/der(l, i)
logs = sorted(set(round(float(log(n)), 4) for n in range(2, 30) if all(n % p for p in range(2, n)) or any(n == p**k for p in range(2, 30) for k in range(2, 6))))
print(" delta    l'      4pi e^d   r        c        kXi-e^-d/16pi  rank1/r'^2   detH=4l'c'   prime entering")
for i in range(2, len(d) - 2):
    lp = der(l, i); rp = der(r, i); sp = der(s, i)
    rk = ((s[i] - r[i]**2)*lp**2 + (sp - 2*r[i]*rp)*lp - rp**2)/rp**2
    cp = (c[i + 1] - c[i - 1])/(d[i + 1] - d[i - 1])
    det = 4*lp*cp
    mark = [f"log {round(float(exp(x)))}" for x in logs if abs(x - float(d[i])) < 0.026]
    print(f"{float(d[i]):5.2f} {float(lp):8.3f} {float(4*pi*exp(d[i])):8.3f} {float(r[i]):.6f} {float(c[i]):.6f} {float(kXi - exp(-d[i])/(16*pi)):.6f}    {float(rk): .2e}   {float(det):8.4f}   {' '.join(mark)}")
