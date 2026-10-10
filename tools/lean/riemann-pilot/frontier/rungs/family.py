#!/usr/bin/env python3
"""Rayleigh quotient of the explicit jet family P_{n,c}(D) Phi, P = prod_{k<n} ((2(k+c)+1/2)^2 - D^2),
from saved zero-side tail matrix A and window Gram B in the basis Phi^{(2k)}."""
import pickle, sys, json, mpmath as mp
S = pickle.load(open(sys.argv[1], "rb")); mp.mp.dps = S["dps"]
A = mp.matrix([[mp.mpf(x) for x in r] for r in S["A"]]); B = mp.matrix([[mp.mpf(x) for x in r] for r in S["B"]])
J = A.rows; a = mp.mpf(S["delta"])/2; X = mp.pi*mp.e**(2*a)
def coeffs(n, c):
    p = [mp.mpf(1)]                                     # coefficients in w = D^2
    for k in range(n):
        b2 = (2*(k + c) + mp.mpf(1)/2)**2
        q = [mp.mpf(0)]*(len(p) + 1)
        for i, pi in enumerate(p): q[i] += b2*pi; q[i+1] -= pi
        p = q
    return p
def rq(p):
    n = len(p); v = mp.matrix(p + [0]*(J - n))
    return (v.T*A*v)[0]/(v.T*B*v)[0]
best = {}
for n in [int(x) for x in sys.argv[2].split(",")]:
    if n + 1 > J: continue
    row = []
    for c in [mp.mpf(x) for x in sys.argv[3].split(",")]:
        r = rq(coeffs(n, c)); row.append((mp.nstr(c, 4), mp.nstr(-mp.log(r), 6)))
    print(json.dumps({"delta": S["delta"], "X": mp.nstr(X, 4), "n": n, "-ln RQ by c": row}), flush=True)
