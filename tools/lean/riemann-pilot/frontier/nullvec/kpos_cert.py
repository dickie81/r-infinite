#!/usr/bin/env python3
"""Round 119: certified positivity of the prime-side (unconditional) window form on the K-dimensional cosine subspace.
Every entry is an arb enclosure (digamma/Hurwitz zeta by arb, exact primes, exact decimal x, rigorous remainder on the geometric
series). A Cholesky factorisation in which every pivot's enclosure is strictly positive certifies that the K x K Gram matrix is
positive definite, i.e. Q(g) > 0 for every nonzero g = sum_{k<K} c_k cos(k pi u/a) on [-a, a], a = ln(x)/2. (Pivots are not
eigenvalues: the smallest pivot is only an upper bound on nothing useful and a lower bound on nothing; it is reported for scale.)
Caveat: the closed forms are derived by hand (kprimeside.py docstring) and checked to 5e-16 against independent quadrature
(kps_indep.py), not formally proved. Usage: kpos_cert.py Kfac x1 x2 ..."""
import sys, json, math
from flint import arb, ctx
import kps_chol as C
Kf = float(sys.argv[1])
for xv in map(float, sys.argv[2:]):
    K = max(40, int(Kf*xv) + 40); prec0 = int(96 + 2.1*4*math.pi*xv*1.4427); res = None
    for fac in (1, 1.5, 2, 3):
        with ctx.workprec(int(prec0*fac)):
            A = C.build(xv, K); bad, piv = C.chol_pivots(A)
            if bad is None:
                lo = min(float(p.lower()) for p in piv)
                res = {"x": xv, "K": K, "prec": int(prec0*fac), "certified_PD": True, "min_pivot_lower": lo,
                       "log10_min_pivot": round(math.log10(lo), 2)}
                break
            elif piv[bad].upper() < 0:
                res = {"x": xv, "K": K, "prec": int(prec0*fac), "certified_PD": False, "negative_pivot_at": bad, "pivot": piv[bad].str(5)}; break
    if res is None: res = {"x": xv, "K": K, "certified_PD": None, "note": "undecided at 3x precision"}
    print(json.dumps(res), flush=True)
