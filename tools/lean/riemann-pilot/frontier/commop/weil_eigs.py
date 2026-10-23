#!/usr/bin/env python3
"""Low eigenvectors of Weil's form on [-a,a], both parities, as coefficient vectors
(even: cos(k pi t/a), k=0..K-1; odd: sin(k pi t/a), k=1..K-1). Saves JSON (float64 coeffs, mp eigenvalues)."""
import sys, json
sys.path.insert(0, __import__('os').path.join(__import__('os').path.dirname(__import__('os').path.abspath(__file__)), '../../../../research'))
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
def eig(G, N, k, d, m):
    D = [1/mp.sqrt(tomp(N[i], d)) for i in range(k)]
    S = mp.matrix(k, k)
    for i in range(k):
        for j in range(k): S[i, j] = D[i]*tomp(G[i, j], d)*D[j]
    E, V = mp.eigsy(S)
    idx = sorted(range(k), key=lambda i: E[i])[:m]
    # coefficient c_i of basis function phi_i: v = sum c_i phi_i with c_i = D[i]*V[i,j]  (unit L2 norm)
    return [(E[j], [float(D[i]*V[i, j]) for i in range(k)]) for j in idx]
delta, K, prec, d, m = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
mp.mp.dps = d
Ge, Ne, _ = W.gram(delta, K, prec); Go, No, _ = WO.gram_odd(delta, K + 1, prec)
ev = eig(Ge, Ne, K, d, m); od = eig(Go, No, K, d, m)
out = {"delta": delta, "K": K,
       "even": [{"lam": mp.nstr(l, 8), "c": c} for l, c in ev],
       "odd": [{"lam": mp.nstr(l, 8), "c": c} for l, c in od]}
json.dump(out, open(f"eigs_{delta}_{K}.json", "w"))
print(json.dumps({"delta": delta, "even": [x["lam"] for x in out["even"]], "odd": [x["lam"] for x in out["odd"]]}))
