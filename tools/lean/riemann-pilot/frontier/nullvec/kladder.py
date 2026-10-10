#!/usr/bin/env python3
"""Round 152: the low spectrum as a ladder? Lowest 3 even and 3 odd eigenvalues of Weil's form on [-a,a],
merged in increasing order, with ratios to kappa^2, kappa = -Phi'(a)/Phi(a)."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
from klimit_gap import Phi
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
def eigs(G, N, k, d):
    D = [1/mp.sqrt(tomp(N[i], d)) for i in range(k)]
    S = mp.matrix(k, k)
    for i in range(k):
        for j in range(k): S[i, j] = D[i]*tomp(G[i, j], d)*D[j]
    return sorted(mp.eigsy(S, eigvals_only=True))
delta, K, prec, d = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = d
Ge, Ne, _ = W.gram(delta, K, prec); Go, No, _ = WO.gram_odd(delta, K + 1, prec)
ee = eigs(Ge, Ne, K, d)[:3]; eo = eigs(Go, No, K, d)[:3]
lev = sorted([(x, 'e') for x in ee] + [(x, 'o') for x in eo], key=lambda t: t[0])
mp.mp.dps = 30; a = mp.mpf(delta)/2; kap = -Phi(a, 1)/Phi(a)
out = {"delta": delta, "K": K, "kappa": mp.nstr(kap, 5), "T*": mp.nstr(2*mp.pi*mp.e**(2*a), 5),
  "levels": [(p, mp.nstr(x, 5)) for x, p in lev],
  "ratio/kappa^2": [mp.nstr(lev[i + 1][0]/lev[i][0]/kap**2, 4) for i in range(len(lev) - 1)]}
print(json.dumps(out), flush=True)
