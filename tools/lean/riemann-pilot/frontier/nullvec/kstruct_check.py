#!/usr/bin/env python3
"""Round 140 checks: (i) min of the even ground state e on [-a,a] (sign);
(ii) ||q||^2 for q = int_{-a}^t o, ||o|| = 1 (so ||q'||/||q|| vs gamma_1 = 14.1347)."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
def ground(G, N, k, d):
    D = [1/mp.sqrt(tomp(N[i], d)) for i in range(k)]
    S = mp.matrix(k, k)
    for i in range(k):
        for j in range(k): S[i, j] = D[i]*tomp(G[i, j], d)*D[j]
    E, V = mp.eigsy(S); i0 = min(range(k), key=lambda i: E[i])
    return E[i0], [V[m, i0]*D[m] for m in range(k)]
delta, K, prec, d = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = d; a = mp.mpf(delta)/2
le, ce = ground(*W.gram(delta, K, prec)[:2], K, d)
Go, No, _ = WO.gram_odd(delta, K + 1, prec); lo, co = ground(Go, No, K, d)
om = [k*mp.pi/a for k in range(K + 1)]
e = lambda t: mp.fsum(ce[k]*mp.cos(om[k]*t) for k in range(K))
o = lambda t: mp.fsum(co[k - 1]*mp.sin(om[k]*t) for k in range(1, K + 1))
if e(0) < 0: ce = [-x for x in ce]
if o(a/2) < 0: co = [-x for x in co]
ts = [a*i/400 for i in range(401)]
emin = min((e(t), t) for t in ts)
q = lambda t: mp.fsum(co[k - 1]*(mp.cos(om[k]*a) - mp.cos(om[k]*t))/om[k] for k in range(1, K + 1))
mp.mp.dps = 30
nq = 2*mp.quad(lambda t: q(t)**2, mp.linspace(0, a, 9))
print(json.dumps({"delta": delta, "K": K, "e_min": mp.nstr(emin[0], 5), "at": mp.nstr(emin[1], 4), "e(0)": mp.nstr(e(0), 5), "e(a)": mp.nstr(e(a), 5),
 "||q||^2": mp.nstr(nq, 6), "||q'||/||q||": mp.nstr(1/mp.sqrt(nq), 6),
  "lam_o/lam_e": mp.nstr(lo/le, 5), "RH-chain bound gamma1^2 ||q||^2": mp.nstr(mp.mpf('14.134725141734693')**2*nq, 5)}), flush=True)
