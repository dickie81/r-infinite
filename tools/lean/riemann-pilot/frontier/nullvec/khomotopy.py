#!/usr/bin/env python3
"""Round 145: the pole-strength homotopy Q_t = Q0 + t*pole.  Even: G_e(t) = G_e - 2(1-t) P P^T; odd: G_o(t) = G_o + 2(1-t) p p^T.
Reports lam_e(t), lam_o(t) on a grid, the positivity window [1-eps_e, 1+eps_o] and the parity crossing t*."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
delta, K, prec, d = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = d; a = mp.mpf(delta)/2
Ge, Ne, _ = W.gram(delta, K, prec); Go, No, _ = WO.gram_odd(delta, K + 1, prec)
ge = mp.matrix([[tomp(Ge[i, j], d) for j in range(K)] for i in range(K)]); ne = [tomp(x, d) for x in Ne]
go = mp.matrix([[tomp(Go[i, j], d) for j in range(K)] for i in range(K)]); no = [tomp(x, d) for x in No[:K]]
Pe = [mp.re(2*mp.sinh((mp.mpf(1)/2 + 1j*k*mp.pi/a)*a)/(mp.mpf(1)/2 + 1j*k*mp.pi/a)) for k in range(K)]
Po = [mp.im(2*mp.sinh((mp.mpf(1)/2 + 1j*k*mp.pi/a)*a)/(mp.mpf(1)/2 + 1j*k*mp.pi/a)) for k in range(1, K + 1)]
def low(G, N, P, s, t):          # s = -1 even (remove +2PP^T), +1 odd (remove -2pp^T)
    k = len(N); D = [1/mp.sqrt(x) for x in N]
    S = mp.matrix(k, k)
    for i in range(k):
        for j in range(k): S[i, j] = D[i]*(G[i, j] + s*2*(1 - t)*P[i]*P[j])*D[j]
    E, V = mp.eigsy(S); i0 = min(range(k), key=lambda i: E[i])
    v = [V[m, i0]*D[m] for m in range(k)]
    return E[i0], mp.fsum(v[m]*P[m] for m in range(k))**2
le, Ce2 = low(ge, ne, Pe, -1, 1); lo, So2 = low(go, no, Po, 1, 1)
eps_e = le/(2*Ce2); eps_o = lo/(2*So2)                       # Hellmann-Feynman: d lam_e/dt = 2C^2, d lam_o/dt = -2S^2
grid = {}
for t in [0, 0.5, 0.9, 0.99]:
    grid[str(t)] = [mp.nstr(low(ge, ne, Pe, -1, t)[0], 5), mp.nstr(low(go, no, Po, 1, t)[0], 5)]
tstar = 1 + (lo - le)/(2*Ce2 + 2*So2)
print(json.dumps({"delta": delta, "K": K, "lam_e(1)": mp.nstr(le, 5), "lam_o(1)": mp.nstr(lo, 5), "2C_e^2": mp.nstr(2*Ce2, 5), "2S_o^2": mp.nstr(2*So2, 5),
  "eps_e": mp.nstr(eps_e, 5), "eps_o": mp.nstr(eps_o, 5), "t* - 1 (parity crossing)": mp.nstr(tstar - 1, 5),
  "grid t: [lam_e(t), lam_o(t)]": grid}), flush=True)
