#!/usr/bin/env python3
"""Round 139: lam_e(a), lam_o(a) at higher resolution, against the edge-amplitude prediction
   lam_o/lam_e ~ (Phi'(a)/Phi(a))^2 * ||Phi||^2/||Phi'||^2 ."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
def lowest(G, N, k, d):
    D = [1/mp.sqrt(tomp(N[i], d)) for i in range(k)]
    S = mp.matrix(k, k)
    for i in range(k):
        for j in range(k): S[i, j] = D[i]*tomp(G[i, j], d)*D[j]
    return min(mp.eigsy(S, eigvals_only=True))
def Phi(u, m=0):
    return mp.diff(lambda v: mp.nsum(lambda n: (2*mp.pi**2*n**4*mp.e**(4.5*v) - 3*mp.pi*n**2*mp.e**(2.5*v))*mp.e**(-mp.pi*n**2*mp.e**(2*v)), [1, mp.inf]), u, m)
if __name__ == "__main__":
    delta, K, prec, d = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
    mp.mp.dps = d
    Ge, Ne, _ = W.gram(delta, K, prec); Go, No, _ = WO.gram_odd(delta, K + 1, prec)
    le = lowest(Ge, Ne, K, d); lo = lowest(Go, No, K, d)
    mp.mp.dps = 30; a = mp.mpf(delta)/2
    n0 = 2*mp.quad(lambda u: Phi(u)**2, [0, 1, 3]); n1 = 2*mp.quad(lambda u: Phi(u, 1)**2, [0, 1, 3])
    pred = (Phi(a, 1)/Phi(a))**2*n0/n1
    print(json.dumps({"delta": delta, "K": K, "lam_e": mp.nstr(le, 6), "lam_o": mp.nstr(lo, 6),
        "ratio": mp.nstr(lo/le, 6), "pred": mp.nstr(pred, 6), "kappa": mp.nstr(-Phi(a, 1)/Phi(a), 6)}), flush=True)
