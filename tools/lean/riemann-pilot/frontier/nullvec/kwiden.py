#!/usr/bin/env python3
"""Round 144: widened-support transfer.  o = odd minimiser at a' = a-b, q = int o, g_b = cosh(b/2) q - (q(.+b)+q(.-b))/2
(even, supp [-a,a], ghat_b = (cosh(b/2) - cos bz) qhat, pole-free).  Measures: the odd-side pole term (1/2) qhat(i/2)^2
against lam_o(a'); Rayleigh(g_b) at support a; lam_e(a), lam_o(a), lam_o(a')."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
import weil_prime_gram as W, weil_prime_gram_odd as WO
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
def mats(delta, K, prec, d, odd):
    G, N, _ = (WO.gram_odd(delta, K + 1, prec) if odd else W.gram(delta, K, prec))
    return mp.matrix([[tomp(G[i, j], d) for j in range(K)] for i in range(K)]), [tomp(N[i], d) for i in range(K)]
def ground(G, N):
    k = len(N); D = [1/mp.sqrt(x) for x in N]
    S = mp.matrix(k, k)
    for i in range(k):
        for j in range(k): S[i, j] = D[i]*G[i, j]*D[j]
    E, V = mp.eigsy(S); i0 = min(range(k), key=lambda i: E[i])
    return E[i0], [V[m, i0]*D[m] for m in range(k)]
a_, b_, K, prec, d = [float(x) for x in sys.argv[1:3]] + [int(x) for x in sys.argv[3:6]]
mp.mp.dps = d; a = mp.mpf(a_); b = mp.mpf(b_); ap = a - b
Ge, Ne = mats(2*a_, K, prec, d, False); Go, No = mats(2*a_, K, prec, d, True); Gp, Np = mats(2*float(ap), K, prec, d, True)
le, _ = ground(Ge, Ne); lo, _ = ground(Go, No); lop, co = ground(Gp, Np)
om = [k*mp.pi/ap for k in range(K + 1)]
def q(t):
    t = abs(t)
    if t >= ap: return mp.mpf(0)
    return mp.fsum(co[k - 1]*(mp.cos(om[k]*ap) - mp.cos(om[k]*t))/om[k] for k in range(1, K + 1))
mp.mp.dps = 30
C = 2*mp.quad(lambda t: q(t)*mp.cosh(t/2), mp.linspace(0, ap, 9))
g = lambda t: mp.cosh(b/2)*q(t) - (q(t + b) + q(t - b))/2
# expand g in the cosine basis of [-a,a]: c_k = int g cos / N_k
nodes = sorted(set([mp.mpf(0), a] + [ap - b, ap, b, ap + b][:4] + list(mp.linspace(0, a, 13))))
nodes = [x for x in nodes if 0 <= x <= a]
omA = [k*mp.pi/a for k in range(K)]
c = [2*mp.quad(lambda t: g(t)*mp.cos(omA[k]*t), nodes)/Ne[k] for k in range(K)]
mp.mp.dps = d
num = mp.fsum(c[i]*Ge[i, j]*c[j] for i in range(K) for j in range(K)); den = mp.fsum(c[i]**2*Ne[i] for i in range(K))
print(json.dumps({"a": a_, "b": b_, "K": K, "lam_e(a)": mp.nstr(le, 5), "lam_o(a)": mp.nstr(lo, 5), "lam_o(a-b)": mp.nstr(lop, 5),
  "odd pole (1/2)qhat(i/2)^2": mp.nstr(C**2/2, 5), "symbol integral of o = lam_o(a-b) + pole": mp.nstr(lop + C**2/2, 5),
  "Rayleigh(g_b) at a": mp.nstr(num/den, 5)}), flush=True)
