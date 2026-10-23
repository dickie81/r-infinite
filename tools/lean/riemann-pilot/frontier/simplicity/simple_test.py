"""Simplicity route for (b).  Connes-van Suijlekom (arXiv 2511.23257): simple isolated even ground state => all zeros
of its transform real.  Perron-Frobenius route to simplicity: split Q = Q0 + 2 <c,g>^2 with c = cosh(t/2) (the pole)
and Q0 = archimedean Dirichlet form - prime shifts (off-diagonal kernel <= 0, Beurling-Deny) => ground state of Q0
positive and simple.  Rank-one secular equation: lambda1(Q) is simple whenever lambda1(Q) < lambda2(Q0) (given
<c, phi1(Q0)> != 0, automatic for positive phi1).  This script measures lambda1(Q), lambda2(Q), lambda1(Q0),
lambda2(Q0), the positivity of phi1(Q0) and of the ground state of Q, and the overlaps <c, phi_k(Q0)>."""
import sys, json
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram
from flint import arb, acb, ctx
import mpmath as mp
d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
a = d / 2
G, N, pp = gram(d, K, p)
with ctx.workprec(p):
    aa = arb(d) / 2; half = arb(1) / 2
    P = [(2 * (acb(half, arb(k) * arb.pi() / aa) * aa).sinh() / acb(half, arb(k) * arb.pi() / aa)).real for k in range(K)]
mp.mp.dps = int(p * 0.28)
cv = lambda x: mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1])))
Gm = mp.matrix(K, K); Pv = [cv(x) for x in P]; Nv = [cv(x) for x in N]
for i in range(K):
    for j in range(K): Gm[i, j] = cv(G[i, j])
def spec(M):
    S = mp.matrix(K, K)
    for i in range(K):
        for j in range(K): S[i, j] = M[i, j] / mp.sqrt(Nv[i] * Nv[j])
    E, Q = mp.eigsy(S)
    idx = sorted(range(K), key=lambda i: E[i])
    vecs = [[Q[r, i] / mp.sqrt(Nv[r]) for r in range(K)] for i in idx]      # coefficient vectors, N-normalised
    return [E[i] for i in idx], vecs
E, V = spec(Gm)
M0 = Gm.copy()
for i in range(K):
    for j in range(K): M0[i, j] -= 2 * Pv[i] * Pv[j]
E0, V0 = spec(M0)
def fmin(v):
    f = lambda u: sum(v[k] * mp.cos(k * mp.pi * u / a) for k in range(K))
    vals = [f(mp.mpf(a) * j / 300) for j in range(301)]
    s = 1 if vals[0] > 0 else -1
    return float(min(s * x for x in vals) / (s * vals[0]))
ov = lambda v: float(sum(Pv[k] * v[k] for k in range(K)))
print(json.dumps(dict(delta=d, K=K,
    lam1_Q=mp.nstr(E[0], 5), lam2_Q=mp.nstr(E[1], 5),
    lam1_Q0=mp.nstr(E0[0], 5), lam2_Q0=mp.nstr(E0[1], 5), lam3_Q0=mp.nstr(E0[2], 5),
    simplicity_margin_lam2Q0_over_lam1Q=mp.nstr(E0[1] / E[0], 5) if E[0] > 0 else None,
    Q0_ground_min_over_center=fmin(V0[0]), Q_ground_min_over_center=fmin(V[0]),
    overlap_c_phi1_Q0=ov(V0[0]), overlap_c_phi2_Q0=ov(V0[1]))), flush=True)
