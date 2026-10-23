"""Jacobi (Krylov) rotation from the pole vector.  In orthonormal cosine coordinates y = N^{1/2} x:
S0 = N^{-1/2}(G - 2pp^T)N^{-1/2} (the pole-free form Q0), q = N^{-1/2}p (the pole: <c,f> = q.y), S = S0 + 2qq^T (= Q).
Lanczos on S0 from q/|q| gives an orthonormal basis in which S0 and S are tridiagonal (the pole only changes T[0,0]).
Off-diagonals b_k >= 0; flip signs -> nonpositive: an irreducible Jacobi matrix is Perron-Frobenius, so every eigenvalue
of Q on the cyclic subspace is simple and the ground state is one-signed there.  Breakdown (b_k = 0) = non-cyclic c."""
import sys, json
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram
from flint import arb, acb, ctx
import mpmath as mp
d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
G, N, pp = gram(d, K, p)
with ctx.workprec(p):
    aa = arb(d) / 2; half = arb(1) / 2
    P = [(2 * (acb(half, arb(k) * arb.pi() / aa) * aa).sinh() / acb(half, arb(k) * arb.pi() / aa)).real for k in range(K)]
mp.mp.dps = int(p * 0.28)
cv = lambda x: mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1])))
Nv = [cv(x) for x in N]; Pv = [cv(x) for x in P]
S = mp.matrix(K, K)
for i in range(K):
    for j in range(K): S[i, j] = cv(G[i, j]) / mp.sqrt(Nv[i] * Nv[j])
q = mp.matrix([Pv[i] / mp.sqrt(Nv[i]) for i in range(K)])
S0 = S - 2 * q * q.T
# Lanczos with full reorthogonalisation
V = []; a = []; b = []
v = q / mp.norm(q)
for k in range(K):
    V.append(v)
    w = S0 * v
    ak = (v.T * w)[0]; a.append(ak)
    for u in V: w = w - (u.T * w)[0] * u
    for u in V: w = w - (u.T * w)[0] * u
    bk = mp.norm(w)
    if k < K - 1:
        b.append(bk)
        v = w / bk
T = mp.matrix(K, K)
for k in range(K): T[k, k] = a[k]
for k in range(K - 1): T[k, k + 1] = T[k + 1, k] = -b[k]          # gauge: nonpositive off-diagonals
T[0, 0] += 2 * mp.norm(q) ** 2                                       # the pole enters only here
E, R = mp.eigsy(T)
idx = sorted(range(K), key=lambda i: E[i])
g = [R[r, idx[0]] for r in range(K)]
sgn = 1 if g[0] > 0 else -1
E0, R0 = mp.eigsy(S0)
i0 = sorted(range(K), key=lambda i: E0[i])
ov = [abs(sum(q[r] * R0[r, i] for r in range(K))) for i in i0]
Es, _ = mp.eigsy(S)
es = sorted([Es[i] for i in range(K)])
print(json.dumps(dict(delta=d, K=K,
    min_offdiag_b=mp.nstr(min(b), 4), b_first=[mp.nstr(x, 3) for x in b[:5]],
    lanczos_ground_all_positive=all(sgn * x > 0 for x in g), ground_min_component=mp.nstr(min(sgn * x for x in g), 3),
    lam1_Jacobi=mp.nstr(E[idx[0]], 5), lam2_Jacobi=mp.nstr(E[idx[1]], 5), lam1_Q_direct=mp.nstr(es[0], 5), lam2_Q_direct=mp.nstr(es[1], 5),
    min_pole_overlap_over_Q0_eigvecs=mp.nstr(min(ov), 3), overlap_psi2=mp.nstr(ov[1], 3), mu2=mp.nstr(E0[i0[1]], 4))), flush=True)
