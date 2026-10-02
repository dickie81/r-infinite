"""Round 47: a structural route to simplicity.  Non-simplicity of Q's even ground state forces an even
Q0-eigenfunction v at level lambda1(Q) with v _|_ phi0 (Q0's positive ground state) and <c, v> = 0, c = cosh(t/2)
(UniquenessQ.groundState_unique_or_excited).  <c, v> = <c - kappa*phi0, v> for every kappa.  If c/phi0 is increasing
in |t| and v has exactly one sign change in |t| on (0, a), choosing kappa = c(r)/phi0(r) at the sign change r makes
(c - kappa*phi0) v one-signed, so <c, v> != 0.  This script measures, per delta: monotonicity of phi0 and of c/phi0 on
[0, a]; sign changes of the first few even Q0-eigenfunctions on (0, a) (Sturm-type counts k-1?); and the overlaps."""
import sys, json, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram
from flint import arb, acb, ctx
import mpmath as mp
d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
jit = sys.argv[4] if len(sys.argv) > 4 else None
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
    return [E[i] for i in idx], [[Q[r, i] / mp.sqrt(Nv[r]) for r in range(K)] for i in idx]
E, V = spec(Gm)
M0 = Gm.copy()
for i in range(K):
    for j in range(K): M0[i, j] -= 2 * Pv[i] * Pv[j]
E0, V0 = spec(M0)
NS = 2000
us = [mp.mpf(a) * j / NS for j in range(NS + 1)]
def vals(v):
    return [sum(v[k] * mp.cos(k * mp.pi * u / a) for k in range(K)) for u in us]
def sign_changes(f):
    m = max(abs(x) for x in f); tol = m * mp.mpf(10) ** (-8)
    s = [1 if x > tol else (-1 if x < -tol else 0) for x in f]
    s = [x for x in s if x != 0]
    return sum(1 for i in range(1, len(s)) if s[i] != s[i - 1])
f0 = vals(V0[0]); s0 = 1 if f0[0] > 0 else -1; f0 = [s0 * x for x in f0]
c = [mp.cosh(u / 2) for u in us]
dec = all(f0[i + 1] <= f0[i] * (1 + mp.mpf(10) ** -12) for i in range(NS))
ratio = [c[i] / f0[i] for i in range(NS + 1)]
rinc = all(ratio[i + 1] > ratio[i] for i in range(NS))
out = dict(delta=d, K=K, prec=p, phi0_min=float(min(f0)), phi0_nonincreasing=dec, c_over_phi0_increasing=rinc,
           phi0_edge_over_centre=float(f0[-1] / f0[0]))
res = []
for k in range(1, 5):
    fk = vals(V0[k])
    ov = sum(Pv[j] * V0[k][j] for j in range(K))
    res.append(dict(k=k + 1, lam_Q0=mp.nstr(E0[k], 5), sign_changes=sign_changes(fk),
                    overlap_c=mp.nstr(ov, 5), overlap_c_rel=mp.nstr(ov / mp.sqrt(mp.mpf(a) + mp.sinh(a)), 5)))
out['Q0_excited'] = res
# crossing condition for psi2: r = its sign change in |t|; need R(u) < R(r) for u < r and R(u) > R(r) for u > r
f2 = vals(V0[1]); m2 = max(abs(x) for x in f2)
idx = [i for i in range(NS) if (f2[i] > 0) != (f2[i + 1] > 0) and max(abs(f2[i]), abs(f2[i + 1])) > m2 * mp.mpf(10) ** -8]
if len(idx) == 1:
    ir = idx[0]
    out['psi2_sign_change_at'] = float(us[ir])
    out['crossing_condition'] = all(ratio[i] < ratio[ir] for i in range(ir)) and all(ratio[i] > ratio[ir + 1] for i in range(ir + 2, NS + 1))
    out['phi0_nonmonotone_first_rise_at'] = next((float(us[i]) for i in range(NS) if f0[i + 1] > f0[i] * (1 + mp.mpf(10) ** -12)), None)
g = vals(V[0])
out['lam1_Q'] = mp.nstr(E[0], 5); out['Q_ground_sign_changes'] = sign_changes(g)
out['margin'] = mp.nstr(E0[1] / E[0], 5) if E[0] > 0 else None
print(json.dumps(out), flush=True)
