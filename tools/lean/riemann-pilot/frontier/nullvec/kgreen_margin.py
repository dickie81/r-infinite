#!/usr/bin/env python3
"""Round 149: how close is the even ground state to a Green-pair degeneracy?
Degeneracy <=> lam1(Q) = lam_perp := min{Q(h): h pole-free} (<= lam2(Q0)); at such a point the pole-free
minimiser w is Theorem D's w. Measures lam1(Q), lam_perp, lam2(Q0), the pole overlap p2 of phi2(Q0), and
the angle between the pole-free minimiser w and its Green partner Gw's projection onto the Q-ground space."""
import sys, json
sys.path.insert(0, "/tmp/claude-0/-home-user-r-infinite/995f457d-116a-5074-b5df-24e4b213812a/scratchpad/wt-review/tools/research")
import mpmath as mp
from flint import arb, acb, ctx
import weil_prime_gram as W
tomp = lambda x, d: mp.mpf(x.mid().str(d + 10, radius=False))
delta, K, prec, d = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
mp.mp.dps = d
G, N, _ = W.gram(delta, K, prec)
with ctx.workprec(prec):
    half = arb(1)/2; aa = arb(delta)/2
    pv = [(2*(acb(half, arb(k)*arb.pi()/aa)*aa).sinh()/acb(half, arb(k)*arb.pi()/aa)).real for k in range(K)]
D = [1/mp.sqrt(tomp(x, d)) for x in N]
S = mp.matrix(K, K)
for i in range(K):
    for j in range(K): S[i, j] = D[i]*tomp(G[i, j], d)*D[j]
p = mp.matrix([D[k]*tomp(pv[k], d) for k in range(K)])
S0 = S - 2*p*p.T
E, V = mp.eigsy(S); lam1 = min(E)
E0, V0 = mp.eigsy(S0); o = sorted(range(K), key=lambda i: E0[i])
lam2Q0 = E0[o[1]]; phi2 = V0[:, o[1]]
pn = mp.sqrt((p.T*p)[0, 0]); p2 = abs((phi2.T*p)[0, 0])/pn
# orthonormal basis of p^perp: Householder
u = p.copy(); u[0] += (1 if p[0] >= 0 else -1)*pn
H = mp.eye(K) - 2*u*u.T/((u.T*u)[0, 0])
B = H[:, 1:]                                   # columns span p^perp
Sp = B.T*S*B
Ep, Vp = mp.eigsy(Sp); ip = min(range(K - 1), key=lambda i: Ep[i])
lamperp = Ep[ip]
print(json.dumps({"delta": delta, "K": K, "lam1": mp.nstr(lam1, 6), "lam_perp": mp.nstr(lamperp, 6),
  "lam2(Q0)": mp.nstr(lam2Q0, 6), "lam_perp/lam1": mp.nstr(lamperp/lam1, 6),
  "pole overlap of phi2(Q0)": mp.nstr(p2, 6)}), flush=True)
# the Green partner of the pole-free minimiser w: coefficients d_k = -c_k/(omega_k^2 + 1/4)
vp = Vp[:, ip]
cw = B*vp                                        # normalised coordinates
c = [cw[k]*D[k] for k in range(K)]               # cosine coefficients of w
a = mp.mpf(delta)/2
om = [k*mp.pi/a for k in range(K)]
dk = [-c[k]/(om[k]**2 + mp.mpf(1)/4) for k in range(K)]
Nm = [tomp(x, d) for x in N]
Gm = mp.matrix(K, K)
for i in range(K):
    for j in range(K): Gm[i, j] = tomp(G[i, j], d)
num = mp.fsum(dk[i]*Gm[i, j]*dk[j] for i in range(K) for j in range(K))
den = mp.fsum(dk[k]**2*Nm[k] for k in range(K))
# pole value of Gw and overlaps with the ground state g and with w
i1 = min(range(K), key=lambda i: E[i]); g = [V[k, i1]*D[k] for k in range(K)]
ip_ = lambda x, y: mp.fsum(x[k]*y[k]*Nm[k] for k in range(K))
ngw = mp.sqrt(den)
print(json.dumps({"delta": delta, "Rayleigh(Gw)": mp.nstr(num/den, 6), "Rayleigh(Gw)/lam1": mp.nstr(num/den/lam1, 6),
  "Rayleigh(Gw)/lam_perp": mp.nstr(num/den/lamperp, 6),
  "cos(Gw, g)": mp.nstr(abs(ip_(dk, g))/ngw, 8), "cos(Gw, w)": mp.nstr(abs(ip_(dk, c))/(ngw*mp.sqrt(ip_(c, c))), 8)}), flush=True)
