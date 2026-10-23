"""Round 121 scoping: true lambda_0 (pole-free Q0) and lambda_1 (full Q) at small half-support a, via kprimeside closed forms;
and the analytic lower bound c0 + Far(a) + Near_lb."""
import math, mpmath as mp, kprimeside as ps
from flint import arb, ctx
mp.mp.dps = 60
def lams(a, K=40):
    xv = math.exp(2*a)
    with ctx.workprec(200):
        A = arb(repr(xv)).log()/2    # note: x = e^{2a} as a decimal repr
        w = [arb(k)*arb.pi()/A for k in range(K)]; s = [1 if k % 2 == 0 else -1 for k in range(K)]
        Sv, Sd, Pv, Pd = ps.phi_parts(A, w, K, xv, ps.prime_powers(xv))
        val, dd = list(Sv), list(Sd)
        for p in Pv:
            for k in range(K): val[k] += Pv[p][k]; dd[k] += Pd[p][k]
        M = ps.assemble(K, w, val, dd, s)          # = (1/2) * (Q0 part)
        Pk = [s[k]*(A/2).sinh()/(w[k]*w[k] + arb(1)/4) for k in range(K)]
        aa = float(A.mid())
        Q0 = mp.matrix([[2*mp.mpf(M[j, k].mid().str(50, radius=False)) for k in range(K)] for j in range(K)])
        Pv_ = [mp.mpf(Pk[k].mid().str(50, radius=False)) for k in range(K)]
    Q = Q0 + mp.matrix([[2*Pv_[j]*Pv_[k] for k in range(K)] for j in range(K)])
    Ginv = mp.diag([1/mp.sqrt(2*aa)] + [1/mp.sqrt(aa)]*(K - 1))
    l0 = min(mp.eigsy(Ginv*Q0*Ginv)[0]); l1 = min(mp.eigsy(Ginv*Q*Ginv)[0])
    return float(l0), float(l1)
c0 = float(mp.re(mp.digamma(0.25)) - mp.log(mp.pi))
Far = lambda a: float(mp.quad(lambda u: mp.exp(u/2)/mp.sinh(u), [2*a, 1, mp.inf]))
Cin = lambda x: float(mp.quad(lambda s: (1 - mp.cos(s))/s, [0, x]))
for a in (0.01, 0.02, 0.05, 0.1, 0.15, 0.2, 0.25, 0.3, 0.3466):
    l0, l1 = lams(a)
    near = 0.4092*Cin(math.pi/2) + 0.25*Cin(math.pi) + 0.3408*0 + 0.0908*Cin(1.5*math.pi) - 0.3408*0
    near = 0.4092*Cin(math.pi/2) + 0.25*Cin(math.pi) + (1 - 0.25 - 0.4092 - 0.25)*Cin(1.5*math.pi)
    print(f"a={a:<7} lambda0(Q0)={l0:+.4f}  lambda1(Q)={l1:+.4e}  | c0+Far={c0 + Far(a):+.4f}  near_lb~{near:.3f}  bound={c0 + Far(a) + near:+.4f}")
