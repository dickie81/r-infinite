#!/usr/bin/env python3
"""Round 105: response of ln K_a(0,0) to zero displacements about the smooth-quantile (pure-Gamma) chain, to THIRD order
(PREREG_linresp3.md). Nodes below HC individually; above HC the fixed smooth tail of kzeroside2.py.
Usage: klinresp3.py HC QFILE SETS Kfac x1 x2 ...   SETS = comma list of name=file ('true' = the zeta zeros)."""
import sys, json, math
from flint import arb, arb_mat, ctx
import mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre
HC, qf, sets, Kf = float(sys.argv[1]), sys.argv[2], sys.argv[3], float(sys.argv[4]); HMAX, NQ = 6997.0, 3
ZQ = [g for g in json.load(open(qf)) if g < HC]; N = len(ZQ)
DT = {}
for item in sets.split(","):
    nm, f = item.split("=")
    z = [g for g in json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json" if f == "true" else f)) if g < HC]
    z = z + ZQ[len(z):]; assert len(z) == N, (nm, len(z), N); DT[nm] = z
from math import factorial
_FACT = None
def sincd(z, n, S=None, C=None):
    """n-th derivative (n <= 3) of sinc(z) = sin z / z; power series for |z| < 1/2 (the removable point), closed form otherwise."""
    if abs(z) < 0.5:
        tot = arb(0)
        for m in range(n//2, 160):
            p = 2*m - n
            if p < 0: continue
            tot += (-1)**m * z**p * arb(factorial(2*m)//factorial(2*m - n) if n else 1) / arb(factorial(2*m + 1))
        return tot
    if S is None: S, C = z.sin(), z.cos()
    if n == 0: return S/z
    if n == 1: return C/z - S/z**2
    if n == 2: return -S/z - 2*C/z**2 + 2*S/z**3
    return -C/z + 3*S/z**2 + 6*C/z**3 - 6*S/z**4
def rowderivs(t, a, om, K, upto):
    """phi_k(t) = g(t - om_k) + g(t + om_k), g(u) = sin(a u)/u = a sinc(a u)  (round 105 fix: no removable-singularity blow-up)."""
    out = [[None]*K for _ in range(upto + 1)]
    S0, C0 = (t*a).sin(), (t*a).cos(); apow = [a**(n + 1) for n in range(upto + 1)]
    for k in range(K):
        um, up = a*(t - om[k]), a*(t + om[k]); S = S0 if k % 2 == 0 else -S0; C = C0 if k % 2 == 0 else -C0   # sin(a t -+ k pi)
        for n in range(upto + 1):
            out[n][k] = apow[n]*(sincd(um, n, S, C) + sincd(up, n, S, C))
    return out
def compute(xv, pf):
    d = math.log(xv); K = max(40, int(Kf*xv) + 40); prec = int((96 + 2.1*4*math.pi*xv*1.4427)*pf)
    with ctx.workprec(prec):
        mp.mp.prec = prec; tq = []; L0, L1 = math.log(HC), math.log(HMAX)
        for p in range(24):
            for u, w in GaussLegendre(mp.mp).get_nodes(mp.mpf(L0 + (L1 - L0)*p/24), mp.mpf(L0 + (L1 - L0)*(p + 1)/24), NQ, mp.mp.prec):
                t = mp.exp(u); tq.append((arb(str(t)), arb(str(w*t*mp.log(t/(2*mp.pi))/(2*mp.pi)/2))))
        a = arb(d)/2; pi = arb.pi(); om = [arb(k)*pi/a for k in range(K)]; om2 = [w*w for w in om]; sg = [1 if k % 2 == 0 else -1 for k in range(K)]
        T = [arb(g) for g in ZQ]
        F = arb_mat(N + len(tq), K)
        for i, t in enumerate(T):
            r0 = rowderivs(t, a, om, K, 0)[0]
            for k in range(K): F[i, k] = r0[k]
        for j, (t, w) in enumerate(tq):
            s2 = 2*t*w.sqrt(); t2 = t*t
            for k in range(K): F[N + j, k] = sg[k]*s2/(t2 - om2[k])
        M = F.transpose()*F; e = arb_mat(K, 1); e[0, 0] = arb(1); y = M.solve(e); s = y[0, 0]
        yl = [y[k, 0] for k in range(K)]
        # pass 2: F-derivatives at every node (independent of the displacement set)
        Fd = []
        for i, t in enumerate(T):
            R = rowderivs(t, a, om, K, 3); Fd.append([sum((R[n][k]*yl[k] for k in range(K)), arb(0)) for n in range(4)])
        out = {"x": xv, "K": K, "nodes": N, "lnK_base": ((2*a)**2*s).log().mid().str(15, radius=False)}
        for nm, Z in DT.items():
            dl = [arb(z) - q for z, q in zip(Z, T)]
            a1 = sum((2*Fd[i][0]*Fd[i][1]*dl[i] for i in range(N)), arb(0))
            a2 = sum(((Fd[i][0]*Fd[i][2] + Fd[i][1]**2)*dl[i]**2 for i in range(N)), arb(0))
            e3 = sum(((Fd[i][0]*Fd[i][3]/3 + Fd[i][1]*Fd[i][2])*dl[i]**3 for i in range(N)), arb(0))
            v1 = arb_mat(K, 1); v2 = arb_mat(K, 1)
            for i, t in enumerate(T):
                if dl[i] == 0: continue
                R = rowderivs(t, a, om, K, 2); F0, F1, F2 = Fd[i][0], Fd[i][1], Fd[i][2]; d1, d2 = dl[i], dl[i]**2/2
                for k in range(K):
                    v1[k, 0] += d1*(R[1][k]*F0 + R[0][k]*F1); v2[k, 0] += d2*(R[2][k]*F0 + 2*R[1][k]*F1 + R[0][k]*F2)
            z = M.solve(v1); q = (v1.transpose()*z)[0, 0]; c12 = (v2.transpose()*z)[0, 0]
            zl = [z[k, 0] for k in range(K)]; t3 = arb(0)
            for i, t in enumerate(T):
                if dl[i] == 0: continue
                R = rowderivs(t, a, om, K, 1)
                t3 += 2*dl[i]*sum((R[0][k]*zl[k] for k in range(K)), arb(0))*sum((R[1][k]*zl[k] for k in range(K)), arb(0))
            s1 = -a1; s2_ = -a2 + q; s3 = -e3 + 2*c12 - t3
            D1 = s1/s; D2 = D1 + s2_/s - s1*s1/(2*s*s); D3 = D2 + s3/s - s1*s2_/(s*s) + s1**3/(3*s**3)
            out[f"d1_{nm}"] = float(D1.mid()); out[f"d2_{nm}"] = float(D2.mid()); out[f"d3_{nm}"] = float(D3.mid()); out[f"rad_{nm}"] = max(float(D2.rad()), float(D3.rad())); out["prec"] = prec
        return out

# round 105 fix 2: the second-order diagonal and re-optimisation terms are individually huge (~1e73 at x = 17) and cancel;
# raise the working precision until every reported order is enclosed to 1e-8.
for xv in map(float, sys.argv[5:]):
    for pf in (1, 2, 3, 4, 6, 8):
        out = compute(xv, pf)
        if max(v for k, v in out.items() if k.startswith("rad_")) < 1e-8: break
    out["prec_factor"] = pf
    print(json.dumps(out), flush=True)
