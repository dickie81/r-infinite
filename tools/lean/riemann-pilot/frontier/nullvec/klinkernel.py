#!/usr/bin/env python3
"""Round 106: first-order kernel w_x = -2 F F'/s and g = F'^2/s at every quantile node (Gamma chain), enclosed to 1e-10.
Usage: klinkernel.py HC QFILE unused Kfac x1 ...  (helpers from klinresp3.py)"""

import sys, json, math
from flint import arb, arb_mat, ctx
import mpmath as mp
import os
LQ = float(os.environ.get('LCOND', '1'))   # round 111: conductor of the L-function whose smooth tail is used (1 = zeta)
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
                t = mp.exp(u); tq.append((arb(str(t)), arb(str(w*t*mp.log(LQ*t/(2*mp.pi))/(2*mp.pi)/2))))
        a = arb(d)/2; pi = arb.pi(); om = [arb(k)*pi/a for k in range(K)]; om2 = [w*w for w in om]; sg = [1 if k % 2 == 0 else -1 for k in range(K)]
        T = [arb(g) for g in ZQ]; F = arb_mat(N + len(tq), K)
        for i, t in enumerate(T):
            r0 = rowderivs(t, a, om, K, 0)[0]
            for k in range(K): F[i, k] = r0[k]
        for j, (t, w) in enumerate(tq):
            s2 = 2*t*w.sqrt(); t2 = t*t
            for k in range(K): F[N + j, k] = sg[k]*s2/(t2 - om2[k])
        M = F.transpose()*F; e = arb_mat(K, 1); e[0, 0] = arb(1); y = M.solve(e); s = y[0, 0]; yl = [y[k, 0] for k in range(K)]
        W, G, rad = [], [], 0.0
        for i, t in enumerate(T):
            R = rowderivs(t, a, om, K, 1)
            F0 = sum((R[0][k]*yl[k] for k in range(K)), arb(0)); F1 = sum((R[1][k]*yl[k] for k in range(K)), arb(0))
            w = -2*F0*F1/s; g = F1*F1/s; rad = max(rad, float(w.rad())); W.append(float(w.mid())); G.append(float(g.mid()))
        return {"x": xv, "K": K, "prec": prec, "w": W, "g": G, "wrad": rad}
for xv in map(float, sys.argv[5:]):
    for pf in (1, 2, 3, 4):
        out = compute(xv, pf)
        if out["wrad"] < 1e-10: break
    out["prec_factor"] = pf; print(json.dumps(out), flush=True)
