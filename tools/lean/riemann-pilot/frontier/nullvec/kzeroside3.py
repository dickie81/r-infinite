#!/usr/bin/env python3
"""Round 99: window-relative band sets on the round-95 fast kernel. At window x, zero k is the true zero if (keep and
c1 <= gamma_k/(4 pi x) < c2) or (drop and not in band), else the smooth quantile (pzeros_0.json). Usage: kzeroside3.py keep|drop c1 c2 Kfac x1 ...
Round 95 docstring follows: Zeros below HCUT enter individually. Above HCUT (to HMAX = 6997, the old truncation)
they enter through their smooth density rho(t) = ln(t/2pi)/(2pi), with sin^2(ta) replaced by its mean 1/2: the rows share
the factor sin(t a), so this is the continuum limit of the tail. Gauss-Legendre in t with NQ nodes.
Usage: kzeroside2.py ZFILE HCUT Kfac x1 x2 ...   (ZFILE: JSON list of zeros; 'true' = the 6700 zeta zeros)"""
import sys, json, math
from flint import arb, arb_mat, ctx
import mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre
mode, c1, c2, Kf = sys.argv[1], float(sys.argv[2]), float(sys.argv[3]), float(sys.argv[4]); HC = 1000.0; zf = f"{mode}_{c1}_{c2}"
import os
ZT = [g for g in json.load(open(os.environ.get("ZTRUE", "../../../../research/checkpoints/zeta_zeros_6700.json"))) if g < HC]  # round 102: ZTRUE overrides the "true" set
ZQ = json.load(open("pzeros_0.json"))
if len(ZT) < len(ZQ): ZT = ZT + ZQ[len(ZT):]   # round 103: a set one short near t = 1000 is completed by the quantile
assert len(ZT) == len(ZQ) == 649; HMAX, NQ = 6997.0, 3
for xv in map(float, sys.argv[5:]):
    E = 4*math.pi*xv; inb = [c1 <= g/E < c2 for g in ZT]
    Z = sorted(t if (b if mode == "keep" else not b) else q for t, q, b in zip(ZT, ZQ, inb))
    d = math.log(xv); K = max(40, int(Kf*xv) + 40); prec = int(96 + 2.1*4*math.pi*xv*1.4427)
    with ctx.workprec(prec):
        mp.mp.prec = prec
        # tail nodes: GL on panels of [HC, HMAX] in log t
        tq = []
        L0, L1 = math.log(HC), math.log(HMAX); P = 24
        for p in range(P):
            for u, w in GaussLegendre(mp.mp).get_nodes(mp.mpf(L0 + (L1 - L0)*p/P), mp.mpf(L0 + (L1 - L0)*(p + 1)/P), NQ, mp.mp.prec):
                t = mp.exp(u); tq.append((arb(str(t)), arb(str(w*t*mp.log(t/(2*mp.pi))/(2*mp.pi)/2))))
        a = arb(d)/2; pi = arb.pi(); om2 = [(arb(k)*pi/a)**2 for k in range(K)]
        R = len(Z) + len(tq); F = arb_mat(R, K)
        for i, g in enumerate(Z):
            t = arb(g); s = 2*t*(t*a).sin(); t2 = t*t
            for k in range(K): F[i, k] = (s if k % 2 == 0 else -s)/(t2 - om2[k])
        for j, (t, w) in enumerate(tq):
            s = 2*t*w.sqrt(); t2 = t*t; i = len(Z) + j
            for k in range(K): F[i, k] = (s if k % 2 == 0 else -s)/(t2 - om2[k])
        M = F.transpose()*F; e = arb_mat(K, 1); e[0, 0] = arb(1); y = M.solve(e)
        lnK = ((2*a)**2*y[0, 0]).log()
        print(json.dumps({"x": xv, "zfile": zf, "hcut": HC, "rows": R, "K": K, "prec": prec, "lnK00": lnK.mid().str(15, radius=False)}), flush=True)
