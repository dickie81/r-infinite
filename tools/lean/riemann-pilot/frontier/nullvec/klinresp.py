#!/usr/bin/env python3
"""Round 104: response of ln K_a(0,0) to zero displacements, about the smooth-quantile (pure-Gamma) chain.
First and second order in delta_k = gamma_k - quantile_k, from the base ground state y = M^-1 e0 (see PREREG_linresp.md).
Usage: klinresp.py Kfac x1 x2 ...  -> JSON lines: x, lnK_base, d1/d2 for 'true' and 'P7' displacements; profiles at chosen x."""
import sys, json, math
from flint import arb, arb_mat, ctx
import mpmath as mp
from mpmath.calculus.quadrature import GaussLegendre
Kf = float(sys.argv[1]); HC = 1000.0; HMAX, NQ = 6997.0, 3
ZQ = json.load(open("pzeros_0.json"))
DT = {"true": [g for g in json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json")) if g < HC], "P7": json.load(open("pzeros_7.json"))}
for k in DT: DT[k] = DT[k] + ZQ[len(DT[k]):]; assert len(DT[k]) == len(ZQ) == 649
for xv in map(float, sys.argv[2:]):
    d = math.log(xv); K = max(40, int(Kf*xv) + 40); prec = int(96 + 2.1*4*math.pi*xv*1.4427)
    with ctx.workprec(prec):
        mp.mp.prec = prec; tq = []; L0, L1 = math.log(HC), math.log(HMAX)
        for p in range(24):
            for u, w in GaussLegendre(mp.mp).get_nodes(mp.mpf(L0 + (L1 - L0)*p/24), mp.mpf(L0 + (L1 - L0)*(p + 1)/24), NQ, mp.mp.prec):
                t = mp.exp(u); tq.append((arb(str(t)), arb(str(w*t*mp.log(t/(2*mp.pi))/(2*mp.pi)/2))))
        a = arb(d)/2; pi = arb.pi(); om2 = [(arb(k)*pi/a)**2 for k in range(K)]; sg = [1 if k % 2 == 0 else -1 for k in range(K)]
        rows, d1r, d2r = [], [], []
        for g in ZQ:
            t = arb(g); S, C = (t*a).sin(), (t*a).cos(); A = 2*t*S; A1 = 2*S + 2*t*a*C; A2 = 4*a*C - 2*t*a*a*S
            r0, r1, r2 = [], [], []
            for k in range(K):
                B = 1/(t*t - om2[k]); B1 = -2*t*B*B; B2 = -2*B*B + 8*t*t*B*B*B
                r0.append(sg[k]*A*B); r1.append(sg[k]*(A1*B + A*B1)); r2.append(sg[k]*(A2*B + 2*A1*B1 + A*B2))
            rows.append(r0); d1r.append(r1); d2r.append(r2)
        R = len(rows) + len(tq); F = arb_mat(R, K)
        for i, r0 in enumerate(rows):
            for k in range(K): F[i, k] = r0[k]
        for j, (t, w) in enumerate(tq):
            s2 = 2*t*w.sqrt(); t2 = t*t
            for k in range(K): F[len(rows) + j, k] = sg[k]*s2/(t2 - om2[k])
        M = F.transpose()*F; e = arb_mat(K, 1); e[0, 0] = arb(1); y = M.solve(e); s = y[0, 0]
        dot = lambda r: sum((r[k]*y[k, 0] for k in range(K)), arb(0))
        Fk = [dot(r) for r in rows]; F1 = [dot(r) for r in d1r]; F2 = [dot(r) for r in d2r]
        out = {"x": xv, "K": K, "lnK_base": ((2*a)**2*s).log().mid().str(15, radius=False)}
        for name, Z in DT.items():
            dl = [arb(z) - arb(q) for z, q in zip(Z, ZQ)]
            a1 = sum((2*Fk[i]*F1[i]*dl[i] for i in range(649)), arb(0)); a2 = sum(((Fk[i]*F2[i] + F1[i]*F1[i])*dl[i]*dl[i] for i in range(649)), arb(0))
            v = arb_mat(K, 1)
            for i in range(649):
                if dl[i] != 0:
                    for k in range(K): v[k, 0] += dl[i]*(d1r[i][k]*Fk[i] + rows[i][k]*F1[i])
            q = (v.transpose()*M.solve(v))[0, 0]
            D1 = -a1/s; D2 = D1 - a2/s + q/s - a1*a1/(2*s*s)
            out[f"d1_{name}"] = float(D1.mid()); out[f"d2_{name}"] = float(D2.mid())
        if round(xv, 2) in (5.0, 8.0, 11.0):
            out["profile"] = [[g, float((2*Fk[i]*F1[i]/s).mid()), float((F1[i]*F1[i]/s).mid())] for i, g in enumerate(ZQ) if g < 6*4*math.pi*xv]
        print(json.dumps(out), flush=True)
