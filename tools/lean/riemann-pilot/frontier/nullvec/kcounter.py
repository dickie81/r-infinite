#!/usr/bin/env python3
"""Round 119: the signature of a counterexample. Start from the certified prime-side form M(x) (all true zeros, unconditional).
Hypothesis H(n, delta): the consecutive zeros gamma_n, gamma_{n+1} collide at g0 = (gamma_n + gamma_{n+1})/2 and leave the line as
rho = 1/2 +- delta + i g0 (a legal quadruple: the zero count is preserved). In M = (1/2) sum_rho H(gamma_rho):
    Delta M = 2 Re[v v^T] - u_n u_n^T - u_{n+1} u_{n+1}^T,   v = ghat(g0 + i delta), u = ghat(gamma)   (ghat_k(t) = (-1)^k 2t sin(ta)/(t^2 - w_k^2)).
Exact: certified Cholesky of M + Delta M (positivity lost or not) and lnK' - lnK. First order (round 113 response_kernel):
    Delta_1 lnK = -y^T Delta M y / s = -[2 Re F(g0 + i delta)^2 - F(gamma_n)^2 - F(gamma_{n+1})^2]/s,  y = M^-1 e0, s = y0, F(t) = y . ghat(t).
The zeros are taken to 210 digits (zeros_hp.json): a double-precision gamma leaves a residual that swamps the form's tiny eigenvalues.
Usage: kcounter.py "n1,n2,..." "d1,d2,..." x1 x2 ...   (env CT_REMOVE_ONLY=1: sanity mode, Delta M = -u_n u_n^T - u_{n+1} u_{n+1}^T)"""
import sys, json, math, os
from flint import arb, acb, arb_mat, ctx
import kps_chol as C
ZH = json.load(open("zeros_hp.json"))
NS = [int(s) for s in sys.argv[1].split(",")]; DS = [s for s in sys.argv[2].split(",")]
RONLY = os.environ.get("CT_REMOVE_ONLY", "") == "1"
def ghat(k, t, a, w):    # t arb or acb
    s = 1 if k % 2 == 0 else -1
    return s*2*t*(t*a).sin()/(t*t - w[k]*w[k])
for xv in map(float, sys.argv[3:]):
    K = max(40, int(15*xv) + 40); prec0 = int(96 + 2.1*4*math.pi*xv*1.4427)
    for fac in (1.5, 2, 3):
        prec = int(prec0*fac); ok = True; rows = []
        with ctx.workprec(prec):
            a = arb(repr(xv)).log()/2; w = [arb(k)*arb.pi()/a for k in range(K)]
            A = C.build(xv, K); M = arb_mat(A); e = arb_mat(K, 1); e[0, 0] = arb(1); y = M.solve(e); s = y[0, 0]
            lnK = ((2*a)**2*s).log()
            for n in NS:
                g1, g2 = arb(ZH[str(n)]), arb(ZH[str(n + 1)]); g0 = (g1 + g2)/2
                u1 = [ghat(k, g1, a, w) for k in range(K)]; u2 = [ghat(k, g2, a, w) for k in range(K)]
                F1 = sum((y[k, 0]*u1[k] for k in range(K)), arb(0)); F2 = sum((y[k, 0]*u2[k] for k in range(K)), arb(0))
                for dstr in (["0"] if RONLY else DS):
                    dl = arb(dstr); v = [ghat(k, acb(g0, dl), a, w) for k in range(K)]
                    Fv = sum((y[k, 0]*v[k] for k in range(K)), acb(0))
                    d1 = -((0 if RONLY else 2*(Fv*Fv).real) - F1*F1 - F2*F2)/s
                    B = [[A[j][k] + (0 if RONLY else 2*(v[j]*v[k]).real) - u1[j]*u1[k] - u2[j]*u2[k] for k in range(K)] for j in range(K)]
                    bad, piv = C.chol_pivots(B)
                    if bad is None:
                        Mb = arb_mat(B); yb = Mb.solve(e); lk = ((2*a)**2*yb[0, 0]).log(); dx = lk - lnK
                        if not (dx.is_finite() and float(dx.rad()) < 1e-6): ok = False; break
                        st = "PD"; dex = float(dx.mid())
                    elif piv[bad].upper() < 0: st = "LOST"; dex = None
                    else: ok = False; break
                    rows.append({"x": xv, "n": n, "g0": float(g0.mid()), "delta": dstr, "status": st, "dlnK_exact": dex,
                                 "dlnK_first": float(d1.mid()) if d1.is_finite() else None, "prec": prec})
                if not ok: break
        if ok:
            for r in rows: print(json.dumps(r), flush=True)
            break
    else: print(json.dumps({"x": xv, "status": "UNDECIDED"}), flush=True)
