#!/usr/bin/env python3
"""Round 91: the window chain from the zero side of the explicit formula. For even g on [-a, a],
Q(g) = sum over zeros rho = 1/2 + i gamma of |g^(gamma)|^2 (Weil; +-gamma counted by a factor 2, dropped as a constant).
K00 = sup g^(0)^2 / sum_gamma |g^(gamma)|^2 over the cosine basis, whose transforms are
g_k^(t) = (-1)^k sin(ta) 2t/(t^2 - (k pi/a)^2). ZSET: 'true' (first 6700 zeros), 'smooth' (theta(g) = (k - 3/2) pi,
the fluctuation-free quantiles of the Riemann-von Mangoldt count). Usage: kzeroside.py ZSET Kfac x1 x2 ..."""
import sys, json, math
from flint import arb, arb_mat, ctx
ZS, Kf = sys.argv[1], float(sys.argv[2])
Zt = json.load(open("../../../../research/checkpoints/zeta_zeros_6700.json"))
if ZS == "true": Z = Zt
else:
    import mpmath as mp
    mp.mp.dps = 30; Z = []
    for k in range(1, len(Zt) + 1):
        Z.append(float(mp.findroot(lambda t: mp.siegeltheta(t) - (k - 1.5)*mp.pi, Zt[k - 1])))
for xv in map(float, sys.argv[3:]):
    d = math.log(xv); K = max(40, int(Kf*xv) + 40); prec = int(200 + 2.2*4*math.pi*xv*1.4427)
    with ctx.workprec(prec):
        a = arb(d)/2; pi = arb.pi(); om2 = [(arb(k)*pi/a)**2 for k in range(K)]
        F = arb_mat(len(Z), K)
        for i, g in enumerate(Z):
            t = arb(g); s = 2*t*(t*a).sin(); t2 = t*t
            for k in range(K): F[i, k] = (s/(t2 - om2[k]) if k % 2 == 0 else -s/(t2 - om2[k]))
        M = F.transpose()*F
        e = arb_mat(K, 1); e[0, 0] = arb(1)
        y = M.solve(e)
        lnK = ((2*a)**2*y[0, 0]).log()
        print(json.dumps({"x": xv, "delta": round(d, 7), "K": K, "prec": prec, "zset": ZS, "lnK00": lnK.mid().str(15, radius=False),
                          "rad": float(lnK.rad())}), flush=True)
