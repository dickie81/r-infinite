"""Certify lambda_1^{DH}(delta) < 0: ball Rayleigh quotient of the computed minimiser (upper end < 0)."""
import sys, math, json
sys.path.insert(0, '.')
import mpmath as mp, dh_gram as D, dhlib as Lb
from flint import arb, arb_mat, ctx
K = int(sys.argv[1]); prec = int(sys.argv[2]); deltas = [float(x) for x in sys.argv[3:]]
dps = int(prec*0.29)
with ctx.workprec(prec + 40):
    _, z0, logq, pole = Lb.lf('dh', 10)
Nall = int(math.exp(max(deltas))) + 2
c = Lb.cvec_arb('dh', Nall, prec)
for delta in deltas:
    Nmax = int(math.exp(delta)) + 1
    w = [(n, c[n]) for n in range(2, Nmax + 1) if not (c[n] == 0)]
    G, Nn, pp = D.gram(delta, K, prec, dict(z0=z0, logq=logq, pole=pole, weights=w))
    lam, v = D.lowest_mp(G, Nn, dps, 1)[0]
    with ctx.workprec(prec):
        vec = arb_mat(K, 1)
        for i in range(K): vec[i, 0] = arb(mp.nstr(v[i], dps - 5))
        num = (vec.transpose()*G*vec)[0, 0]
        den = arb(0)
        for i in range(K): den += Nn[i]*vec[i, 0]*vec[i, 0]
        rq = num/den
        print(json.dumps({"delta": delta, "K": K, "eig": mp.nstr(lam, 6), "rq_upper": rq.upper().str(8, radius=False),
                          "rq_mid": rq.mid().str(8, radius=False), "certified_negative": bool(rq.upper() < 0)}), flush=True)
