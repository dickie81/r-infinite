#!/usr/bin/env python3
"""Round 78: the pole overlap <c, psi2(Q0)> of the second eigenvector of the pole-free form Q0, at large
support, by block inverse iteration in arb (overlap_track.py uses mp.eigsy, too slow at K >~ 150).
Q0 has exactly one negative eigenvalue mu1 (~ -4.3; Q >= 0 and Q0 = Q - 2|c><c|), so psi2 is the eigenvector of
the smallest nonnegative eigenvalue mu2, i.e. the smallest in magnitude: inverse iteration finds it directly.
Sign convention psi2(0) > 0, as in overlap_track.py. Reports kappa = <c, psi2>/mu2 (round 51: ~ -0.35).
Usage: overlap_big.py <delta> <K> <prec> [iters]"""
import sys, os, json, time
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "..", "research"))
from weil_prime_gram import gram
from flint import arb, acb, arb_mat, ctx

def run(delta, K, prec, iters=12):
    t0 = time.time()
    G, N, pp = gram(delta, K, prec)
    with ctx.workprec(prec):
        a = arb(delta)/2; half = arb(1)/2
        P = [(2*(acb(half, arb(k)*arb.pi()/a)*a).sinh()/acb(half, arb(k)*arb.pi()/a)).real for k in range(K)]
        D = [1/N[i].sqrt() for i in range(K)]
        S = arb_mat(K, K)
        for i in range(K):
            for j in range(K):
                S[i, j] = ((G[i, j] - 2*P[i]*P[j])*D[i]*D[j]).mid()
        Sinv = S.inv(); Sinv = arb_mat([[Sinv[i, j].mid() for j in range(K)] for i in range(K)])
        # block inverse iteration on two vectors
        V = arb_mat([[arb(1)/(i + 1), arb((-1)**i)/(i + 2)] for i in range(K)])
        def orth(V):
            c0 = [V[i, 0] for i in range(K)]; n0 = sum(x*x for x in c0).sqrt(); c0 = [x/n0 for x in c0]
            c1 = [V[i, 1] for i in range(K)]; p = sum(c0[i]*c1[i] for i in range(K))
            c1 = [c1[i] - p*c0[i] for i in range(K)]; n1 = sum(x*x for x in c1).sqrt(); c1 = [x/n1 for x in c1]
            return arb_mat([[c0[i].mid(), c1[i].mid()] for i in range(K)])
        V = orth(V)
        for _ in range(iters):
            V = orth(Sinv*V)
        # Rayleigh-Ritz on span V
        H = V.transpose()*S*V
        h00, h01, h11 = H[0, 0], H[0, 1], H[1, 1]
        tr = h00 + h11; disc = ((h00 - h11)**2 + 4*h01*h01).sqrt()
        mu2, mu3 = (tr - disc)/2, (tr + disc)/2          # the two smallest-magnitude eigenvalues of S
        e = [h01, mu3 - h00]; ne = (e[0]**2 + e[1]**2).sqrt(); e = [e[0]/ne, e[1]/ne]
        psi3 = [V[i, 0]*e[0] + V[i, 1]*e[1] for i in range(K)]
        f = [-e[1], e[0]]
        psi2 = [V[i, 0]*f[0] + V[i, 1]*f[1] for i in range(K)]
        def overlap(v):
            x = [v[i]*D[i] for i in range(K)]          # cosine coefficients
            centre = sum(x)
            s = 1 if centre > 0 else -1
            return s*sum(P[i]*x[i] for i in range(K)), s*centre
        # residual check
        r2 = [sum(S[i, j]*psi2[j] for j in range(K)) - mu2*psi2[i] for i in range(K)]
        res = sum(x*x for x in r2).sqrt()
        ov2, c2 = overlap(psi2); ov3, c3 = overlap(psi3)
    f = lambda x: x.mid().str(8, radius=False)
    return {"delta": delta, "K": K, "prec": prec, "mu2": f(mu2), "mu3": f(mu3), "overlap_c_psi2": f(ov2),
            "kappa": f(ov2/mu2), "overlap_c_psi3": f(ov3), "psi2_centre": f(c2), "resid2": f(res),
            "t_s": round(time.time() - t0, 1)}

if __name__ == "__main__":
    d, K, p = float(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    it = int(sys.argv[4]) if len(sys.argv) > 4 else 12
    print(json.dumps(run(d, K, p, it)), flush=True)
