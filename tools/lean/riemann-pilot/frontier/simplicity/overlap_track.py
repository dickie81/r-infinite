"""Track the pole overlap <c, psi2(Q0)> across supports with a fixed sign convention psi2(0) > 0."""
import sys, json
import os; sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "../../../../research"))
from weil_prime_gram import gram
from flint import arb, acb, ctx
import mpmath as mp
def run(d, K, p):
    G, N, pp = gram(d, K, p)
    with ctx.workprec(p):
        aa = arb(d) / 2; half = arb(1) / 2
        P = [(2 * (acb(half, arb(k) * arb.pi() / aa) * aa).sinh() / acb(half, arb(k) * arb.pi() / aa)).real for k in range(K)]
    mp.mp.dps = int(p * 0.28)
    cv = lambda x: mp.mpf((int(x.mid().man_exp()[0]), int(x.mid().man_exp()[1])))
    Nv = [cv(x) for x in N]; Pv = [cv(x) for x in P]
    S = mp.matrix(K, K)
    for i in range(K):
        for j in range(K): S[i, j] = (cv(G[i, j]) - 2 * Pv[i] * Pv[j]) / mp.sqrt(Nv[i] * Nv[j])
    E, R = mp.eigsy(S)
    idx = sorted(range(K), key=lambda i: E[i])
    out = {}
    for name, col in (("psi1", idx[0]), ("psi2", idx[1])):
        x = [R[r, col] / mp.sqrt(Nv[r]) for r in range(K)]       # cosine coefficients
        centre = sum(x)                                            # psi(0)
        s = 1 if centre > 0 else -1
        out[name] = (s * sum(Pv[r] * x[r] for r in range(K)), E[col], centre)
    return out
d0, d1, step, K, p = map(float, sys.argv[1:6])
d = d0
while d <= d1 + 1e-9:
    o = run(round(d, 4), int(K), int(p))
    print(json.dumps(dict(delta=round(d, 4), overlap_c_psi2=mp.nstr(o["psi2"][0], 5), mu2=mp.nstr(o["psi2"][1], 5),
                          psi2_centre=mp.nstr(o["psi2"][2], 4), overlap_c_phi0=mp.nstr(o["psi1"][0], 4))), flush=True)
    d += step
