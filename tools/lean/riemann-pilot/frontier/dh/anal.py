"""Eigenvectors of the DH Weil form near the first failure: hat g at the off-line zeros."""
import sys, math, json
sys.path.insert(0, '.')
import mpmath as mp, dh_gram as D, dhlib as Lb
from flint import arb, ctx
K = int(sys.argv[1]); prec = int(sys.argv[2]); deltas = [float(x) for x in sys.argv[3:]]
dps = int(prec*0.29); mp.mp.dps = 30
kap = (mp.sqrt(10 - 2*mp.sqrt(5)) - 2)/(mp.sqrt(5) - 1)
chi = [0, 1, 1j, -1j, -1]; chib = [0, 1, -1j, 1j, -1]
f = lambda s: (1 - 1j*kap)/2*mp.dirichlet(s, chi) + (1 + 1j*kap)/2*mp.dirichlet(s, chib)
seeds = [(0.808517, 85.699348), (0.650830, 114.163343), (0.574356, 166.479306), (0.724258, 176.702461)]
off = []
for b, g in seeds:
    r = mp.findroot(f, mp.mpc(b, g))
    off.append(r)
print("off-line zeros", [mp.nstr(r, 12) for r in off], flush=True)
with ctx.workprec(prec + 40):
    _, z0, logq, pole = Lb.lf('dh', 10)
Nall = int(math.exp(max(deltas))) + 2
c = Lb.cvec_arb('dh', Nall, prec)
for delta in deltas:
    Nmax = int(math.exp(delta)) + 1
    w = [(n, c[n]) for n in range(2, Nmax + 1) if not (c[n] == 0)]
    G, Nn, pp = D.gram(delta, K, prec, dict(z0=z0, logq=logq, pole=pole, weights=w))
    lo = D.lowest_mp(G, Nn, dps, 3)
    a = mp.mpf(delta)/2
    out = {"delta": delta, "modes": []}
    for lam, v in lo:
        def gh(t):
            s = mp.mpc(0)
            for k, ck in enumerate(v):
                om = k*mp.pi/a
                s += ck*((mp.sin((t - om)*a)/(t - om) if t != om else a) + (mp.sin((t + om)*a)/(t + om) if t != -om else a))
            return s
        offc = []
        for r in off:
            tau = (r - mp.mpf(1)/2)/1j
            val = gh(tau)
            offc.append(mp.nstr(4*mp.re(val**2), 5))
        # where does |hat g| peak on the real line
        grid = [mp.mpf(x)/2 for x in range(0, 500)]
        vals = [abs(gh(t)) for t in grid]
        imax = max(range(len(vals)), key=lambda i: vals[i])
        out["modes"].append({"lam": mp.nstr(lam, 6), "offline_4Re_ghat2": offc,
                             "argmax_t": float(grid[imax]), "max": mp.nstr(vals[imax], 4)})
    print(json.dumps(out), flush=True)
