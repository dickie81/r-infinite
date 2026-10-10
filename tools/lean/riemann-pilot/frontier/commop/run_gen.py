import json, sys, numpy as np
from numpy.polynomial.legendre import leggauss
from numpy.polynomial import legendre as Lg
from slweak import sample
from slgen import gen_fit, families
def weil(path, m):
    J = json.load(open(path)); a = J["delta"]/2; K = J["K"]
    lev = [(float(e["lam"]), "even", e["c"]) for e in J["even"][:m]] + [(float(e["lam"]), "odd", e["c"]) for e in J["odd"][:m]]
    lev.sort(key=lambda z: z[0]); x, _ = leggauss(4000); t = a*x
    return a, K, [(k,) + sample(c, k, a, t) for _, k, c in lev]
def gauss(sig, a=0.8, M=50):
    xs, ws = leggauss(300)
    P = np.array([Lg.legval(xs, np.eye(M)[n])*np.sqrt((2*n+1)/2) for n in range(M)])
    H = (P*ws) @ (np.exp(-(a*(xs[:, None]-xs[None, :]))**2/(2*sig**2))*a) @ (P*ws).T
    E, V = np.linalg.eigh(H); x, _ = leggauss(4000); fs = []
    for i, j in enumerate(np.argsort(-E)[:6]):
        d = V[:, j]*np.array([np.sqrt((2*n+1)/2) for n in range(M)])
        fs.append(("even" if i % 2 == 0 else "odd", Lg.legval(x, d)/np.sqrt(a), Lg.legval(x, Lg.legder(d))/np.sqrt(a)/a))
    return a, 60, fs
cases = [("gauss s=0.3",) + gauss(0.3)] + [(f"weil d={d}",) + weil(f"eigs_{d}_80.json", 3) for d in ("1.6", "2.2", "2.6")]
for tag, a, K, fs in cases:
    for D in (1, 2, 4, 6):
        for name, (pb, qb) in families(a, D).items():
            rho, per, edge = gen_fit(fs, a, K, pb, qb)
            print(json.dumps({"case": tag, "family": name, "D": D, "rho": round(rho, 5),
                              "worst_level": round(max(per), 4), "edge_dv_rel": f"{edge:.1e}"}), flush=True)
