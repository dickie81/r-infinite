import json, sys, numpy as np
from numpy.polynomial.legendre import leggauss
from slweak import sample, report
path, m, Dmax = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
J = json.load(open(path)); a = J["delta"]/2; K = J["K"]
lev = [(float(e["lam"]), "even", e["c"]) for e in J["even"][:m]] + [(float(e["lam"]), "odd", e["c"]) for e in J["odd"][:m]]
lev.sort(key=lambda z: z[0])
x, _ = leggauss(4000); t = a*x
funcs = [(k,) + sample(c, k, a, t) for _, k, c in lev]
report(f"weil delta={J['delta']} levels={[k for _,k,_ in lev]}", funcs, a, K, Dmax)
