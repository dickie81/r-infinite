import numpy as np, json, pickle, sys
from xval import fit_eval, interleave
J = pickle.load(open(sys.argv[2], "rb")); a = J["a"]; K = 200; t, w = J["t"], J["w"]
fs = interleave(J["even"], J["odd"])[:24]
s = lambda m: (lambda t: (t/a)**(2*m)); ch = lambda m: (lambda t: np.cosh(2*m*t)); ts = lambda m: (lambda t: t*np.sinh(2*m*t))
one = lambda t: 0*t + 1
F = {
 "A: {1,s2,s4,ch2,ch4}": ([one, s(1), s(2), ch(1), ch(2)], [s(1), s(2), ch(1), ch(2)]),
 "B: A+{s6,ch6}": ([one, s(1), s(2), s(3), ch(1), ch(2), ch(3)], [s(1), s(2), s(3), ch(1), ch(2), ch(3)]),
 "C: {1,s2,ch2,ch4,tsh2,tsh4}": ([one, s(1), ch(1), ch(2), ts(1), ts(2)], [s(1), ch(1), ch(2), ts(1), ts(2)]),
 "D: C+{s4,ch6,tsh6}": ([one, s(1), s(2), ch(1), ch(2), ch(3), ts(1), ts(2), ts(3)], [s(1), s(2), ch(1), ch(2), ch(3), ts(1), ts(2), ts(3)]),
}
ntr = int(sys.argv[1]) if len(sys.argv) > 1 else 14
for name, (pb, qb) in F.items():
    rho, tr, te = fit_eval(fs[:ntr], fs[ntr:], t, w, a, K, pb, qb)
    print(json.dumps({"fam": name, "npar": len(pb)+len(qb), "ntrain": ntr, "train_rho": f"{rho:.2e}",
                      "train": [f"{x:.0e}" for x in tr], "test": [f"{x:.1e}" for x in te]}), flush=True)
