import pickle, sys, json, mpmath as mp
S = pickle.load(open(sys.argv[1], "rb")); mp.mp.dps = S["dps"]
A = mp.matrix([[mp.mpf(x) for x in r] for r in S["A"]]); B = mp.matrix([[mp.mpf(x) for x in r] for r in S["B"]])
J = A.rows; a = mp.mpf(S["delta"])/2; X = mp.pi*mp.e**(2*a)
def rq(p):
    v = mp.matrix(p + [0]*(J - len(p))); return (v.T*A*v)[0]/(v.T*B*v)[0]
for sgn in (+1, -1):
    for n in [int(x) for x in sys.argv[2].split(",")]:
        best = None
        for c in [mp.mpf(x)/X for x in sys.argv[3].split(",")]:   # c in units of 1/X
            p = [(sgn*c)**k/mp.factorial(k) for k in range(n + 1)]
            v = -mp.log(rq(p))
            if best is None or v > best[1]: best = (c*X, v)
        print(json.dumps({"delta": S["delta"], "sign": sgn, "n": n, "best c*X": mp.nstr(best[0], 4), "-ln RQ": mp.nstr(best[1], 6)}), flush=True)
