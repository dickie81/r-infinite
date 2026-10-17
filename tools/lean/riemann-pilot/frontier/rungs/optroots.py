import pickle, sys, mpmath as mp, json
S = pickle.load(open(sys.argv[1], "rb")); mp.mp.dps = S["dps"]
A = mp.matrix([[mp.mpf(x) for x in r] for r in S["A"]]); B = mp.matrix([[mp.mpf(x) for x in r] for r in S["B"]])
J = int(sys.argv[2]) if len(sys.argv) > 2 else A.rows
A = A[:J, :J]; B = B[:J, :J]
a = mp.mpf(S["delta"])/2; X = mp.pi*mp.e**(2*a)
L = mp.cholesky(B); Li = mp.inverse(L); C = Li*A*Li.T
E, V = mp.eigsy((C + C.T)/2)
i0 = min(range(J), key=lambda i: E[i]); y = V[:, i0]; p = Li.T*y   # coefficients of D^{2k}
coeffs = [p[k] for k in range(J)]
# roots of P(w) = sum p_k w^k
r = mp.polyroots(coeffs[::-1], maxsteps=400, extraprec=4*mp.mp.dps)
r = sorted(r, key=lambda z: mp.re(z))
print(json.dumps({"delta": S["delta"], "J": J, "X": mp.nstr(X, 5), "2X": mp.nstr(2*X, 5), "lam": mp.nstr(E[i0], 5),
  "roots w=D^2 (as z = sqrt(-w) for w<0)": [mp.nstr(z, 5) for z in r]}))
