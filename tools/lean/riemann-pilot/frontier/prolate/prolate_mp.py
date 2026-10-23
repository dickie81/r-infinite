"""Exact 1 - lambda_n(c) for Slepian's time-band limiting operator on [-1,1], even n, via the Bouwkamp
Legendre expansion in mpmath: lambda_n = (c/2pi) mu_n^2, mu_n = int S_n / S_n(0) (S_n L2-normalised)."""
import mpmath as mp, sys, json
def deficits(c, ns, dps):
    mp.mp.dps = dps; c = mp.mpf(c)
    R = int(2*c + 80); rs = list(range(0, R, 2)); m = len(rs)
    M = mp.matrix(m, m)
    for i, r in enumerate(rs):
        M[i, i] = r*(r+1) + c*c*(2*r*(r+1) - 1)/mp.mpf((2*r+3)*(2*r-1))
        if i + 1 < m:
            M[i, i+1] = M[i+1, i] = c*c*(r+2)*(r+1)/((2*r+3)*mp.sqrt(mp.mpf((2*r+1)*(2*r+5))))
    E, V = mp.eigsy(M)
    order = sorted(range(m), key=lambda i: E[i])
    P0 = [mp.mpf(1)]
    for r in rs[1:]:
        P0.append(-P0[-1]*(r-1)/r)            # P_r(0) = (-1)^{r/2} (r-1)!!/r!!
    out = {}
    for n in ns:
        j = order[n//2]; d = [V[i, j] for i in range(m)]
        S0 = mp.fsum(d[i]*mp.sqrt(rs[i] + mp.mpf(1)/2)*P0[i] for i in range(m))
        mu = mp.sqrt(2)*d[0]/S0
        out[n] = -mp.log(1 - c/(2*mp.pi)*mu*mu)
    return out
for a in [float(v) for v in sys.argv[1].split(",")]:
    X = mp.pi*mp.e**(2*mp.mpf(a)); c = 2*X
    dps = int(2*float(c)/2.3) + 80
    D = deficits(c, [0, 2, 4, 6, 8], dps)
    print(json.dumps({"a": a, "X": mp.nstr(X, 6), "c": mp.nstr(c, 6),
                      "-ln(1-lam_n)": {n: mp.nstr(v, 7) for n, v in D.items()}}), flush=True)
